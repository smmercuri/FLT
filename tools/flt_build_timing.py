#!/usr/bin/env python3
"""
Zero-dependency stdio MCP server that times the *build* of every FLT module in
the import closure and writes the raw timing data to a new file.

Speaks JSON-RPC 2.0 over newline-delimited stdio (MCP stdio transport), so it
needs no third-party packages -- only the Python standard library.

How this differs from `flt_profile_ranking`:
    `flt_profile_ranking` runs `lean --profile` and derives a per-declaration
    OWN time (total minus import time, divided by #decls). This tool is simpler
    and coarser: it times the full wall-clock cost of compiling each file --
    imports included -- as a stand-in for "how long does this file take to
    build". No profiling, no per-decl accounting.

Exposed tool:
    flt_build_timing(closure_json?, modules?, timeout?, runs?, limit?, write_output?)
        For every FLT module listed in .cache/flt_import_closure_output.json
        (the output of the `flt_import_closure` tool), run

            lake env lean <leanOptions> <file>

        and measure the wall-clock time Lean takes to compile that single file
        (its imports must already be built, e.g. via `lake exe cache get`). The
        file is compiled `runs` times (default 3) and the wall times are averaged
        to reduce noise; per-run figures are retained. Modules are ranked slowest
        build first, and the full result is written to .cache/flt_build_times.json.

        `lake env lean <file>` recompiles the file's own content on every
        invocation (it does not consult lake's up-to-date olean cache), so the
        measurement is repeatable and does not require invalidating the build
        tree between runs.

Run standalone for a quick protocol smoke test:
    echo '{"jsonrpc":"2.0","id":1,"method":"tools/list"}' | tools/flt_build_timing.py

Or run the timing directly (bypassing MCP), e.g. on the first 3 modules:
    tools/flt_build_timing.py --run --limit 3
"""

import json
import subprocess
import sys
import time
import tomllib
from pathlib import Path

# Resolve paths regardless of the current working directory.
_HERE = Path(__file__).resolve().parent
_PROJECT_ROOT = _HERE.parent
_LAKEFILE = _PROJECT_ROOT / "lakefile.toml"
_CACHE_DIR = _PROJECT_ROOT / ".cache"
DEFAULT_CLOSURE_JSON = _CACHE_DIR / "flt_import_closure_output.json"
DEFAULT_OUTPUT = _CACHE_DIR / "flt_build_times.json"
DEFAULT_TIMEOUT = 900  # seconds per file
DEFAULT_RUNS = 3  # build each file this many times and average the wall times

PROTOCOL_VERSION = "2024-11-05"
SERVER_INFO = {"name": "flt-build-timing", "version": "1.0.0"}

TOOLS = [
    {
        "name": "flt_build_timing",
        "description": (
            "Time the full build of every FLT module in "
            ".cache/flt_import_closure_output.json by running "
            "`lake env lean <file>` and measuring its wall-clock compile time "
            "(imports included). Ranks modules slowest build first and writes "
            "the raw timing data to .cache/flt_build_times.json. Each file is "
            "built `runs` times (default 3) and the wall times averaged to reduce "
            "noise. Coarser than `flt_profile_ranking` (which derives a per-decl "
            "own time); use this for whole-file build cost. NOTE: requires the "
            "Mathlib/FLT oleans to be built (e.g. `lake exe cache get`), else "
            "every file errors at the import stage."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "closure_json": {
                    "type": "string",
                    "description": (
                        "Path to the import-closure JSON to read the module list "
                        f"from (default: {DEFAULT_CLOSURE_JSON.name} in .cache). "
                        "Reads the top-level `modules` array."
                    ),
                },
                "modules": {
                    "type": "array",
                    "items": {"type": "string"},
                    "description": (
                        "Explicit list of FLT modules to time, overriding "
                        "closure_json (e.g. [\"FLT.NumberField.AdeleRing\"])."
                    ),
                },
                "timeout": {
                    "type": "number",
                    "description": (
                        f"Per-file timeout in seconds (default: {DEFAULT_TIMEOUT}). "
                        "A file that times out is recorded with its error flagged."
                    ),
                },
                "runs": {
                    "type": "integer",
                    "description": (
                        f"How many times to build each file, averaging the wall "
                        f"times to reduce noise (default: {DEFAULT_RUNS}, minimum 1)."
                    ),
                },
                "limit": {
                    "type": "integer",
                    "description": "Only time the first N modules (useful for a smoke test).",
                },
                "write_output": {
                    "type": "boolean",
                    "description": (
                        "Also write the ranked result to "
                        ".cache/flt_build_times.json (default true)."
                    ),
                },
            },
        },
    }
]


def _module_to_path(module: str) -> Path:
    """`FLT.NumberField.AdeleRing` -> <root>/FLT/NumberField/AdeleRing.lean."""
    return _PROJECT_ROOT / (module.replace(".", "/") + ".lean")


def _fmt_option_value(value) -> str:
    """Format a lakefile option value the way the Lean `-D` flag expects."""
    if isinstance(value, bool):  # must precede int: bool is a subclass of int
        return "true" if value else "false"
    return str(value)


_lean_option_args_cache: list[str] | None = None


def _lean_option_args() -> list[str]:
    """Return the package's `[leanOptions]` from lakefile.toml as `-D<key>=<val>`
    flags.

    `lake env lean` sets up the environment (LEAN_PATH etc.) but, unlike
    `lake build`, does NOT apply the package's Lean options -- so a file that
    builds cleanly can otherwise diverge (different typeclass search, autoImplicit
    behaviour, heartbeat outcomes) when compiled directly. Passing them here makes
    the timing match the real build. Keys are kept verbatim, including any `weak.`
    prefix, which Lean treats as "ignore if unknown"."""
    global _lean_option_args_cache
    if _lean_option_args_cache is not None:
        return _lean_option_args_cache
    args: list[str] = []
    try:
        with _LAKEFILE.open("rb") as f:
            data = tomllib.load(f)
        # TOML dotted keys (`pp.unicode.fun = true`) parse into nested tables, so
        # flatten them back to the dotted option name Lean's `-D` expects.
        for key, value in _flatten_options(data.get("leanOptions") or {}):
            args.append(f"-D{key}={_fmt_option_value(value)}")
    except (OSError, tomllib.TOMLDecodeError):
        args = []  # no lakefile / unparseable -> fall back to bare `lean`
    _lean_option_args_cache = args
    return args


def _flatten_options(options: dict, prefix: str = ""):
    """Yield (dotted_key, scalar_value) pairs, flattening nested TOML tables."""
    for key, value in options.items():
        dotted = f"{prefix}{key}"
        if isinstance(value, dict):
            yield from _flatten_options(value, prefix=f"{dotted}.")
        else:
            yield dotted, value


def _measure_once(cmd: list[str], timeout: float) -> dict:
    """Run one `lake env lean <file>` build; return {total_s, error}. `total_s`
    is the wall time; `error` is the first error line / timeout message, else
    None."""
    start = time.monotonic()
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(_PROJECT_ROOT),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            # Lean emits UTF-8; decode as such (with replacement) so we don't
            # crash on non-cp1252 bytes under Windows' default locale encoding.
            encoding="utf-8",
            errors="replace",
            text=True,
            timeout=timeout,
        )
        elapsed = time.monotonic() - start
        output = proc.stdout or ""
        error = None
        if proc.returncode != 0:
            error = next(
                (ln for ln in output.splitlines() if ": error:" in ln),
                f"lean exited with code {proc.returncode}",
            ).strip()
        return {"total_s": round(elapsed, 3), "error": error}
    except subprocess.TimeoutExpired:
        return {
            "total_s": round(time.monotonic() - start, 3),
            "error": f"timed out after {timeout}s",
        }
    except Exception as e:  # noqa: BLE001 - surface any failure into the record
        return {"total_s": None, "error": f"{type(e).__name__}: {e}"}


def _time_one(module: str, timeout: float, runs: int = DEFAULT_RUNS) -> dict:
    """Build one module `runs` times and average the wall times; return a
    timing record."""
    runs = max(1, runs)
    path = _module_to_path(module)
    record = {
        "module": module,
        "file": str(path.relative_to(_PROJECT_ROOT)).replace("\\", "/")
        if path.is_file()
        else module.replace(".", "/") + ".lean",
        "total_s": None,
        "runs": runs,
        "runs_completed": 0,
        "total_s_runs": [],
        "error": None,
    }
    if not path.is_file():
        record["error"] = "file not found"
        return record

    cmd = ["lake", "env", "lean", *_lean_option_args(), str(path)]
    totals: list[float] = []
    for _ in range(runs):
        m = _measure_once(cmd, timeout)
        if m["total_s"] is not None:
            record["total_s_runs"].append(m["total_s"])
        if m["error"]:
            # A file that errors will almost certainly error on every run, so
            # stop early and surface the first failure.
            record["error"] = m["error"]
            if m["total_s"] is not None and record["total_s"] is None:
                record["total_s"] = m["total_s"]
            break
        totals.append(m["total_s"])

    record["runs_completed"] = len(totals)
    if totals:
        record["total_s"] = round(sum(totals) / len(totals), 3)
    return record


def _load_modules(closure_json: Path) -> list[str]:
    data = json.loads(closure_json.read_text())
    modules = data.get("modules")
    if not isinstance(modules, list) or not modules:
        raise ValueError(f"No `modules` array found in {closure_json}")
    return list(modules)


def _rank_key(r: dict):
    """Sort key: slowest total build time first, missing values last."""
    return (r["total_s"] is None, -(r["total_s"] or 0.0))


def _render(records: list[dict], runs: int) -> str:
    """Render the ranked records as a plain-text table (slowest build first)."""
    ranked = sorted(records, key=_rank_key)
    errored = sum(1 for r in records if r["error"])
    lines = [
        "Ranked by whole-file build wall time (`lake env lean <file>`), slowest first.",
        f"Each file built {runs} time(s); total_s is the average over runs_completed.",
        "",
        f"{'rank':>4}  {'total_s':>8}  {'runs':>4}  module",
        f"{'':->4}  {'':->8}  {'':->4}  {'':->40}",
    ]
    for i, r in enumerate(ranked, 1):
        total = f"{r['total_s']:.3f}" if r["total_s"] is not None else "-"
        flag = f"  [ERROR: {r['error']}]" if r["error"] else ""
        lines.append(
            f"{i:>4}  {total:>8}  {r['runs_completed']:>4}  {r['module']}{flag}"
        )
    if errored:
        lines.append("")
        lines.append(f"Note: {errored} file(s) errored during build (see flags above).")
    return "\n".join(lines)


def _run_timing(
    closure_json: Path | None,
    modules: list[str] | None,
    timeout: float,
    limit: int | None,
    write_output: bool,
    runs: int = DEFAULT_RUNS,
) -> str:
    runs = max(1, runs)
    if modules is None:
        cj = closure_json or DEFAULT_CLOSURE_JSON
        if not Path(cj).is_file():
            raise FileNotFoundError(f"Closure JSON not found: {cj}")
        modules = _load_modules(Path(cj))
    if limit is not None:
        modules = modules[:limit]

    records = [_time_one(m, timeout, runs) for m in modules]
    ranked = sorted(records, key=_rank_key)
    text = _render(records, runs)

    if write_output:
        _CACHE_DIR.mkdir(parents=True, exist_ok=True)
        DEFAULT_OUTPUT.write_text(
            json.dumps(
                {
                    "command": "lake env lean <file>",
                    "metric": "total_s = whole-file build wall time (imports included)",
                    "runs": runs,
                    "note": (
                        f"Each file built {runs} time(s); total_s is the average "
                        "over runs_completed (per-run wall times in total_s_runs)."
                    ),
                    "count": len(records),
                    "ranking": ranked,
                },
                indent=2,
            )
            + "\n"
        )
        rel = DEFAULT_OUTPUT.relative_to(_PROJECT_ROOT)
        text += f"\n\n(written to {str(rel).replace(chr(92), '/')})"
    return text


def _handle(msg: dict) -> dict | None:
    """Return a JSON-RPC response dict, or None for notifications."""
    method = msg.get("method")
    msg_id = msg.get("id")

    if msg_id is None and method != "initialize":
        return None

    if method == "initialize":
        return _ok(msg_id, {
            "protocolVersion": PROTOCOL_VERSION,
            "capabilities": {"tools": {}},
            "serverInfo": SERVER_INFO,
        })

    if method == "tools/list":
        return _ok(msg_id, {"tools": TOOLS})

    if method == "tools/call":
        params = msg.get("params") or {}
        name = params.get("name")
        args = params.get("arguments") or {}
        if name != "flt_build_timing":
            return _err(msg_id, -32602, f"Unknown tool: {name}")
        try:
            cj = args.get("closure_json")
            text = _run_timing(
                closure_json=Path(cj) if cj else None,
                modules=args.get("modules") or None,
                timeout=float(args.get("timeout", DEFAULT_TIMEOUT)),
                limit=args.get("limit"),
                write_output=bool(args.get("write_output", True)),
                runs=int(args.get("runs", DEFAULT_RUNS)),
            )
            return _ok(msg_id, {"content": [{"type": "text", "text": text}]})
        except Exception as e:  # noqa: BLE001 - surface any failure to the client
            return _ok(msg_id, {
                "content": [{"type": "text", "text": f"error: {e}"}],
                "isError": True,
            })

    return _err(msg_id, -32601, f"Method not found: {method}")


def _ok(msg_id, result):
    return {"jsonrpc": "2.0", "id": msg_id, "result": result}


def _err(msg_id, code, message):
    return {"jsonrpc": "2.0", "id": msg_id, "error": {"code": code, "message": message}}


def _cli() -> int:
    """Direct (non-MCP) run:
    `flt_build_timing.py --run [--limit N] [--timeout S] [--runs N]`."""
    argv = sys.argv[1:]
    limit = None
    timeout = DEFAULT_TIMEOUT
    runs = DEFAULT_RUNS
    if "--limit" in argv:
        limit = int(argv[argv.index("--limit") + 1])
    if "--timeout" in argv:
        timeout = float(argv[argv.index("--timeout") + 1])
    if "--runs" in argv:
        runs = int(argv[argv.index("--runs") + 1])
    print(_run_timing(None, None, timeout, limit, write_output=True, runs=runs))
    return 0


def main() -> int:
    if "--run" in sys.argv:
        return _cli()
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        response = _handle(msg)
        if response is not None:
            sys.stdout.write(json.dumps(response) + "\n")
            sys.stdout.flush()
    return 0


if __name__ == "__main__":
    sys.exit(main())
