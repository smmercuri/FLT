#!/usr/bin/env python3
"""
Zero-dependency stdio MCP server exposing the FLT per-file profile ranker.

Speaks JSON-RPC 2.0 over newline-delimited stdio (MCP stdio transport), so it
needs no third-party packages -- only the Python standard library.

Exposed tool:
    flt_profile_ranking(closure_json?, modules?, timeout?, limit?, write_output?)
        For every FLT module listed in .cache/flt_import_closure_output.json
        (the output of the `flt_import_closure` tool), run

            time lake env lean --profile <file>

        capture its `--profile` output, compute
        (total wall time) - (import time), i.e. the time Lean spent on the
        file's OWN content after its imports finished loading, then divide that
        by the number of top-level declarations in the file and rank the modules
        by this per-declaration own time. The wall time is the `real` figure
        `time` would report; it is measured in-process for portability (Windows
        has no `time` builtin), which is exactly equivalent. Declarations are
        counted by scanning the `.lean` source for declaration keywords.

Run standalone for a quick protocol smoke test:
    echo '{"jsonrpc":"2.0","id":1,"method":"tools/list"}' | tools/flt_profile_ranking.py

Or run the ranking directly (bypassing MCP), e.g. on the first 3 modules:
    tools/flt_profile_ranking.py --run --limit 3
"""

import json
import re
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
DEFAULT_OUTPUT = _CACHE_DIR / "flt_profile_ranking.json"
DEFAULT_TIMEOUT = 900  # seconds per file

PROTOCOL_VERSION = "2024-11-05"
SERVER_INFO = {"name": "flt-profile-ranking", "version": "1.0.0"}

TOOLS = [
    {
        "name": "flt_profile_ranking",
        "description": (
            "Run `time lake env lean --profile <file>` on every FLT module in "
            ".cache/flt_import_closure_output.json and return a ranked list of "
            "(total wall time - import time) / (number of declarations) per file "
            "-- i.e. the time Lean spent elaborating the file's OWN content (with "
            "the cost of loading its imports subtracted out), divided by the "
            "number of top-level declarations in the file. Slowest per-declaration "
            "own-time first. Results are "
            "also written to .cache/flt_profile_ranking.json. NOTE: requires the "
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
                        "Explicit list of FLT modules to profile, overriding "
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
                "limit": {
                    "type": "integer",
                    "description": "Only profile the first N modules (useful for a smoke test).",
                },
                "write_output": {
                    "type": "boolean",
                    "description": (
                        "Also write the ranked result to "
                        ".cache/flt_profile_ranking.json (default true)."
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
    behaviour, heartbeat outcomes) when profiled. Passing them here makes the
    profiler elaborate each file exactly as the build does. Keys are kept verbatim,
    including any `weak.` prefix, which Lean treats as "ignore if unknown"."""
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


# Leading declaration keywords, optionally preceded by attributes/modifiers.
_DECL_KEYWORDS = (
    "theorem", "lemma", "def", "abbrev", "instance", "structure",
    "inductive", "class", "axiom", "opaque", "example",
)
_DECL_MODIFIERS = (
    "private", "protected", "noncomputable", "partial", "unsafe",
    "scoped", "local", "mutual",
)
_DECL_RE = re.compile(
    r"^[ \t]*"                                      # leading indentation
    r"(?:@\[[^\]]*\][ \t]*)*"                        # optional @[...] attributes
    r"(?:(?:" + "|".join(_DECL_MODIFIERS) + r")[ \t]+)*"  # optional modifiers
    r"(?:" + "|".join(_DECL_KEYWORDS) + r")\b",      # the declaration keyword
    re.MULTILINE,
)


def _strip_comments(src: str) -> str:
    """Remove Lean line (`--`) and block (`/- -/`) comments so keywords inside
    comments/docstrings aren't miscounted. A best-effort heuristic (nested block
    comments and `--` inside string literals are not handled precisely)."""
    src = re.sub(r"/-.*?-/", " ", src, flags=re.DOTALL)  # block comments & docstrings
    src = re.sub(r"--[^\n]*", " ", src)                    # line comments
    return src


def _count_declarations(path: Path) -> int | None:
    """Count top-level declarations in a `.lean` source file by scanning for
    declaration keywords at the start of a line (after attributes/modifiers)."""
    try:
        src = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return None
    return len(_DECL_RE.findall(_strip_comments(src)))


def _parse_duration(text: str) -> float | None:
    """Parse a Lean profiler duration like '1.83s', '218ms', '1m2.3s' to seconds."""
    text = text.strip()
    total = 0.0
    matched = False
    # Minutes component, e.g. the '1m' in '1m2.3s'.
    m = re.search(r"([\d.]+)\s*m(?![s])", text)
    if m:
        total += float(m.group(1)) * 60.0
        matched = True
    # Milliseconds.
    m = re.search(r"([\d.]+)\s*ms", text)
    if m:
        total += float(m.group(1)) / 1000.0
        matched = True
    # Seconds. A '...ms' token can't match here (its digits are followed by 'm',
    # not 's'), so milliseconds are never double-counted.
    for sm in re.finditer(r"([\d.]+)\s*s\b", text):
        total += float(sm.group(1))
        matched = True
    return total if matched else None


def _parse_import_seconds(output: str) -> float | None:
    """Extract the import time (seconds) from `lean --profile` output.

    Prefers the `import` entry inside the `cumulative profiling times:` block;
    falls back to a top-level `import took <dur>` line.
    """
    lines = output.splitlines()
    in_block = False
    for line in lines:
        if "cumulative profiling times:" in line:
            in_block = True
            continue
        if in_block:
            stripped = line.strip()
            if stripped.startswith("import"):
                return _parse_duration(stripped[len("import"):])
            # Block entries are indented; a non-indented line ends the block.
            if stripped and not line[:1].isspace():
                in_block = False
    # Fallback: the top-of-output "import took 1.83s" line.
    m = re.search(r"import took\s+(.+)", output)
    if m:
        return _parse_duration(m.group(1))
    return None


def _profile_one(module: str, timeout: float) -> dict:
    """Run `lake env lean --profile` on one module; return a timing record."""
    path = _module_to_path(module)
    record = {
        "module": module,
        "file": str(path.relative_to(_PROJECT_ROOT)).replace("\\", "/"),
        "total_s": None,
        "import_s": None,
        "own_s": None,
        "decl_count": None,
        "own_s_per_decl": None,
        "error": None,
    }
    if not path.is_file():
        record["error"] = "file not found"
        return record
    record["decl_count"] = _count_declarations(path)

    cmd = ["lake", "env", "lean", *_lean_option_args(), "--profile", str(path)]
    start = time.monotonic()
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(_PROJECT_ROOT),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            # Lean emits UTF-8; decode as such (with replacement) so the reader
            # thread doesn't crash on non-cp1252 bytes under Windows' default
            # locale encoding.
            encoding="utf-8",
            errors="replace",
            text=True,
            timeout=timeout,
        )
        elapsed = time.monotonic() - start
        output = proc.stdout or ""
        record["total_s"] = round(elapsed, 3)
        import_s = _parse_import_seconds(output)
        record["import_s"] = round(import_s, 3) if import_s is not None else None
        if import_s is not None:
            own_s = round(max(elapsed - import_s, 0.0), 3)
            record["own_s"] = own_s
            if record["decl_count"]:  # non-None and > 0
                record["own_s_per_decl"] = round(own_s / record["decl_count"], 6)
        if proc.returncode != 0:
            # Surface the first error line for context (imports still get timed).
            err_line = next(
                (ln for ln in output.splitlines() if ": error:" in ln),
                f"lean exited with code {proc.returncode}",
            )
            record["error"] = err_line.strip()
    except subprocess.TimeoutExpired:
        record["total_s"] = round(time.monotonic() - start, 3)
        record["error"] = f"timed out after {timeout}s"
    except Exception as e:  # noqa: BLE001 - surface any failure into the record
        record["error"] = f"{type(e).__name__}: {e}"
    return record


def _load_modules(closure_json: Path) -> list[str]:
    data = json.loads(closure_json.read_text())
    modules = data.get("modules")
    if not isinstance(modules, list) or not modules:
        raise ValueError(f"No `modules` array found in {closure_json}")
    return list(modules)


def _rank_key(r: dict):
    """Sort key: slowest own-time-per-declaration first, missing values last."""
    return (r["own_s_per_decl"] is None, -(r["own_s_per_decl"] or 0.0))


def _render(records: list[dict], skipped_no_import: int) -> str:
    """Render the ranked records as a plain-text table (slowest per-decl first)."""
    ranked = sorted(records, key=_rank_key)
    lines = [
        "Ranked by own elaboration time per declaration "
        "((total wall time - import time) / #declarations), slowest first.",
        "",
        f"{'rank':>4}  {'s/decl':>10}  {'own_s':>8}  {'decls':>6}  "
        f"{'total_s':>8}  {'import_s':>8}  module",
        f"{'':->4}  {'':->10}  {'':->8}  {'':->6}  {'':->8}  {'':->8}  {'':->40}",
    ]
    for i, r in enumerate(ranked, 1):
        per = f"{r['own_s_per_decl']:.6f}" if r["own_s_per_decl"] is not None else "-"
        own = f"{r['own_s']:.3f}" if r["own_s"] is not None else "-"
        decls = f"{r['decl_count']}" if r["decl_count"] is not None else "-"
        total = f"{r['total_s']:.3f}" if r["total_s"] is not None else "-"
        imp = f"{r['import_s']:.3f}" if r["import_s"] is not None else "-"
        flag = f"  [ERROR: {r['error']}]" if r["error"] else ""
        lines.append(
            f"{i:>4}  {per:>10}  {own:>8}  {decls:>6}  "
            f"{total:>8}  {imp:>8}  {r['module']}{flag}"
        )
    if skipped_no_import:
        lines.append("")
        lines.append(
            f"Note: {skipped_no_import} file(s) had no per-declaration own time "
            "(sorted last); missing import time or zero declarations."
        )
    return "\n".join(lines)


def _run_ranking(
    closure_json: Path | None,
    modules: list[str] | None,
    timeout: float,
    limit: int | None,
    write_output: bool,
) -> str:
    if modules is None:
        cj = closure_json or DEFAULT_CLOSURE_JSON
        if not Path(cj).is_file():
            raise FileNotFoundError(f"Closure JSON not found: {cj}")
        modules = _load_modules(Path(cj))
    if limit is not None:
        modules = modules[:limit]

    records = [_profile_one(m, timeout) for m in modules]
    ranked = sorted(records, key=_rank_key)
    skipped_no_import = sum(1 for r in records if r["own_s_per_decl"] is None)
    text = _render(records, skipped_no_import)

    if write_output:
        _CACHE_DIR.mkdir(parents=True, exist_ok=True)
        DEFAULT_OUTPUT.write_text(
            json.dumps(
                {
                    "command": "time lake env lean --profile <file>",
                    "metric": (
                        "own_s_per_decl = (total_s - import_s) / decl_count "
                        "(own elaboration wall time per top-level declaration)"
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
        if name != "flt_profile_ranking":
            return _err(msg_id, -32602, f"Unknown tool: {name}")
        try:
            cj = args.get("closure_json")
            text = _run_ranking(
                closure_json=Path(cj) if cj else None,
                modules=args.get("modules") or None,
                timeout=float(args.get("timeout", DEFAULT_TIMEOUT)),
                limit=args.get("limit"),
                write_output=bool(args.get("write_output", True)),
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
    """Direct (non-MCP) run: `flt_profile_ranking.py --run [--limit N] [--timeout S]`."""
    argv = sys.argv[1:]
    limit = None
    timeout = DEFAULT_TIMEOUT
    if "--limit" in argv:
        limit = int(argv[argv.index("--limit") + 1])
    if "--timeout" in argv:
        timeout = float(argv[argv.index("--timeout") + 1])
    print(_run_ranking(None, None, timeout, limit, write_output=True))
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
