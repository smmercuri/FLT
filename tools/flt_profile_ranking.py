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
        own_s = (total wall time) - (import time), i.e. the total time Lean
        spent on the file's OWN content after its imports finished loading, and
        rank the modules by this total own time (slowest first). The
        per-declaration figure own_s / #declarations is also reported as a
        secondary column. The wall time is the `real` figure
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

import cache_paths

# Resolve paths regardless of the current working directory.
_HERE = Path(__file__).resolve().parent
_PROJECT_ROOT = _HERE.parent
_LAKEFILE = _PROJECT_ROOT / "lakefile.toml"
_CACHE_DIR = _PROJECT_ROOT / ".cache"
DEFAULT_CLOSURE_JSON = _CACHE_DIR / "flt_import_closure_output.json"
OUTPUT_NAME = "flt_profile_ranking.json"  # written under .cache/Pass_<n>/
DEFAULT_TIMEOUT = 900  # seconds per file

PROTOCOL_VERSION = "2024-11-05"
SERVER_INFO = {"name": "flt-profile-ranking", "version": "1.0.0"}

TOOLS = [
    {
        "name": "flt_profile_ranking",
        "description": (
            "Run `time lake env lean --profile <file>` on every FLT module in "
            ".cache/flt_import_closure_output.json, measuring own_s = (total wall "
            "time - import time) per file -- the total time Lean spent elaborating "
            "the file's OWN content, with imports subtracted out -- and the "
            "per-declaration figure own_s_per_decl = own_s / #declarations. Both "
            "are reported for every module. The `rank_by` argument chooses the sort "
            "key: `own_s` (default) surfaces the most expensive files overall "
            "(typically nearer the root of the import graph); `s/decl` surfaces "
            "files with a pathologically slow individual declaration (typically "
            "leaf nodes, where a fix propagates upward). Results are also written "
            "to .cache/Pass_<n>/flt_profile_ranking.json (see the `pass` argument). "
            "NOTE: requires the Mathlib/FLT oleans to be built (e.g. `lake exe "
            "cache get`), else every file errors at the import stage."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "pass": {
                    "type": "integer",
                    "description": (
                        "Pass number: results are written under .cache/Pass_<n>/. "
                        "Passing it also updates .cache/current_pass so the other "
                        "tools in this pass write to the same place. Defaults to the "
                        "current pass pointer (or 1 if unset)."
                    ),
                },
                "rank_by": {
                    "type": "string",
                    "enum": ["own_s", "s/decl"],
                    "description": (
                        "Which metric to sort the ranking by. `own_s` (default) = "
                        "total own elaboration time per file (biggest total cost "
                        "first). `s/decl` = own time per top-level declaration "
                        "(worst individual declaration first). Both figures are "
                        "always shown regardless of this choice."
                    ),
                },
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


# Which record field each user-facing `rank_by` value sorts on. Aliases let a
# caller say "own_s"/"total" or "s/decl"/"avg" interchangeably.
DEFAULT_RANK_BY = "own_s"
_RANK_BY_FIELD = {
    "own_s": "own_s",
    "total": "own_s",
    "own": "own_s",
    "s/decl": "own_s_per_decl",
    "own_s_per_decl": "own_s_per_decl",
    "per_decl": "own_s_per_decl",
    "avg": "own_s_per_decl",
}
# Human-readable description of each ranking field, for headers / metadata.
_RANK_FIELD_TITLE = {
    "own_s": "total own elaboration time (total wall time - import time)",
    "own_s_per_decl": "own elaboration time per declaration "
    "((total wall time - import time) / #declarations)",
}


def _resolve_rank_field(rank_by: str | None) -> str:
    """Map a user-facing `rank_by` value to the record field it sorts on."""
    key = (rank_by or DEFAULT_RANK_BY).strip().lower()
    if key not in _RANK_BY_FIELD:
        allowed = "own_s, s/decl"
        raise ValueError(f"unknown rank_by {rank_by!r}; choose one of: {allowed}")
    return _RANK_BY_FIELD[key]


def _rank_key(r: dict, field: str):
    """Sort key on `field`: largest value first, missing values last."""
    return (r[field] is None, -(r[field] or 0.0))


def _render(records: list[dict], skipped_no_import: int, rank_field: str) -> str:
    """Render the ranked records as a plain-text table, sorted by `rank_field`
    (largest first). Both the `own_s` and `s/decl` columns are always shown; the
    header names whichever one is the active sort key."""
    ranked = sorted(records, key=lambda r: _rank_key(r, rank_field))
    lines = [
        f"Ranked by {_RANK_FIELD_TITLE[rank_field]}, slowest first.",
        "",
        f"{'rank':>4}  {'own_s':>8}  {'s/decl':>10}  {'decls':>6}  "
        f"{'total_s':>8}  {'import_s':>8}  module",
        f"{'':->4}  {'':->8}  {'':->10}  {'':->6}  {'':->8}  {'':->8}  {'':->40}",
    ]
    for i, r in enumerate(ranked, 1):
        per = f"{r['own_s_per_decl']:.6f}" if r["own_s_per_decl"] is not None else "-"
        own = f"{r['own_s']:.3f}" if r["own_s"] is not None else "-"
        decls = f"{r['decl_count']}" if r["decl_count"] is not None else "-"
        total = f"{r['total_s']:.3f}" if r["total_s"] is not None else "-"
        imp = f"{r['import_s']:.3f}" if r["import_s"] is not None else "-"
        flag = f"  [ERROR: {r['error']}]" if r["error"] else ""
        lines.append(
            f"{i:>4}  {own:>8}  {per:>10}  {decls:>6}  "
            f"{total:>8}  {imp:>8}  {r['module']}{flag}"
        )
    if skipped_no_import:
        reason = (
            "missing import time so own_s could not be computed"
            if rank_field == "own_s"
            else "missing import time or zero declarations"
        )
        lines.append("")
        lines.append(
            f"Note: {skipped_no_import} file(s) had no {_RANK_FIELD_TITLE[rank_field]} "
            f"value (sorted last); {reason}."
        )
    return "\n".join(lines)


def _run_ranking(
    closure_json: Path | None,
    modules: list[str] | None,
    timeout: float,
    limit: int | None,
    write_output: bool,
    rank_by: str | None = None,
    pass_no=None,
) -> str:
    rank_field = _resolve_rank_field(rank_by)
    if modules is None:
        cj = closure_json or DEFAULT_CLOSURE_JSON
        if not Path(cj).is_file():
            raise FileNotFoundError(f"Closure JSON not found: {cj}")
        modules = _load_modules(Path(cj))
    if limit is not None:
        modules = modules[:limit]

    records = [_profile_one(m, timeout) for m in modules]
    ranked = sorted(records, key=lambda r: _rank_key(r, rank_field))
    skipped_no_import = sum(1 for r in records if r[rank_field] is None)
    text = _render(records, skipped_no_import, rank_field)

    if write_output:
        out_path = cache_paths.pass_dir(pass_no) / OUTPUT_NAME
        out_path.write_text(
            json.dumps(
                {
                    "command": "time lake env lean --profile <file>",
                    "pass": cache_paths.resolve_pass(pass_no),
                    "rank_by": rank_field,
                    "metric": (
                        f"ranked by {rank_field}. own_s = total_s - import_s "
                        "(total own elaboration wall time, imports subtracted); "
                        "own_s_per_decl = own_s / decl_count (per-declaration "
                        "figure). Both are reported for every module regardless of "
                        "which one is the sort key."
                    ),
                    "count": len(records),
                    "ranking": ranked,
                },
                indent=2,
            )
            + "\n"
        )
        rel = out_path.relative_to(_PROJECT_ROOT)
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
                rank_by=args.get("rank_by"),
                pass_no=args.get("pass"),
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
    rank_by = None
    pass_no = None
    if "--limit" in argv:
        limit = int(argv[argv.index("--limit") + 1])
    if "--timeout" in argv:
        timeout = float(argv[argv.index("--timeout") + 1])
    if "--rank-by" in argv:
        rank_by = argv[argv.index("--rank-by") + 1]
    if "--pass" in argv:
        pass_no = int(argv[argv.index("--pass") + 1])
    print(_run_ranking(None, None, timeout, limit, write_output=True,
                       rank_by=rank_by, pass_no=pass_no))
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
