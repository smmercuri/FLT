#!/usr/bin/env python3
"""
Zero-dependency stdio MCP server that ranks the declarations of a Lean file by
heartbeat cost -- stage 2 of the diagnosis workflow ("which theorems in this
file are the worst offenders"), feeding the tracer tools (synth_trace /
isdefeq_trace) that explain a single decl.

Mechanism -- cold, per-decl `#count_heartbeats in`:
    Mathlib's `countHeartbeats` *linter* is unusable here: it re-elaborates each
    decl AFTER the normal pass, so it measures a warm-cache re-run (a near-
    constant baseline) rather than the true first elaboration. Instead this tool
    injects `#count_heartbeats in` directly ABOVE each top-level declaration, so
    the measured elaboration IS the real one (cold). The decl<->cost assignment
    is then exact by construction: the k-th `Used N heartbeats` line belongs to
    the k-th injected decl, in source order. The file is compiled once and ALWAYS
    restored.

Caveats:
  * Heartbeats count elaborator work (whnf / isDefEq / typeclass / simp), NOT
    kernel reduction, so `decide` / `native_decide`-heavy decls read as cheap.
  * `mutual` blocks are measured as a single unit; anonymous instances are
    labelled by source line.
  * Order-based assignment assumes the file compiles (an errored decl emits no
    `Used` line and would shift the mapping) -- true for checked-in FLT files.

Exposed tool:
    profile_file(file, top?, write_output?)

Run standalone for a quick protocol smoke test:
    echo '{"jsonrpc":"2.0","id":1,"method":"tools/list"}' | tools/decl_profile.py
"""

import json
import re
import subprocess
import sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_PROJECT_ROOT = _HERE.parent

_CACHE_DIR = _PROJECT_ROOT / ".cache"
_PROFILE_DIR = _CACHE_DIR / "decl_profile"

PROTOCOL_VERSION = "2024-11-05"
SERVER_INFO = {"name": "decl-profile", "version": "2.0.0"}

TOOLS = [
    {
        "name": "profile_file",
        "description": (
            "Rank the declarations in a Lean file by heartbeat cost (deterministic) "
            "to find the worst offenders to trace next. Injects `#count_heartbeats in` "
            "above each top-level decl (exact decl<->cost assignment by construction), "
            "compiles the file once, ALWAYS restores the source, and reports a ranked "
            "per-decl profile. Heartbeats count elaborator work, not kernel reduction, "
            "so `decide`-heavy decls read as cheap; `mutual` blocks count as one unit."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "file": {
                    "type": "string",
                    "description": "Lean source file to profile (repo-relative or absolute).",
                },
                "top": {
                    "type": "integer",
                    "description": "How many decls to show in the report (default 25; full list goes to JSON).",
                },
                "write_output": {
                    "type": "boolean",
                    "description": (
                        "Write report + machine-readable ranking to "
                        ".cache/decl_profile/<module>.{report.txt,json} (default true)."
                    ),
                },
            },
            "required": ["file"],
        },
    }
]

_BUILD_TIMEOUT = 900
_IMPORT_MODULE = "Mathlib.Util.CountHeartbeats"
_IMPORT_RE = re.compile(r"^\s*(?:public\s+|private\s+)?import\s+(?:all\s+)?(\S+)")
_USED_RE = re.compile(r"Used (\d+) heartbeats")

# A line that starts a top-level declaration (after optional attributes / modifiers).
_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+|unsafe\s+|partial\s+)*"
    r"(?P<kw>def|theorem|lemma|instance|abbrev|structure|class|inductive|example|mutual)\b"
    r"[ \t]*(?P<name>[^\s:({\[⦃]+)?"
)


# --------------------------------------------------------------------------- #
# Locate declarations + injection points
# --------------------------------------------------------------------------- #

def _block_start(lines, idx):
    """Top of the contiguous non-blank block ending at the decl (above its
    attributes / `set_option ... in` / doc comment)."""
    i = idx
    while i > 0 and lines[i - 1].strip() != "":
        i -= 1
    return i


def _find_decls(lines):
    """Return ordered [(name, block_start_index)] for each top-level declaration.
    Skips lines that are inside a preceding decl's block (only the first decl
    keyword of a block counts)."""
    decls = []
    claimed = set()
    for i, line in enumerate(lines):
        m = _DECL_RE.match(line)
        if not m:
            continue
        bstart = _block_start(lines, i)
        if bstart in claimed:
            continue  # a second decl keyword within the same block (rare) -- skip
        claimed.add(bstart)
        kw, name = m.group("kw"), m.group("name")
        if name and name not in ("where", "extends"):
            label = name
        else:
            label = f"{kw}@L{i + 1}"  # anonymous instance / example / mutual
        decls.append((label, bstart))
    return decls


def _import_insert_index(lines):
    last_import = None
    uses_public = False
    for i, line in enumerate(lines):
        m = _IMPORT_RE.match(line)
        if m:
            last_import = i
            if line.lstrip().startswith("public"):
                uses_public = True
            if m.group(1) == _IMPORT_MODULE:
                return None, uses_public  # already imported
    if last_import is not None:
        return last_import + 1, uses_public
    return next((i + 1 for i, l in enumerate(lines) if l.strip() == "module"), 0), uses_public


def _module_name(path: Path) -> str:
    try:
        rel = path.relative_to(_PROJECT_ROOT)
    except ValueError:
        rel = path
    return ".".join(rel.with_suffix("").parts)


def _fmt(n: int) -> str:
    return f"{n:,}".replace(",", "_")


# --------------------------------------------------------------------------- #
# Report
# --------------------------------------------------------------------------- #

def _build_report(module, ranked, top, note):
    out = []
    w = out.append
    w(f"declaration heartbeat profile: {module}")
    w("=" * 60)
    if note:
        w(note)
    if not ranked:
        w("no declarations measured.")
        return "\n".join(out)

    total = sum(hb for _, hb in ranked)
    n = len(ranked)
    mean = total // n if n else 0
    median = ranked[n // 2][1]
    top5 = sum(hb for _, hb in ranked[:5])
    share = (100 * top5 / total) if total else 0

    w(f"decls measured: {n}    total: {_fmt(total)} hb    "
      f"mean: {_fmt(mean)}    median: {_fmt(median)}")
    w(f"concentration: top 5 decls = {share:.0f}% of total heartbeats")
    w("")
    w(f"  {'rank':>4}  {'heartbeats':>12}  {'share':>5}  declaration")
    for i, (name, hb) in enumerate(ranked[:top], start=1):
        pct = (100 * hb / total) if total else 0
        w(f"  {i:>4}  {_fmt(hb):>12}  {pct:>4.0f}%  {name}")
    if len(ranked) > top:
        w(f"  … {len(ranked) - top} more (full ranking in the .json)")
    return "\n".join(out)


# --------------------------------------------------------------------------- #
# Core: parse decls -> inject markers -> compile -> restore -> zip -> rank
# --------------------------------------------------------------------------- #

def profile_file(file, top, write_output):
    src = Path(file)
    if not src.is_absolute():
        src = _PROJECT_ROOT / src
    if not src.is_file():
        return f"error: source file not found: {src}"

    original = src.read_text()
    lines = original.splitlines(keepends=True)

    decls = _find_decls(lines)
    if not decls:
        return _build_report(_module_name(src), [], top,
                             "no top-level declarations found to profile.")

    # Build all insertions, apply bottom-up so earlier indices stay valid.
    import_idx, uses_public = _import_insert_index(lines)
    insertions = [(bstart, "#count_heartbeats in\n") for _, bstart in decls]
    if import_idx is not None:
        style = "public import" if uses_public else "import"
        insertions.append((import_idx, f"{style} {_IMPORT_MODULE}\n"))
    for idx, text in sorted(insertions, key=lambda t: t[0], reverse=True):
        lines.insert(idx, text)

    rel = src.relative_to(_PROJECT_ROOT) if src.is_relative_to(_PROJECT_ROOT) else src
    try:
        src.write_text("".join(lines))
        proc = subprocess.run(
            ["lake", "env", "lean", str(rel)],
            cwd=str(_PROJECT_ROOT),
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=_BUILD_TIMEOUT,
        )
        output = proc.stdout.decode("utf-8", "replace")
    except subprocess.TimeoutExpired:
        return f"error: `lake env lean {rel}` timed out after {_BUILD_TIMEOUT}s (file restored)."
    except Exception as e:  # noqa: BLE001
        return f"error running lean: {e} (file restored)"
    finally:
        src.write_text(original)

    used = [int(m.group(1)) for line in output.splitlines()
            if (m := _USED_RE.search(line))]

    # Assign by source order: k-th `Used N` <-> k-th declaration.
    names = [name for name, _ in decls]
    note = None
    if len(used) != len(names):
        note = (f"warning: injected {len(names)} markers but saw {len(used)} heartbeat "
                f"reports -- a decl may have errored (assignment may be off past that "
                f"point). Aligning the first {min(len(used), len(names))}.")
        errs = [l for l in output.splitlines() if "error" in l.lower()][:5]
        if errs:
            note += "\n  first errors: " + " | ".join(errs)
    pairs = list(zip(names, used))
    ranked = sorted(pairs, key=lambda kv: kv[1], reverse=True)

    module = _module_name(src)
    report = _build_report(module, ranked, top, note)
    if not write_output:
        return report

    _PROFILE_DIR.mkdir(parents=True, exist_ok=True)
    report_path = _PROFILE_DIR / f"{module}.report.txt"
    json_path = _PROFILE_DIR / f"{module}.json"
    report_path.write_text(report + "\n")
    json_path.write_text(json.dumps({
        "module": module,
        "file": str(rel),
        "count": len(ranked),
        "total_heartbeats": sum(hb for _, hb in ranked),
        "ranking": [{"rank": i, "decl": n, "heartbeats": hb}
                    for i, (n, hb) in enumerate(ranked, start=1)],
    }, indent=2))
    return (f"{report}\n\n(report: {report_path.relative_to(_PROJECT_ROOT)}  |  "
            f"ranking json: {json_path.relative_to(_PROJECT_ROOT)})")


# --------------------------------------------------------------------------- #
# MCP plumbing
# --------------------------------------------------------------------------- #

def _handle(msg):
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
        if name != "profile_file":
            return _err(msg_id, -32602, f"Unknown tool: {name}")
        try:
            text = profile_file(
                file=args.get("file"),
                top=int(args.get("top", 25)),
                write_output=bool(args.get("write_output", True)),
            )
            return _ok(msg_id, {"content": [{"type": "text", "text": text}]})
        except Exception as e:  # noqa: BLE001
            return _ok(msg_id, {
                "content": [{"type": "text", "text": f"error: {e}"}],
                "isError": True,
            })
    return _err(msg_id, -32601, f"Method not found: {method}")


def _ok(msg_id, result):
    return {"jsonrpc": "2.0", "id": msg_id, "result": result}


def _err(msg_id, code, message):
    return {"jsonrpc": "2.0", "id": msg_id, "error": {"code": code, "message": message}}


def main() -> int:
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
