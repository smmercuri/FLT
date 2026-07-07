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
  * Heartbeats are deterministic (they count work, not wall time), so the
    `runs` option defaults to 1; setting it higher only acts as a consistency
    check: the file is compiled `runs` times and each decl's heartbeat count is
    averaged across them. Barring nondeterministic elaboration they agree exactly.

Exposed tool:
    profile_file(file, decl?, top?, write_output?, runs?, pass?)

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

import cache_paths

_CACHE_DIR = _PROJECT_ROOT / ".cache"
_PROFILE_SUBDIR = "decl_profile"  # under .cache/Pass_<n>/

PROTOCOL_VERSION = "2024-11-05"
SERVER_INFO = {"name": "decl-profile", "version": "2.0.0"}

DEFAULT_RUNS = 1  # heartbeats are deterministic; >1 only re-checks consistency

TOOLS = [
    {
        "name": "profile_file",
        "description": (
            "Rank the declarations in a Lean file by heartbeat cost (deterministic) "
            "to find the worst offenders to trace next. Injects `#count_heartbeats in` "
            "above each top-level decl (exact decl<->cost assignment by construction), "
            "compiles the file `runs` times (default 1), averages each decl's heartbeat "
            "count across runs, ALWAYS restores the source, and reports a ranked "
            "per-decl profile. Pass `decl` (a name or list of names) to report just "
            "those declarations instead of the whole ranking -- each shown with its "
            "rank/share within the full file. Heartbeats count elaborator work, not "
            "kernel reduction, so `decide`-heavy decls read as cheap; `mutual` blocks "
            "count as one unit. Heartbeats are deterministic, so `runs` mainly serves "
            "as a consistency check."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "file": {
                    "type": "string",
                    "description": "Lean source file to profile (repo-relative or absolute).",
                },
                "decl": {
                    "type": ["string", "array"],
                    "items": {"type": "string"},
                    "description": (
                        "Restrict the report to one declaration name (or a list of "
                        "names), e.g. \"Submodule.quotientPiContinuousLinearEquiv\". "
                        "Names are matched exactly. The whole file is still compiled "
                        "(a decl's cold cost is only meaningful in context), but only "
                        "the requested decl(s) are reported, each annotated with its "
                        "heartbeat rank/share within the full file. Omit to rank all "
                        "decls. Filtered output is written to a separate, "
                        "content-derived name (<module>.<decl>.{report.txt,json}, or "
                        "a joined slug for a list) and never overwrites an existing "
                        "cache file -- the full-file profile, other decls, and prior "
                        "identical runs are all preserved (a numeric .2/.3 suffix is "
                        "added if needed)."
                    ),
                },
                "top": {
                    "type": "integer",
                    "description": "How many decls to show in the report (default 25; full list goes to JSON).",
                },
                "runs": {
                    "type": "integer",
                    "description": (
                        "How many times to compile the file, averaging each decl's "
                        "heartbeat count across runs (default 1, minimum 1). Heartbeats "
                        "are deterministic, so raising this is mainly a consistency check."
                    ),
                },
                "write_output": {
                    "type": "boolean",
                    "description": (
                        "Write report + machine-readable ranking to "
                        ".cache/Pass_<n>/decl_profile/<module>.{report.txt,json} "
                        "(default true)."
                    ),
                },
                "pass": {
                    "type": "integer",
                    "description": (
                        "Pass number: output goes under .cache/Pass_<n>/<stage>/. "
                        "Also updates .cache/current_pass. Defaults to the current "
                        "pass pointer (or 1 if unset)."
                    ),
                },
                "stage": {
                    "type": "string",
                    "enum": ["before", "after"],
                    "description": (
                        "Within-pass bucket: 'before' (default) for the baseline "
                        "diagnosis timing, 'after' for the post-fix re-timing. Writes "
                        "to .cache/Pass_<n>/<stage>/decl_profile/ so before and after "
                        "never overwrite each other and can be diffed."
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


def _slugify(s: str) -> str:
    """Filesystem-safe token for a decl name (keeps dots, so
    `Submodule.Quotient.foo` stays readable)."""
    return re.sub(r"[^A-Za-z0-9._-]+", "_", s).strip("_") or "decl"


def _unique_stem(directory: Path, base: str) -> str:
    """`base`, or `base.2`, `base.3`, ... -- the first for which neither
    <stem>.report.txt nor <stem>.json already exists. Guarantees a write never
    clobbers an existing profile in `directory`."""
    stem, k = base, 2
    while ((directory / f"{stem}.report.txt").exists()
           or (directory / f"{stem}.json").exists()):
        stem = f"{base}.{k}"
        k += 1
    return stem


# --------------------------------------------------------------------------- #
# Report
# --------------------------------------------------------------------------- #

def _build_report(module, ranked, top, note, rank_of=None, total_all=None):
    """Render the heartbeat report. In the default (unfiltered) mode `ranked` is
    the whole file. In filtered mode (`rank_of` given), `ranked` holds only the
    requested decls and each row is annotated with its rank/share *within the
    full file*, so a single decl's cost keeps its context."""
    out = []
    w = out.append
    filtered = rank_of is not None
    w(f"declaration heartbeat profile{' (filtered)' if filtered else ''}: {module}")
    w("=" * 60)
    if note:
        w(note)
    if not ranked:
        w("no matching declarations measured." if filtered
          else "no declarations measured.")
        return "\n".join(out)

    if filtered:
        sel = sum(hb for _, hb in ranked)
        line = f"selected: {len(ranked)} decl(s)    heartbeats: {_fmt(sel)} hb"
        if total_all:
            line += (f"    ({100 * sel / total_all:.0f}% of file total "
                     f"{_fmt(total_all)} hb across {len(rank_of)} decls)")
        w(line)
        w("")
        w(f"  {'file#':>5}  {'heartbeats':>12}  {'file%':>5}  declaration")
        for name, hb in ranked:  # show every selected decl (no `top` cap)
            pct = (100 * hb / total_all) if total_all else 0
            w(f"  {rank_of.get(name, '?'):>5}  {_fmt(hb):>12}  {pct:>4.0f}%  {name}")
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

def profile_file(file, top, write_output, pass_no=None, runs=DEFAULT_RUNS,
                 decl=None, stage=cache_paths.DEFAULT_STAGE):
    runs = max(1, runs)
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
    # Inject the markers once, then compile the file `runs` times, collecting the
    # per-decl heartbeat vector each run. The source is ALWAYS restored.
    runs_used = []  # list of per-run [heartbeats] vectors, in source order
    try:
        src.write_text("".join(lines))
        for _ in range(runs):
            proc = subprocess.run(
                ["lake", "env", "lean", str(rel)],
                cwd=str(_PROJECT_ROOT),
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=_BUILD_TIMEOUT,
            )
            output = proc.stdout.decode("utf-8", "replace")
            runs_used.append([int(m.group(1)) for line in output.splitlines()
                              if (m := _USED_RE.search(line))])
    except subprocess.TimeoutExpired:
        return f"error: `lake env lean {rel}` timed out after {_BUILD_TIMEOUT}s (file restored)."
    except Exception as e:  # noqa: BLE001
        return f"error running lean: {e} (file restored)"
    finally:
        src.write_text(original)

    # Average each decl's heartbeats across runs. Runs can differ in length only
    # if a decl errored (shifting the mapping), so align on the shortest run.
    names = [name for name, _ in decls]
    n_reports = min((len(u) for u in runs_used), default=0)
    used = [round(sum(u[k] for u in runs_used) / len(runs_used))
            for k in range(n_reports)]

    # Assign by source order: k-th `Used N` <-> k-th declaration.
    note = None
    if runs > 1:
        note = f"averaged over {runs} run(s)."
    if n_reports != len(names):
        warn = (f"warning: injected {len(names)} markers but saw {n_reports} heartbeat "
                f"reports -- a decl may have errored (assignment may be off past that "
                f"point). Aligning the first {min(n_reports, len(names))}.")
        errs = [l for l in output.splitlines() if "error" in l.lower()][:5]
        if errs:
            warn += "\n  first errors: " + " | ".join(errs)
        note = f"{note}\n{warn}" if note else warn
    pairs = list(zip(names, used))
    full_ranked = sorted(pairs, key=lambda kv: kv[1], reverse=True)
    rank_of = {name: i for i, (name, _) in enumerate(full_ranked, start=1)}
    total_all = sum(hb for _, hb in full_ranked)

    # Optional decl filter: still profiles the WHOLE file (a decl's cold cost is
    # only meaningful in context) but reports just the requested decl(s), each
    # annotated with its rank/share within the full file.
    wanted = missing = None
    if decl:
        wanted = [decl] if isinstance(decl, str) else list(decl)
        missing = [d for d in wanted if d not in rank_of]
        if missing:
            miss_note = ("requested decl(s) not found in file: " + ", ".join(missing)
                         + f" (file has {len(rank_of)} decl(s); names are matched "
                         "exactly).")
            note = f"{note}\n{miss_note}" if note else miss_note
        wanted_set = set(wanted)
        ranked = [p for p in full_ranked if p[0] in wanted_set]
    else:
        ranked = full_ranked

    module = _module_name(src)
    if wanted is not None:
        report = _build_report(module, ranked, top, note,
                               rank_of=rank_of, total_all=total_all)
    else:
        report = _build_report(module, ranked, top, note)
    if not write_output:
        return report

    profile_dir = cache_paths.pass_subdir(_PROFILE_SUBDIR, pass_no, stage)
    if wanted is None:
        # Full-file profile keeps its canonical name; a re-run within the same
        # pass refreshes it (cross-run history is captured by separate passes).
        stem = module
    else:
        # Filtered runs never clobber: the full-file profile has a different stem,
        # and distinct decl sets get distinct, content-derived names. `_unique_stem`
        # then guards against re-running the identical query in the same pass.
        if len(wanted) == 1:
            base = f"{module}.{_slugify(wanted[0])}"
        else:
            base = f"{module}.{_slugify('+'.join(sorted(wanted)))[:80]}"
        stem = _unique_stem(profile_dir, base)
    report_path = profile_dir / f"{stem}.report.txt"
    json_path = profile_dir / f"{stem}.json"
    report_path.write_text(report + "\n")
    payload = {
        "module": module,
        "file": str(rel),
        "runs": runs,
        "count": len(ranked),
        "total_heartbeats": sum(hb for _, hb in ranked),
        "ranking": [{"rank": i, "decl": n, "heartbeats": hb}
                    for i, (n, hb) in enumerate(ranked, start=1)],
    }
    if wanted is not None:
        payload["filtered_to"] = wanted
        payload["file_decl_count"] = len(full_ranked)
        payload["file_total_heartbeats"] = total_all
        # In filtered mode each row carries its file-wide rank, not a 1..k rank.
        payload["ranking"] = [{"file_rank": rank_of.get(n), "decl": n,
                               "heartbeats": hb} for (n, hb) in ranked]
        if missing:
            payload["not_found"] = missing
    json_path.write_text(json.dumps(payload, indent=2))
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
                pass_no=args.get("pass"),
                runs=int(args.get("runs", DEFAULT_RUNS)),
                decl=args.get("decl"),
                stage=args.get("stage", cache_paths.DEFAULT_STAGE),
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
