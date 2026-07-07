#!/usr/bin/env python3
"""
Zero-dependency stdio MCP server maintaining FLT's *static heartbeat tables* --
the file-level companion to `decl_profile` and the deterministic, load-invariant
alternative to `flt_profile_ranking`'s wall-time sweep.

Why this exists
---------------
`flt_profile_ranking` re-times all 64 modules (x3 runs) every pass because wall
time is noisy and cross-session-incomparable, so a stored value is worthless.
Heartbeats are *deterministic* (they count elaborator work, not seconds), so a
measured value stays valid across sessions and machines. That makes a persistent,
incrementally-updated table possible: measure a file once, and only remeasure it
when its content -- or an upstream file it depends on -- actually changes.

Two tables live at the top of `.cache` (cross-pass, like the import closure):

    .cache/metrics_files.json / .txt   -- one row per module
        { module -> {heartbeats, decl_count, heartbeats_per_decl,
                     instructions, source_hash, measured_at, error} }
    .cache/metrics_decls.json / .txt   -- per-decl, grouped by module
        { module -> {source_hash, measured_at, total_heartbeats,
                     decls:[{decl, heartbeats}, ...]} }

`source_hash` (sha256 of the .lean bytes) is what makes updates incremental: on
each run a module is "dirty" if it is absent or its hash changed; the set actually
remeasured is the dirty modules PLUS (by default) their DIRECT dependents -- the
modules that import a dirty one -- because a downstream file's OWN heartbeat count
can shift when an upstream declaration it uses gets more/less expensive to unfold.
Everything else keeps its stored value untouched.

Metric caveats (identical to decl_profile, since the mechanism is shared):
  * Heartbeats count elaborator work (whnf / isDefEq / typeclass / simp), NOT
    kernel reduction, so `decide` / `native_decide`-heavy decls read as cheap.
  * File total = sum of the per-decl `#count_heartbeats` reports; imports are
    already-compiled oleans and contribute ~no heartbeats, so the total is
    inherently "own" cost (no import subtraction, unlike wall time).
  * `instructions` is reserved for a Linux/`perf` refill (see
    `flt_instruction_count`); it is never computed here and defaults to null on
    macOS. A remeasure preserves any previously-stored instruction value only
    when the file hash is unchanged.

Exposed tool:
    flt_heartbeat_ranking(modules?, closure_json?, refresh?, dependents?,
                          limit?, timeout?, top?, pass?, stage?, write_output?)

Run standalone for a protocol smoke test:
    echo '{"jsonrpc":"2.0","id":1,"method":"tools/list"}' | tools/flt_heartbeat_ranking.py
Or measure directly (bypassing MCP), e.g. the first 2 modules:
    tools/flt_heartbeat_ranking.py --run --limit 2
"""

import datetime
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

import cache_paths
import decl_profile  # reuse the heartbeat-injection helpers (shared mechanism)

_HERE = Path(__file__).resolve().parent
_PROJECT_ROOT = _HERE.parent
_CACHE_DIR = _PROJECT_ROOT / ".cache"
DEFAULT_CLOSURE_JSON = _CACHE_DIR / "flt_import_closure_output.json"

# Persistent, cross-pass static tables (companions to flt_import_closure_output).
FILES_TABLE_JSON = _CACHE_DIR / "metrics_files.json"
FILES_TABLE_TXT = _CACHE_DIR / "metrics_files.txt"
DECLS_TABLE_JSON = _CACHE_DIR / "metrics_decls.json"
DECLS_TABLE_TXT = _CACHE_DIR / "metrics_decls.txt"
# Per-pass snapshot, written alongside flt_profile_ranking.json etc.
PASS_RANKING_NAME = "flt_heartbeat_ranking.json"

_BUILD_TIMEOUT = 900
METRIC = "heartbeats"
DEFAULT_MODE = "before"
DEFAULT_DEPENDENTS = "direct"
# Which pass/stage bucket each mode writes its snapshot to (bootstrap/read write
# no pass snapshot -- they are table-maintenance ops, not pass artifacts).
_MODE_STAGE = {"before": "before", "after": "after"}

PROTOCOL_VERSION = "2024-11-05"
SERVER_INFO = {"name": "flt-heartbeat-ranking", "version": "1.0.0"}

TOOLS = [
    {
        "name": "flt_heartbeat_ranking",
        "description": (
            "Maintain and query FLT's STATIC HEARTBEAT TABLES -- the deterministic, "
            "load-invariant companion to flt_profile_ranking's wall-time sweep. "
            "File-level heartbeats = sum of the per-decl `#count_heartbeats` reports "
            "(same mechanism as decl_profile), import-invariant so no subtraction is "
            "needed. Two persistent, complete tables live at .cache root: "
            "metrics_files.json/.txt (all modules) and metrics_decls.json/.txt (all "
            "decls, grouped by module); each row is stamped with the source file's "
            "sha256 so updates touch only changed rows. Driven by `mode`, matching the "
            "diagnosis/fix workflow: 'bootstrap' measures every module once to fill the "
            "tables (the ONLY full sweep -- never run per pass); 'before' writes a "
            "pass's before-snapshot for the selected `modules` by READING their current "
            "values from the static table (zero compiles; measures only a file missing "
            "from the table) WITHOUT modifying existing rows; 'after' recompiles the "
            "changed `modules` (plus their direct dependents), writes the pass's "
            "after-snapshot, and writes those relevant rows back into the static tables "
            "-- the single point at which the tables change. 'read' just re-renders. "
            "Snapshots go to .cache/Pass_<n>/<before|after>/flt_heartbeat_ranking.json. "
            "Heartbeats count elaborator work (isDefEq / typeclass / simp), NOT kernel "
            "reduction, so they are a strong SELECTOR but not a precise payoff metric "
            "(gate a fix on the isDefEq/synth trace; quantify with flt_instruction_count "
            "on Linux)."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "mode": {
                    "type": "string",
                    "enum": ["before", "after", "bootstrap", "read"],
                    "description": (
                        "'before' (default): write the pass BEFORE snapshot for the "
                        "selected `modules`, reading current values from the static "
                        "table (measuring only files absent from it); existing rows are "
                        "left untouched. 'after': recompile the changed `modules` (+ "
                        "dependents), write the pass AFTER snapshot, AND update those "
                        "relevant rows in the static tables. 'bootstrap': measure every "
                        "module in scope and (re)fill the static tables -- the one-time "
                        "full sweep; writes no pass snapshot. 'read': re-render the "
                        "current table without compiling or writing snapshots."
                    ),
                },
                "dependents": {
                    "type": "string",
                    "enum": ["direct", "none", "transitive"],
                    "description": (
                        "For mode='after' only: how far to propagate a change, since a "
                        "downstream file's own heartbeat count can shift when an upstream "
                        "decl it uses changes. 'direct' (default): also remeasure modules "
                        "that directly import a changed one. 'none': only the changed "
                        "files. 'transitive': the whole downstream cone."
                    ),
                },
                "modules": {
                    "type": "array",
                    "items": {"type": "string"},
                    "description": (
                        "The modules this call is about: the ~5 selected files for "
                        "'before', the files a fix touched for 'after'. For 'bootstrap' "
                        "defaults to the whole closure. If omitted for before/after it "
                        "also defaults to the whole closure (rarely what you want -- pass "
                        "the selection)."
                    ),
                },
                "closure_json": {
                    "type": "string",
                    "description": (
                        "Path to the import-closure JSON providing the module list AND "
                        "the import graph used for dependent propagation (default: "
                        f"{DEFAULT_CLOSURE_JSON.name} in .cache)."
                    ),
                },
                "top": {
                    "type": "integer",
                    "description": "How many rows to show in the returned report (default 25; full table in the .txt/.json).",
                },
                "limit": {
                    "type": "integer",
                    "description": "Only consider the first N modules (smoke test).",
                },
                "timeout": {
                    "type": "number",
                    "description": f"Per-file compile timeout in seconds (default {_BUILD_TIMEOUT}).",
                },
                "pass": {
                    "type": "integer",
                    "description": (
                        "Pass number for the before/after snapshot under "
                        ".cache/Pass_<n>/. Also updates .cache/current_pass. The "
                        "persistent tables at .cache root are NOT pass-scoped. Defaults "
                        "to the current pass pointer (or 1)."
                    ),
                },
                "write_output": {
                    "type": "boolean",
                    "description": (
                        "Persist the updated tables (.cache/metrics_*.{json,txt}) and "
                        "the per-pass snapshot (default true). Set false for a dry run."
                    ),
                },
            },
        },
    }
]


# --------------------------------------------------------------------------- #
# Helpers
# --------------------------------------------------------------------------- #

def _module_to_path(module: str) -> Path:
    return _PROJECT_ROOT / (module.replace(".", "/") + ".lean")


def _fmt(n) -> str:
    if n is None:
        return "-"
    return f"{n:,}".replace(",", "_")


def _now() -> str:
    return datetime.datetime.now().isoformat(timespec="seconds")


def _hash_file(path: Path) -> str | None:
    try:
        return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return None


def _load_json(path: Path, default):
    if path.is_file():
        try:
            return json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            pass
    return default


def _load_modules_and_imports(closure_json: Path):
    data = json.loads(closure_json.read_text())
    modules = data.get("modules")
    if not isinstance(modules, list) or not modules:
        raise ValueError(f"No `modules` array found in {closure_json}")
    imports = data.get("imports") or {}
    return list(modules), imports


def _reverse_imports(imports: dict) -> dict:
    """module -> set of modules that DIRECTLY import it (dependents)."""
    rev: dict[str, set] = {}
    for mod, deps in imports.items():
        for d in deps:
            rev.setdefault(d, set()).add(mod)
    return rev


def _dependents(seed: set, rev: dict, mode: str, universe: set) -> set:
    """Expand `seed` by importers, restricted to `universe`. 'direct' = one hop,
    'transitive' = the whole cone, 'none' = seed unchanged."""
    if mode == "none":
        return set(seed)
    result = set(seed)
    frontier = set(seed)
    while frontier:
        nxt = set()
        for m in frontier:
            for imp in rev.get(m, ()):
                if imp in universe and imp not in result:
                    nxt.add(imp)
        result |= nxt
        if mode == "direct":
            break
        frontier = nxt
    return result


# --------------------------------------------------------------------------- #
# Measurement: inject #count_heartbeats above each decl into a SIBLING TEMP FILE
# (same directory, so imports/module resolution match), compile it, delete it.
# The tracked source file is only ever READ -- never written -- so a kill or a
# concurrent git operation can never corrupt the working tree.
# (reuses decl_profile's helpers so file total == sum of decl_profile per-decl)
# --------------------------------------------------------------------------- #

# Sibling temp files carry this suffix; it is gitignored so a leftover from a
# hard kill can never be staged/committed.
_TMP_SUFFIX = ".hbtmp.lean"


def _measure_file(module: str, timeout: float) -> dict:
    """Return {total_heartbeats, decl_count, per_decl:[{decl,heartbeats}], error}.
    Injects into a sibling temp file; the source file is never modified."""
    path = _module_to_path(module)
    if not path.is_file():
        return {"error": "file not found", "total_heartbeats": None,
                "decl_count": None, "per_decl": []}

    lines = path.read_text().splitlines(keepends=True)
    decls = decl_profile._find_decls(lines)
    if not decls:
        return {"error": "no top-level declarations", "total_heartbeats": 0,
                "decl_count": 0, "per_decl": []}

    import_idx, uses_public = decl_profile._import_insert_index(lines)
    insertions = [(bstart, "#count_heartbeats in\n") for _, bstart in decls]
    if import_idx is not None:
        style = "public import" if uses_public else "import"
        insertions.append((import_idx, f"{style} {decl_profile._IMPORT_MODULE}\n"))
    for idx, text in sorted(insertions, key=lambda t: t[0], reverse=True):
        lines.insert(idx, text)

    # Sibling temp file in the SAME directory (module resolves like the original);
    # pid-tagged so parallel measurements never collide.
    tmp = path.with_name(f"{path.stem}.{os.getpid()}{_TMP_SUFFIX}")
    output = ""
    try:
        tmp.write_text("".join(lines))
        proc = subprocess.run(
            ["lake", "env", "lean", str(tmp.relative_to(_PROJECT_ROOT))],
            cwd=str(_PROJECT_ROOT),
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=timeout,
        )
        output = proc.stdout.decode("utf-8", "replace")
    except subprocess.TimeoutExpired:
        return {"error": f"timed out after {timeout}s",
                "total_heartbeats": None, "decl_count": None, "per_decl": []}
    except Exception as e:  # noqa: BLE001
        return {"error": f"{type(e).__name__}: {e}",
                "total_heartbeats": None, "decl_count": None, "per_decl": []}
    finally:
        try:
            tmp.unlink()
        except OSError:
            pass

    used = [int(m.group(1)) for line in output.splitlines()
            if (m := decl_profile._USED_RE.search(line))]
    names = [name for name, _ in decls]
    n = min(len(used), len(names))
    per_decl = [{"decl": names[i], "heartbeats": used[i]} for i in range(n)]
    error = None
    if n != len(names):
        errs = [l for l in output.splitlines() if "error" in l.lower()][:3]
        error = (f"measured {n}/{len(names)} decls (a decl may have errored, shifting "
                 "the mapping past that point)"
                 + (": " + " | ".join(errs) if errs else ""))
    return {
        "total_heartbeats": sum(used[:n]),
        "decl_count": n,
        "per_decl": per_decl,
        "error": error,
    }


# --------------------------------------------------------------------------- #
# Table update
# --------------------------------------------------------------------------- #

def _files_entry(prev: dict | None, r: dict, source_hash: str, hash_changed: bool) -> dict:
    hb = r.get("total_heartbeats")
    dc = r.get("decl_count")
    # Preserve a previously-measured instruction count only if the file is
    # unchanged; a content change makes it stale, so it is dropped for a Linux
    # refill (flt_instruction_count).
    instructions = None
    if prev and not hash_changed:
        instructions = prev.get("instructions")
    return {
        "heartbeats": hb,
        "decl_count": dc,
        "heartbeats_per_decl": (round(hb / dc) if hb is not None and dc else None),
        "instructions": instructions,
        "source_hash": source_hash,
        "measured_at": _now(),
        "error": r.get("error"),
    }


def _render_files_txt(files_tbl: dict, order: list, current_hashes: dict,
                      remeasured: set) -> str:
    ranked = sorted(
        order,
        key=lambda m: (files_tbl.get(m, {}).get("heartbeats") is None,
                       -(files_tbl.get(m, {}).get("heartbeats") or 0)),
    )
    measured = [m for m in order if files_tbl.get(m, {}).get("heartbeats") is not None]
    total = sum(files_tbl[m]["heartbeats"] for m in measured)
    lines = [
        "FLT static heartbeat table (file level)",
        "=" * 60,
        f"metric: {METRIC} (deterministic, import-invariant; sum of per-decl "
        "#count_heartbeats)",
        f"modules: {len(order)}    measured: {len(measured)}    "
        f"unmeasured: {len(order) - len(measured)}",
        f"total heartbeats (measured files): {_fmt(total)}",
        f"last update remeasured: {len(remeasured)} file(s)",
        "",
        f"  {'rank':>4}  {'heartbeats':>12}  {'hb/decl':>9}  {'decls':>6}  "
        f"{'status':>7}  module",
        f"  {'':->4}  {'':->12}  {'':->9}  {'':->6}  {'':->7}  {'':->40}",
    ]
    for i, m in enumerate(ranked, 1):
        e = files_tbl.get(m, {})
        hb = e.get("heartbeats")
        stored_hash = e.get("source_hash")
        cur_hash = current_hashes.get(m)
        if hb is None and not e:
            status = "missing"
        elif e.get("error"):
            status = "err"
        elif stored_hash is not None and cur_hash is not None and stored_hash != cur_hash:
            status = "stale"
        else:
            status = "ok"
        mark = " *" if m in remeasured else "  "
        lines.append(
            f"  {i:>4}  {_fmt(hb):>12}  {_fmt(e.get('heartbeats_per_decl')):>9}  "
            f"{_fmt(e.get('decl_count')):>6}  {status:>7}  {m}{mark}"
        )
    lines.append("")
    lines.append("status: ok=hash matches | stale=file changed since measured "
                 "(rerun to refresh) | err=compile/mapping issue | missing=never measured")
    lines.append("'*' = remeasured on the most recent update.")
    return "\n".join(lines)


def _render_decls_txt(decls_tbl: dict, order: list, top: int) -> str:
    flat = []
    for m in order:
        e = decls_tbl.get(m)
        if not e:
            continue
        for d in e.get("decls", []):
            flat.append((d["heartbeats"], d["decl"], m))
    flat.sort(reverse=True)
    lines = [
        "FLT static heartbeat table (declaration level)",
        "=" * 60,
        f"metric: {METRIC}    decls: {len(flat)}    modules: "
        f"{sum(1 for m in order if decls_tbl.get(m))}",
        "",
        f"  {'rank':>4}  {'heartbeats':>12}  declaration   [module]",
        f"  {'':->4}  {'':->12}  {'':->50}",
    ]
    for i, (hb, decl, m) in enumerate(flat[:top], 1):
        lines.append(f"  {i:>4}  {_fmt(hb):>12}  {decl}   [{m}]")
    if len(flat) > top:
        lines.append(f"  … {len(flat) - top} more (full list in metrics_decls.json)")
    return "\n".join(lines)


def _render_report(files_tbl: dict, order: list, current_hashes: dict,
                   remeasured: set, top: int, mode: str) -> str:
    ranked = sorted(
        order,
        key=lambda m: (files_tbl.get(m, {}).get("heartbeats") is None,
                       -(files_tbl.get(m, {}).get("heartbeats") or 0)),
    )
    measured = [m for m in order if files_tbl.get(m, {}).get("heartbeats") is not None]
    stale = [m for m in order
             if (e := files_tbl.get(m)) and e.get("source_hash")
             and current_hashes.get(m) and e["source_hash"] != current_hashes[m]]
    out = [
        f"heartbeat ranking (mode={mode}); remeasured {len(remeasured)} of "
        f"{len(order)} module(s) this call.",
        f"measured: {len(measured)}/{len(order)}    stale: {len(stale)}    "
        f"(deterministic heartbeats -- values persist across sessions)",
        "",
        f"  {'rank':>4}  {'heartbeats':>12}  {'hb/decl':>9}  {'decls':>6}  module",
    ]
    for i, m in enumerate(ranked[:top], 1):
        e = files_tbl.get(m, {})
        mark = " *" if m in remeasured else ""
        out.append(
            f"  {i:>4}  {_fmt(e.get('heartbeats')):>12}  "
            f"{_fmt(e.get('heartbeats_per_decl')):>9}  "
            f"{_fmt(e.get('decl_count')):>6}  {m}{mark}"
        )
    if len(order) > top:
        out.append(f"  … {len(order) - top} more (full table in metrics_files.txt)")
    if remeasured:
        out.append("")
        out.append("remeasured (*): " + ", ".join(sorted(remeasured)))
    return "\n".join(out)


# --------------------------------------------------------------------------- #
# Core run
# --------------------------------------------------------------------------- #

def _measure_into(module, timeout, files_tbl, decls_tbl, current_hashes):
    """Measure one module and write it into both in-memory tables. Returns the
    module name (for the remeasured set)."""
    r = _measure_file(module, timeout)
    prev = files_tbl.get(module)
    h = current_hashes.get(module) or _hash_file(_module_to_path(module))
    current_hashes[module] = h
    hash_changed = (prev is None) or (prev.get("source_hash") != h)
    files_tbl[module] = _files_entry(prev, r, h, hash_changed)
    decls_tbl[module] = {
        "source_hash": h,
        "measured_at": _now(),
        "total_heartbeats": r.get("total_heartbeats"),
        "decls": r.get("per_decl", []),
    }
    return module


def run(mode=DEFAULT_MODE, modules=None, closure_json=None,
        dependents=DEFAULT_DEPENDENTS, limit=None, timeout=_BUILD_TIMEOUT,
        top=25, pass_no=None, write_output=True):
    if mode not in ("before", "after", "bootstrap", "read"):
        raise ValueError(f"unknown mode {mode!r}; choose before/after/bootstrap/read")
    cj = Path(closure_json) if closure_json else DEFAULT_CLOSURE_JSON
    if not cj.is_file():
        raise FileNotFoundError(f"Closure JSON not found: {cj}")
    all_modules, imports = _load_modules_and_imports(cj)
    # bootstrap defaults to the whole closure; the pass modes normally receive a
    # small selection but also fall back to the closure if none is given.
    order = list(modules) if modules else list(all_modules)
    if limit is not None:
        order = order[:limit]
    universe = set(all_modules)
    rev = _reverse_imports(imports)

    # Load persistent tables.
    files_doc = _load_json(FILES_TABLE_JSON, {})
    files_tbl = files_doc.get("files", {}) if isinstance(files_doc, dict) else {}
    decls_doc = _load_json(DECLS_TABLE_JSON, {})
    decls_tbl = decls_doc.get("by_module", {}) if isinstance(decls_doc, dict) else {}

    current_hashes = {m: _hash_file(_module_to_path(m)) for m in order}

    remeasured: set = set()
    table_changed = False

    if mode == "read":
        pass  # render only

    elif mode == "bootstrap":
        for m in order:
            remeasured.add(_measure_into(m, timeout, files_tbl, decls_tbl,
                                         current_hashes))
        table_changed = bool(remeasured)

    elif mode == "before":
        # Photograph the static table for the selection. Only measure a file
        # genuinely absent from the table (gap-fill); never overwrite a live row.
        for m in order:
            e = files_tbl.get(m)
            if e is None or e.get("heartbeats") is None:
                remeasured.add(_measure_into(m, timeout, files_tbl, decls_tbl,
                                             current_hashes))
        table_changed = bool(remeasured)

    else:  # mode == "after": recompute the changed rows and commit them.
        dep_universe = set(order) if limit is not None else universe
        targets = _dependents(set(order), rev, dependents, dep_universe)
        for m in sorted(targets):
            remeasured.add(_measure_into(m, timeout, files_tbl, decls_tbl,
                                         current_hashes))
        table_changed = bool(remeasured)

    report = _render_report(files_tbl, order, current_hashes, remeasured, top, mode)

    if write_output:
        # Persistent tables only get rewritten when a row actually changed, so a
        # 'read' or a no-op 'before' never rewrites them.
        if table_changed:
            _write_static_tables(files_tbl, decls_tbl, files_doc, all_modules,
                                 current_hashes, remeasured, top)
        # before/after write a pass snapshot; bootstrap/read do not.
        stage = _MODE_STAGE.get(mode)
        if stage is not None:
            snap_rel = _write_pass_snapshot(files_tbl, order, remeasured,
                                            pass_no, stage)
            report += f"\n\n(pass {stage} snapshot: {snap_rel})"
            frozen = _freeze_tables_to_pass(pass_no, stage)
            if frozen:
                report += (f"\n(frozen full tables in pass dir: "
                           f"{len(frozen)} file(s))")
            else:
                report += ("\n(no static tables to freeze yet -- run mode=bootstrap "
                           "first)")
        if table_changed:
            report += (f"\n(updated static tables: "
                       f"{FILES_TABLE_TXT.relative_to(_PROJECT_ROOT)}, "
                       f"{DECLS_TABLE_TXT.relative_to(_PROJECT_ROOT)})")
    return report


def _write_static_tables(files_tbl, decls_tbl, files_doc, all_modules,
                         current_hashes, remeasured, top):
    """Persist both complete static tables (json + human-readable txt)."""
    FILES_TABLE_JSON.write_text(json.dumps({
        "metric": METRIC,
        "description": (
            "Static file-level heartbeat table. heartbeats = sum of per-decl "
            "#count_heartbeats (deterministic, import-invariant). Rows carry the "
            "source sha256 so updates touch only changed rows. `instructions` is "
            "reserved for a Linux/perf refill (flt_instruction_count)."
        ),
        "root": files_doc.get("root") if isinstance(files_doc, dict) else None,
        "count": len(files_tbl),
        "files": files_tbl,
    }, indent=2) + "\n")
    FILES_TABLE_TXT.write_text(
        _render_files_txt(files_tbl, list(all_modules), current_hashes, remeasured)
        + "\n")
    DECLS_TABLE_JSON.write_text(json.dumps({
        "metric": METRIC,
        "description": (
            "Static declaration-level heartbeat table, grouped by module (the unit "
            "of measurement/invalidation). Produced in the same sweep as "
            "metrics_files.json."
        ),
        "count": sum(len(e.get("decls", [])) for e in decls_tbl.values()),
        "by_module": decls_tbl,
    }, indent=2) + "\n")
    DECLS_TABLE_TXT.write_text(
        _render_decls_txt(decls_tbl, list(all_modules), max(top, 50)) + "\n")


def _write_pass_snapshot(files_tbl, order, remeasured, pass_no, stage):
    """Write the selection-scoped before/after snapshot into the pass dir; return
    its repo-relative path as a string."""
    snap_ranked = sorted(
        order,
        key=lambda m: (files_tbl.get(m, {}).get("heartbeats") is None,
                       -(files_tbl.get(m, {}).get("heartbeats") or 0)),
    )
    pass_path = cache_paths.pass_dir(pass_no, stage) / PASS_RANKING_NAME
    pass_path.write_text(json.dumps({
        "metric": METRIC,
        "pass": cache_paths.resolve_pass(pass_no),
        "stage": cache_paths.resolve_stage(stage),
        "note": (
            "Deterministic heartbeat snapshot for this pass/stage, scoped to the "
            "selection, drawn from the persistent .cache/metrics_files.json table. "
            "Complements flt_profile_ranking.json (wall time) in the same directory."
        ),
        "remeasured_this_call": sorted(remeasured),
        "count": len(order),
        "ranking": [{
            "rank": i,
            "module": m,
            "heartbeats": files_tbl.get(m, {}).get("heartbeats"),
            "heartbeats_per_decl": files_tbl.get(m, {}).get("heartbeats_per_decl"),
            "decl_count": files_tbl.get(m, {}).get("decl_count"),
        } for i, m in enumerate(snap_ranked, 1)],
    }, indent=2) + "\n")
    return str(pass_path.relative_to(_PROJECT_ROOT))


def _freeze_tables_to_pass(pass_no, stage):
    """Copy the FULL static tables (files + decls, json + txt) into the pass/stage
    dir as a frozen, pass-time snapshot. Unlike flt_heartbeat_ranking.json (which is
    scoped to the pass's selection), these are the complete tables, so improvements
    can be compared across passes (e.g. diff Pass_1/after/metrics_files.json against
    Pass_2/after/metrics_files.json). Returns the list of copied repo-relative paths."""
    dest = cache_paths.pass_dir(pass_no, stage)
    copied = []
    for src in (FILES_TABLE_JSON, FILES_TABLE_TXT, DECLS_TABLE_JSON, DECLS_TABLE_TXT):
        if src.is_file():
            (dest / src.name).write_text(src.read_text())
            copied.append(str((dest / src.name).relative_to(_PROJECT_ROOT)))
    return copied


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
        if name != "flt_heartbeat_ranking":
            return _err(msg_id, -32602, f"Unknown tool: {name}")
        try:
            text = run(
                mode=args.get("mode", DEFAULT_MODE),
                modules=args.get("modules") or None,
                closure_json=args.get("closure_json"),
                dependents=args.get("dependents", DEFAULT_DEPENDENTS),
                limit=args.get("limit"),
                timeout=float(args.get("timeout", _BUILD_TIMEOUT)),
                top=int(args.get("top", 25)),
                pass_no=args.get("pass"),
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


def _cli() -> int:
    argv = sys.argv[1:]
    def opt(flag, cast=str, default=None):
        return cast(argv[argv.index(flag) + 1]) if flag in argv else default
    print(run(
        mode=opt("--mode", str, DEFAULT_MODE),
        modules=None,
        limit=opt("--limit", int),
        dependents=opt("--dependents", str, DEFAULT_DEPENDENTS),
        timeout=opt("--timeout", float, _BUILD_TIMEOUT),
        top=opt("--top", int, 25),
        pass_no=opt("--pass", int),
    ))
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
