#!/usr/bin/env python3
"""
Zero-dependency stdio MCP server that measures the *instruction count* of
compiling FLT modules -- the deterministic, load-invariant metric Mathlib's
`!bench` / speed center ("radar") uses to detect compile-time regressions.

WHY INSTRUCTIONS INSTEAD OF WALL TIME
-------------------------------------
`flt_build_timing` and `flt_profile_ranking` report wall-clock seconds. Wall time
on a shared/throttling machine swings wildly (we have observed the *same
unmodified* module read 2.99s and 8.09s minutes apart, and a cold build drift
376s -> 144s with no code change). That noise can exceed the effect of a fix,
making before/after wall deltas meaningless -- and, worse, cross-session
comparisons invalid.

Retired user-space instructions (`perf stat -e instructions:u`) are the ground
truth for CPU work: independent of CPU frequency, core contention, and other
processes, with typical run-to-run variance well under 1%. They also capture the
`isDefEq`/kernel reduction that dominates these decls (unlike `#count_heartbeats`,
which only counts elaborator "heartbeat" steps and was observed moving *opposite*
to wall time). Because the metric is deterministic, an "after" number IS directly
comparable to a "before" number even across sessions -- the property wall time
lacks.

This mirrors what the Lean FRO speed center measures for Mathlib PRs.

MECHANISM
---------
For each module `M` (default: the whole import closure, or an explicit `modules`
list) the tool runs, from the project root:

    perf stat -e instructions:u -x , -- lake env lean <file-of-M>

i.e. it counts the instructions the `lean` process retires while elaborating that
one module (its imports are loaded from already-built oleans, deterministically).
This is the same per-file invocation `flt_profile_ranking` times, only counted
instead of clocked. It reports, per module: instructions (and Ginstr = /1e9), the
declaration count, and instructions-per-declaration; plus the closure total.

Unlike the wall tool, NO import-time subtraction is done: imports are identical
between a `before` and an `after` run, so they cancel in the delta, and the raw
per-module instruction count is exactly what Mathlib reports.

PLATFORM REQUIREMENT
--------------------
`perf` is Linux-only (it reads `perf_event` hardware counters). On macOS/Darwin --
where there is no equivalent per-process retired-instruction counter -- this tool
does NOT silently fall back to wall time (that would defeat its purpose); it
returns a clear "unavailable" message telling you to run it on Linux/CI (e.g. a
container or a GitHub Actions runner), which is how you replicate Mathlib's radar.
On Linux you may also need `kernel.perf_event_paranoid <= 2`
(`sudo sysctl kernel.perf_event_paranoid=2`) for user-space counting.

Exposed tool:
    flt_instruction_count(modules?, closure_json?, runs?, event?, timeout?,
                          limit?, write_output?, pass?, stage?)

Run standalone for a quick protocol smoke test:
    echo '{"jsonrpc":"2.0","id":1,"method":"tools/list"}' | tools/flt_instruction_count.py

Or measure directly (bypassing MCP):
    tools/flt_instruction_count.py --run --modules FLT.NumberField.AdeleRing
"""

import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

import cache_paths

_HERE = Path(__file__).resolve().parent
_PROJECT_ROOT = _HERE.parent
_CACHE_DIR = _PROJECT_ROOT / ".cache"
DEFAULT_CLOSURE_JSON = _CACHE_DIR / "flt_import_closure_output.json"
OUTPUT_NAME = "flt_instruction_counts.json"  # under .cache/Pass_<n>/<stage>/
FALLBACK_TARGET = "FLT.NumberField.AdeleRing"

DEFAULT_EVENT = "instructions:u"   # user-space retired instructions (Mathlib metric)
DEFAULT_RUNS = 1                   # instructions are ~deterministic; >1 = variance check
DEFAULT_TIMEOUT = 900              # seconds per module

PROTOCOL_VERSION = "2024-11-05"
SERVER_INFO = {"name": "flt-instruction-count", "version": "1.0.0"}

# Declaration keywords, matched at line start, for the instr/decl figure.
_DECL_KEYWORDS = (
    "theorem", "lemma", "def", "abbrev", "instance", "structure", "class",
    "inductive", "example", "opaque", "axiom",
)
_DECL_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|"
                      r"public\s+|scoped\s+|local\s+)*(" + "|".join(_DECL_KEYWORDS) + r")\b")
_BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)
_LINE_COMMENT = re.compile(r"--[^\n]*")

TOOLS = [
    {
        "name": "flt_instruction_count",
        "description": (
            "Measure the DETERMINISTIC instruction count of compiling FLT modules "
            "via `perf stat -e instructions:u -- lake env lean <file>` -- the "
            "load-invariant metric Mathlib's !bench / speed center ('radar') uses. "
            "Use this INSTEAD of flt_build_timing / flt_profile_ranking wall time "
            "when validating whether a fix reduced compile cost: wall time here is "
            "noise-dominated and cross-session-incomparable, whereas retired "
            "user-space instructions vary <1% run-to-run and capture isDefEq/kernel "
            "work (which heartbeats miss). Because it is deterministic, an 'after' "
            "number is directly comparable to a 'before' number even across "
            "sessions. Per module it reports instructions, Ginstr (/1e9), decls, and "
            "instr/decl, plus the closure total; ranked by instructions. Default "
            "modules = the whole import closure (or pass an explicit `modules` list "
            "to measure just the files you changed). REQUIRES perf (Linux only); on "
            "macOS/Darwin it returns an 'unavailable' message rather than silently "
            "falling back to wall time -- run it on Linux/CI to replicate the radar. "
            "Result written to .cache/Pass_<n>/<stage>/flt_instruction_counts.json."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "modules": {
                    "type": "array",
                    "items": {"type": "string"},
                    "description": (
                        "Explicit list of FLT modules to measure (e.g. "
                        "[\"FLT.Mathlib.Topology.Algebra.Module.Quotient\"]). Best for "
                        "validating a fix -- measure just the changed files, before "
                        "and after. Overrides closure_json. Defaults to the whole "
                        "import closure."
                    ),
                },
                "closure_json": {
                    "type": "string",
                    "description": (
                        "Path to the import-closure JSON to read the module list from "
                        "(default: .cache/flt_import_closure_output.json). Its "
                        "top-level `modules` array is used."
                    ),
                },
                "runs": {
                    "type": "integer",
                    "description": (
                        "How many times to measure each module (default 1). "
                        "Instructions are ~deterministic, so >1 is a consistency "
                        "check: the report shows min/median and the spread so you can "
                        "confirm stability. The median is used as the headline value."
                    ),
                },
                "event": {
                    "type": "string",
                    "description": (
                        "perf event to count (default 'instructions:u' = user-space "
                        "retired instructions, matching Mathlib). Use 'instructions' "
                        "to include kernel, or another perf event name if desired."
                    ),
                },
                "timeout": {
                    "type": "number",
                    "description": f"Per-module timeout in seconds (default {DEFAULT_TIMEOUT}).",
                },
                "limit": {
                    "type": "integer",
                    "description": "Only measure the first N modules (smoke test).",
                },
                "write_output": {
                    "type": "boolean",
                    "description": (
                        "Also write the ranked result to "
                        ".cache/Pass_<n>/<stage>/flt_instruction_counts.json "
                        "(default true)."
                    ),
                },
                "pass": {
                    "type": "integer",
                    "description": (
                        "Pass number: result written under "
                        ".cache/Pass_<n>/<stage>/. Also updates .cache/current_pass. "
                        "Defaults to the current pass pointer (or 1)."
                    ),
                },
                "stage": {
                    "type": "string",
                    "enum": ["before", "after"],
                    "description": (
                        "Within-pass bucket: 'before' (default) baseline, 'after' "
                        "post-fix. Because instructions are deterministic, the "
                        "before/after diff is meaningful even across sessions."
                    ),
                },
            },
        },
    }
]


# --------------------------------------------------------------------------- #
# perf backend
# --------------------------------------------------------------------------- #
def _perf_path() -> str | None:
    return shutil.which("perf")


def _perf_unavailable_message() -> str:
    import platform
    sysname = platform.system()
    lines = [
        "instruction counting UNAVAILABLE: `perf` was not found on PATH.",
        "",
        f"Detected platform: {sysname} {platform.machine()}.",
    ]
    if sysname == "Darwin":
        lines += [
            "",
            "`perf` is Linux-only -- it reads perf_event hardware counters that macOS",
            "does not expose, and there is no reliable per-process retired-instruction",
            "counter on Darwin. This tool deliberately does NOT fall back to wall time",
            "(that is the noisy metric it exists to replace).",
            "",
            "To replicate Mathlib's radar, run this on Linux:",
            "  - a Linux container/VM (Docker/Colima/OrbStack), or",
            "  - a GitHub Actions Linux runner (a self-hosted mini `!bench`),",
            "with the FLT+Mathlib oleans built, then call this tool there.",
        ]
    else:
        lines += [
            "",
            "Install perf (e.g. `linux-tools-common linux-tools-$(uname -r)` on",
            "Debian/Ubuntu, or `perf` on Fedora/Arch). You may also need:",
            "  sudo sysctl kernel.perf_event_paranoid=2",
            "so user-space instruction counting is permitted.",
        ]
    return "\n".join(lines)


def _parse_perf_csv(stderr: str, event: str) -> tuple[int | None, str | None]:
    """Parse `perf stat -x ,` output (written to stderr). Return (instructions,
    error). perf CSV row: value,unit,event,runtime,pct,... . The event field may
    be 'instructions:u' or 'instructions'."""
    base_event = event.split(":")[0]
    perm_hint = None
    for line in stderr.splitlines():
        low = line.lower()
        if "permission" in low or "paranoid" in low or "not permitted" in low:
            perm_hint = line.strip()
        parts = line.split(",")
        if len(parts) >= 3 and (event in parts[2] or base_event in parts[2]):
            val = parts[0].strip()
            if val in ("<not counted>", "<not supported>", ""):
                return None, (
                    f"perf reported '{val or 'empty'}' for {event} -- hardware "
                    "instruction counters are not available here"
                    + (f" ({perm_hint})" if perm_hint else "")
                )
            digits = val.replace(".", "")
            if digits.isdigit():
                return int(digits), None
    if perm_hint:
        return None, f"perf could not count {event}: {perm_hint}"
    return None, f"could not find event {event} in perf output"


def _measure_once(cmd: list[str], event: str, timeout: float) -> tuple[int | None, str | None]:
    """Run `perf stat -e <event> -x , -- <cmd>` once; return (instructions, error)."""
    perf = _perf_path()
    if perf is None:
        return None, "perf not found"
    full = [perf, "stat", "-e", event, "-x", ",", "--", *cmd]
    try:
        proc = subprocess.run(
            full,
            cwd=str(_PROJECT_ROOT),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            encoding="utf-8",
            errors="replace",
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return None, f"timed out after {timeout}s"
    except Exception as e:  # noqa: BLE001
        return None, f"{type(e).__name__}: {e}"
    instr, perr = _parse_perf_csv(proc.stderr, event)
    if proc.returncode != 0:
        # The wrapped `lake env lean` failed (perf returns the child's code).
        errline = next(
            (ln.strip() for ln in (proc.stdout or "").splitlines() if "error" in ln.lower()),
            None,
        )
        return None, errline or f"`lake env lean` exited with code {proc.returncode}"
    return instr, perr


# --------------------------------------------------------------------------- #
# module helpers
# --------------------------------------------------------------------------- #
def _module_to_path(module: str) -> Path:
    """`FLT.NumberField.AdeleRing` -> <root>/FLT/NumberField/AdeleRing.lean."""
    return _PROJECT_ROOT / (module.replace(".", "/") + ".lean")


def _count_declarations(path: Path) -> int | None:
    try:
        src = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return None
    src = _BLOCK_COMMENT.sub("", src)
    n = 0
    for line in src.splitlines():
        line = _LINE_COMMENT.sub("", line)
        if _DECL_RE.match(line):
            n += 1
    return n or None


def _median(xs: list[int]) -> int:
    s = sorted(xs)
    m = len(s)
    if m == 0:
        return 0
    if m % 2:
        return s[m // 2]
    return (s[m // 2 - 1] + s[m // 2]) // 2


def _measure_module(module: str, event: str, runs: int, timeout: float) -> dict:
    path = _module_to_path(module)
    rec = {
        "module": module,
        "file": str(path.relative_to(_PROJECT_ROOT)) if path.exists() else str(path),
        "instructions": None,
        "ginstr": None,
        "runs_completed": 0,
        "samples": [],
        "spread_pct": None,
        "decls": None,
        "instr_per_decl": None,
        "error": None,
    }
    if not path.exists():
        rec["error"] = "source file not found"
        return rec
    rec["decls"] = _count_declarations(path)
    cmd = ["lake", "env", "lean", str(path)]
    samples: list[int] = []
    for _ in range(max(1, runs)):
        instr, err = _measure_once(cmd, event, timeout)
        if err:
            rec["error"] = err
            break
        if instr is not None:
            samples.append(instr)
    rec["runs_completed"] = len(samples)
    rec["samples"] = samples
    if samples:
        med = _median(samples)
        rec["instructions"] = med
        rec["ginstr"] = round(med / 1e9, 3)
        if len(samples) > 1:
            spread = (max(samples) - min(samples)) / med * 100 if med else 0.0
            rec["spread_pct"] = round(spread, 3)
        if rec["decls"]:
            rec["instr_per_decl"] = int(med / rec["decls"])
    return rec


def _load_modules(closure_json: Path) -> list[str]:
    data = json.loads(closure_json.read_text())
    mods = data.get("modules")
    if not isinstance(mods, list) or not mods:
        raise ValueError(f"No `modules` array found in {closure_json}")
    return [m for m in mods if isinstance(m, str)]


# --------------------------------------------------------------------------- #
# render
# --------------------------------------------------------------------------- #
def _render(records: list[dict], event: str, runs: int) -> str:
    ok = [r for r in records if r["instructions"] is not None]
    ranked = sorted(ok, key=lambda r: r["instructions"], reverse=True)
    lines = [
        f"Instruction count per module ({event}, deterministic; ranked by "
        f"instructions, highest first). {runs} run(s) each.",
        "This metric is load-invariant -- before/after deltas are meaningful even "
        "across sessions.",
        "",
    ]
    header = f"{'rank':>4}  {'Ginstr':>10}  {'instructions':>15}  {'decls':>6}  {'instr/decl':>12}  module"
    lines.append(header)
    lines.append("-" * len(header))
    for i, r in enumerate(ranked, 1):
        ipd = f"{r['instr_per_decl']:,}" if r["instr_per_decl"] is not None else "-"
        decls = str(r["decls"]) if r["decls"] is not None else "-"
        spread = f"  (spread {r['spread_pct']}%)" if r.get("spread_pct") else ""
        lines.append(
            f"{i:>4}  {r['ginstr']:>10.3f}  {r['instructions']:>15,}  {decls:>6}  "
            f"{ipd:>12}  {r['module']}{spread}"
        )
    total = sum(r["instructions"] for r in ok)
    if ok:
        lines.append("-" * len(header))
        lines.append(f"      {total/1e9:>10.3f}  {total:>15,}  {'':>6}  {'':>12}  "
                     f"TOTAL ({len(ok)} module(s))")
    failed = [r for r in records if r["instructions"] is None]
    for r in failed:
        lines.append(f"  [skipped] {r['module']}: {r['error']}")
    return "\n".join(lines)


def _run_counts(
    modules: list[str] | None,
    closure_json: Path | None,
    runs: int,
    event: str,
    timeout: float,
    limit: int | None,
    write_output: bool,
    pass_no=None,
    stage=cache_paths.DEFAULT_STAGE,
) -> str:
    if _perf_path() is None:
        return _perf_unavailable_message()

    if modules:
        mods = list(modules)
    else:
        cj = closure_json or DEFAULT_CLOSURE_JSON
        try:
            mods = _load_modules(cj)
        except (OSError, ValueError, json.JSONDecodeError) as e:
            return f"error: could not load modules ({e})"
    if limit is not None:
        mods = mods[:limit]

    records = [_measure_module(m, event, runs, timeout) for m in mods]
    text = _render(records, event, runs)

    if write_output:
        ok = [r for r in records if r["instructions"] is not None]
        payload = {
            "pass": cache_paths.resolve_pass(pass_no),
            "stage": cache_paths.resolve_stage(stage),
            "metric": (
                f"instructions = retired {event} while running `lake env lean "
                "<file>` (perf stat). Deterministic/load-invariant; comparable "
                "before<->after even across sessions. instr_per_decl = instructions / "
                "#top-level decls. No import subtraction (imports cancel in the delta)."
            ),
            "event": event,
            "runs": runs,
            "total_instructions": sum(r["instructions"] for r in ok),
            "modules": records,
        }
        out_path = cache_paths.pass_dir(pass_no, stage) / OUTPUT_NAME
        out_path.write_text(json.dumps(payload, indent=2) + "\n")
        rel = str(out_path.relative_to(_PROJECT_ROOT)).replace(chr(92), "/")
        text += f"\n\n(written to {rel})"
    return text


# --------------------------------------------------------------------------- #
# MCP plumbing
# --------------------------------------------------------------------------- #
def _handle(msg: dict) -> dict | None:
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
        if name != "flt_instruction_count":
            return _err(msg_id, -32602, f"Unknown tool: {name}")
        try:
            cj = args.get("closure_json")
            text = _run_counts(
                modules=args.get("modules") or None,
                closure_json=Path(cj) if cj else None,
                runs=int(args.get("runs", DEFAULT_RUNS)),
                event=str(args.get("event", DEFAULT_EVENT)),
                timeout=float(args.get("timeout", DEFAULT_TIMEOUT)),
                limit=args.get("limit"),
                write_output=bool(args.get("write_output", True)),
                pass_no=args.get("pass"),
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


def _cli() -> int:
    """Direct run:
    flt_instruction_count.py --run [--modules A,B] [--runs N] [--event E]
        [--timeout S] [--limit N] [--pass N] [--stage before|after]"""
    argv = sys.argv[1:]
    def opt(flag, default=None):
        return argv[argv.index(flag) + 1] if flag in argv else default
    modules = None
    if "--modules" in argv:
        modules = [m for m in opt("--modules").split(",") if m]
    print(_run_counts(
        modules=modules,
        closure_json=Path(opt("--closure")) if "--closure" in argv else None,
        runs=int(opt("--runs", DEFAULT_RUNS)),
        event=str(opt("--event", DEFAULT_EVENT)),
        timeout=float(opt("--timeout", DEFAULT_TIMEOUT)),
        limit=int(opt("--limit")) if "--limit" in argv else None,
        write_output=True,
        pass_no=int(opt("--pass")) if "--pass" in argv else None,
        stage=opt("--stage", cache_paths.DEFAULT_STAGE),
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
