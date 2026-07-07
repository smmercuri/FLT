#!/usr/bin/env python3
"""
Zero-dependency stdio MCP server that times the *build* of the FLT sub-tree.

Unlike `flt_profile_ranking` (which compiles each module in isolation with
`lake env lean --profile` to attribute per-file own-time), this tool measures
the real end-to-end build by running

    lake build <targets>

which builds the target module(s) AND their whole dependency sub-tree in
parallel, rebuilding only stale targets -- exactly as a developer's build does.
Its wall time is the "overview" number: how long the sub-tree takes to build.
For per-module attribution ("which file is the bottleneck") use
`flt_profile_ranking` instead; the two are complementary.

The default target is the import-closure root (FLT.NumberField.AdeleRing, read
from .cache/flt_import_closure_output.json), so `lake build` walks precisely the
64-module closure.

Repeatability: `lake build` is idempotent -- once built, a re-run is a cached
no-op (~0s). So to measure a real build (and to make `runs`-averaging or a
before/after comparison meaningful) pass `clean=true`, which runs
`lake clean FLT` before each build.

SAFETY: the clean is ALWAYS scoped to the FLT package. Per `lake clean --help`,
a bare `lake clean` deletes the build outputs of EVERY package in the workspace,
including the Mathlib cache -- so this tool never issues a bare clean.

Exposed tool:
    flt_build_timing(targets?, clean?, runs?, timeout?, write_output?, pass?, stage?)

Run standalone for a quick protocol smoke test:
    echo '{"jsonrpc":"2.0","id":1,"method":"tools/list"}' | tools/flt_build_timing.py
"""

import json
import subprocess
import sys
import time
from pathlib import Path

import cache_paths

# Resolve paths regardless of the current working directory.
_HERE = Path(__file__).resolve().parent
_PROJECT_ROOT = _HERE.parent
_CACHE_DIR = _PROJECT_ROOT / ".cache"
DEFAULT_CLOSURE_JSON = _CACHE_DIR / "flt_import_closure_output.json"
OUTPUT_NAME = "flt_build_times.json"  # written under .cache/Pass_<n>/<stage>/
FALLBACK_TARGET = "FLT.NumberField.AdeleRing"  # if the closure JSON has no root
FLT_PACKAGE = "FLT"  # scope for `lake clean` -- NEVER clean bare (wipes Mathlib)
DEFAULT_TIMEOUT = 1800  # seconds for a build (a cold sub-tree build can be minutes)
DEFAULT_RUNS = 1

PROTOCOL_VERSION = "2024-11-05"
SERVER_INFO = {"name": "flt-build-timing", "version": "2.0.0"}

TOOLS = [
    {
        "name": "flt_build_timing",
        "description": (
            "Time the real end-to-end build of the FLT sub-tree by running "
            "`lake build <targets>` and measuring its wall-clock time. Builds the "
            "target(s) plus their whole dependency sub-tree in parallel (Mathlib "
            "deps from cache), so the number reflects an actual developer build -- "
            "the sub-tree 'overview', NOT a per-module ranking (use "
            "flt_profile_ranking for per-file attribution). Default target is the "
            "import-closure root (FLT.NumberField.AdeleRing), i.e. the whole "
            "64-module closure. `lake build` is idempotent, so a warm tree builds "
            "in ~0s; pass clean=true to run `lake clean FLT` before each build for "
            "a real cold build (needed for runs>1 averaging and for a comparable "
            "before/after). The clean is always scoped to the FLT package -- a bare "
            "`lake clean` would wipe every package incl. Mathlib, so this tool never "
            "does that. Result written to .cache/Pass_<n>/<stage>/flt_build_times.json."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "targets": {
                    "type": "array",
                    "items": {"type": "string"},
                    "description": (
                        "lake build targets (module names, e.g. "
                        "[\"FLT.NumberField.AdeleRing\"]). They are built together in "
                        "one `lake build` invocation (shared parallelism). Defaults "
                        "to the import-closure root."
                    ),
                },
                "clean": {
                    "type": "boolean",
                    "description": (
                        "If true, run `lake clean FLT` (scoped to the FLT package) "
                        "before each build so it is a real cold build of the "
                        "sub-tree. Required for meaningful runs>1 averaging and for a "
                        "comparable before/after (a warm tree otherwise builds in "
                        "~0s). Default false (times whatever is currently stale)."
                    ),
                },
                "runs": {
                    "type": "integer",
                    "description": (
                        "How many times to build, averaging the wall times (default "
                        "1). Only meaningful with clean=true (otherwise runs 2+ hit "
                        "the cache and read ~0s)."
                    ),
                },
                "timeout": {
                    "type": "number",
                    "description": (
                        f"Timeout in seconds for each build (default {DEFAULT_TIMEOUT})."
                    ),
                },
                "write_output": {
                    "type": "boolean",
                    "description": (
                        "Also write the result to "
                        ".cache/Pass_<n>/<stage>/flt_build_times.json (default true)."
                    ),
                },
                "pass": {
                    "type": "integer",
                    "description": (
                        "Pass number: result is written under "
                        ".cache/Pass_<n>/<stage>/. Passing it also updates "
                        ".cache/current_pass. Defaults to the current pass pointer "
                        "(or 1 if unset)."
                    ),
                },
                "stage": {
                    "type": "string",
                    "enum": ["before", "after"],
                    "description": (
                        "Within-pass bucket: 'before' (default) for the baseline "
                        "build time, 'after' for the post-fix build time. Writes to "
                        ".cache/Pass_<n>/<stage>/ so before and after never overwrite "
                        "each other and can be diffed."
                    ),
                },
            },
        },
    }
]


def _default_targets() -> list[str]:
    """Default `lake build` targets: the import-closure root."""
    try:
        data = json.loads(DEFAULT_CLOSURE_JSON.read_text())
        root = data.get("root")
        if isinstance(root, str) and root:
            return [root]
    except (OSError, json.JSONDecodeError):
        pass
    return [FALLBACK_TARGET]


def _run_cmd(cmd: list[str], timeout: float):
    """Run one command; return (elapsed_s, error_or_None, output)."""
    start = time.monotonic()
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(_PROJECT_ROOT),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
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
                (ln.strip() for ln in output.splitlines() if "error" in ln.lower()),
                f"`{' '.join(cmd)}` exited with code {proc.returncode}",
            )
        return elapsed, error, output
    except subprocess.TimeoutExpired:
        return time.monotonic() - start, f"timed out after {timeout}s", ""
    except Exception as e:  # noqa: BLE001 - surface any failure into the record
        return None, f"{type(e).__name__}: {e}", ""


def _time_build(targets: list[str], timeout: float, runs: int, clean: bool) -> dict:
    """Build `targets` with `lake build`, `runs` times, averaging wall time.
    With `clean`, run `lake clean FLT` before each build (scoped to FLT)."""
    runs = max(1, runs)
    record = {
        "command": "lake build " + " ".join(targets),
        "targets": targets,
        "clean": clean,
        "clean_command": f"lake clean {FLT_PACKAGE}" if clean else None,
        "runs": runs,
        "runs_completed": 0,
        "total_s": None,
        "total_s_runs": [],
        "error": None,
    }
    times: list[float] = []
    for _ in range(runs):
        if clean:
            _, cerr, _ = _run_cmd(["lake", "clean", FLT_PACKAGE], timeout)
            if cerr:
                record["error"] = f"`lake clean {FLT_PACKAGE}` failed: {cerr}"
                break
        elapsed, err, _ = _run_cmd(["lake", "build", *targets], timeout)
        if elapsed is not None:
            record["total_s_runs"].append(round(elapsed, 3))
        if err:
            record["error"] = err
            if elapsed is not None and record["total_s"] is None:
                record["total_s"] = round(elapsed, 3)
            break
        times.append(elapsed)
    record["runs_completed"] = len(times)
    if times:
        record["total_s"] = round(sum(times) / len(times), 3)
    return record


def _render(record: dict) -> str:
    r = record
    lines = [
        f"lake build timing: {' '.join(r['targets'])}",
        "=" * 60,
    ]
    if r["clean"]:
        lines.append(f"cold build: `{r['clean_command']}` (FLT package only) before each run.")
    else:
        lines.append("incremental (clean=false): times whatever is currently stale; "
                     "a fully-built tree reports ~0s.")
    if r["total_s"] is not None:
        lines.append(f"build wall time: {r['total_s']:.3f}s"
                     + (f"    (avg of {r['runs_completed']}/{r['runs']} run(s))"
                        if r["runs"] > 1 else ""))
    if len(r["total_s_runs"]) > 1:
        lines.append("per-run: " + ", ".join(f"{t:.1f}s" for t in r["total_s_runs"]))
    if not r["clean"] and r["runs"] > 1:
        lines.append("note: with clean=false, runs 2+ hit the build cache (~0s); "
                     "pass clean=true to average real builds.")
    if r["error"]:
        lines.append(f"[ERROR: {r['error']}]")
    return "\n".join(lines)


def _run_timing(
    targets: list[str] | None,
    timeout: float,
    runs: int,
    write_output: bool,
    pass_no=None,
    stage=cache_paths.DEFAULT_STAGE,
    clean: bool = False,
) -> str:
    targets = list(targets) if targets else _default_targets()
    record = _time_build(targets, timeout, runs, clean)
    text = _render(record)

    if write_output:
        out_path = cache_paths.pass_dir(pass_no, stage) / OUTPUT_NAME
        payload = {
            "pass": cache_paths.resolve_pass(pass_no),
            "stage": cache_paths.resolve_stage(stage),
            "metric": (
                "total_s = wall time of `lake build <targets>` -- the parallel "
                "sub-tree build (imports/deps served from cache). clean=true runs "
                "`lake clean FLT` first for a cold build."
            ),
            **record,
        }
        out_path.write_text(json.dumps(payload, indent=2) + "\n")
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
        if name != "flt_build_timing":
            return _err(msg_id, -32602, f"Unknown tool: {name}")
        try:
            text = _run_timing(
                targets=args.get("targets") or None,
                timeout=float(args.get("timeout", DEFAULT_TIMEOUT)),
                runs=int(args.get("runs", DEFAULT_RUNS)),
                write_output=bool(args.get("write_output", True)),
                pass_no=args.get("pass"),
                stage=args.get("stage", cache_paths.DEFAULT_STAGE),
                clean=bool(args.get("clean", False)),
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
    `flt_build_timing.py --run [--targets A,B] [--clean] [--runs N] [--timeout S]
     [--pass N] [--stage before|after]`."""
    argv = sys.argv[1:]
    targets = None
    timeout = DEFAULT_TIMEOUT
    runs = DEFAULT_RUNS
    pass_no = None
    stage = cache_paths.DEFAULT_STAGE
    clean = "--clean" in argv
    if "--targets" in argv:
        targets = [t for t in argv[argv.index("--targets") + 1].split(",") if t]
    if "--timeout" in argv:
        timeout = float(argv[argv.index("--timeout") + 1])
    if "--runs" in argv:
        runs = int(argv[argv.index("--runs") + 1])
    if "--pass" in argv:
        pass_no = int(argv[argv.index("--pass") + 1])
    if "--stage" in argv:
        stage = argv[argv.index("--stage") + 1]
    print(_run_timing(targets, timeout, runs, write_output=True,
                      pass_no=pass_no, stage=stage, clean=clean))
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
