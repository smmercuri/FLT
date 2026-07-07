"""Shared per-pass `.cache` path resolution for the FLT profiling tools.

A "pass" is one full unit of work -- a diagnosis AND the fix that follows it,
timed before and after. All per-pass artefacts live under `.cache/Pass_<n>/`;
only `log.jsonl` (an append-only, cross-pass ledger) stays at the top of
`.cache`.

Within a pass there is a `stage` dimension so the improver can compare timings
taken BEFORE a fix against timings taken AFTER it, without one clobbering the
other:

    .cache/Pass_<n>/
        before/   <- baseline timings/traces (diagnosis)
            flt_profile_ranking.json
            flt_build_times.json
            decl_profile/ ...  synth_trace/ ...  isdefeq/ ...
        after/    <- post-fix timings/traces (same relative layout)
            ...
        <cross-stage artefacts>   <- reports, before/after diffs (stage=None)

Because each tool is a separate MCP process, they agree on "which pass" via a
tiny pointer file `.cache/current_pass` holding the integer `n`. A tool call may
override the pass with an explicit `pass` argument, which also updates the
pointer so the rest of the pass follows suit. With no pointer and no override,
the pass defaults to 1.

`stage` is NOT pointer-backed: it is an explicit argument defaulting to
"before". Diagnosis therefore needs no change (everything lands in `before/`);
the fix-timing step passes `stage="after"`. Passing `stage=None` targets the
pass root, for artefacts that span both stages (a report, a before/after diff).
"""

from pathlib import Path

_HERE = Path(__file__).resolve().parent
PROJECT_ROOT = _HERE.parent
CACHE_DIR = PROJECT_ROOT / ".cache"
_POINTER = CACHE_DIR / "current_pass"
DEFAULT_PASS = 1

DEFAULT_STAGE = "before"
_STAGES = ("before", "after")
# Aliases so a caller can say "baseline"/"fixed" etc. interchangeably.
_STAGE_ALIASES = {
    "before": "before", "baseline": "before", "base": "before", "pre": "before",
    "after": "after", "fixed": "after", "fix": "after", "post": "after",
    "improved": "after",
}


def _read_pointer() -> int | None:
    try:
        return int(_POINTER.read_text().strip())
    except (OSError, ValueError):
        return None


def current_pass() -> int:
    """The pass number the pointer currently names (or DEFAULT_PASS if unset)."""
    n = _read_pointer()
    return n if n is not None else DEFAULT_PASS


def set_current_pass(n: int) -> None:
    """Point subsequent tool calls (in any tool process) at pass `n`."""
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    _POINTER.write_text(f"{int(n)}\n")


def resolve_pass(pass_no=None) -> int:
    """Resolve the effective pass: an explicit `pass_no` wins and updates the
    pointer; otherwise fall back to the current pointer / default."""
    if pass_no is not None:
        n = int(pass_no)
        if n < 1:
            raise ValueError(f"pass must be a positive integer, got {pass_no!r}")
        set_current_pass(n)
        return n
    return current_pass()


def resolve_stage(stage=None) -> str:
    """Normalise a `stage` value to 'before'/'after' (accepting aliases)."""
    key = (stage or DEFAULT_STAGE).strip().lower()
    key = _STAGE_ALIASES.get(key, key)
    if key not in _STAGES:
        raise ValueError(
            f"unknown stage {stage!r}; choose 'before' or 'after'."
        )
    return key


def pass_dir(pass_no=None, stage=DEFAULT_STAGE, create: bool = True) -> Path:
    """Directory for the resolved pass + stage.

    `stage='before'|'after'` -> `.cache/Pass_<n>/<stage>` (the default is
    'before'). `stage=None` -> the pass root `.cache/Pass_<n>`, for artefacts
    that span both stages (reports, before/after diffs)."""
    base = CACHE_DIR / f"Pass_{resolve_pass(pass_no)}"
    d = base if stage is None else base / resolve_stage(stage)
    if create:
        d.mkdir(parents=True, exist_ok=True)
    return d


def pass_subdir(name: str, pass_no=None, stage=DEFAULT_STAGE,
                create: bool = True) -> Path:
    """A named subdirectory (e.g. "decl_profile") inside the pass+stage dir."""
    d = pass_dir(pass_no, stage, create=create) / name
    if create:
        d.mkdir(parents=True, exist_ok=True)
    return d
