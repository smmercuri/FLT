"""Shared per-pass `.cache` path resolution for the FLT profiling tools.

A "pass" is one run of the diagnosis pipeline (TIME -> PROFILE -> TRACE ->
REPORT). All per-pass artefacts (rankings, decl profiles, synth/isDefEq traces,
reports) live under `.cache/Pass_<n>/`; only `log.jsonl` (an append-only,
cross-pass ledger) stays at the top of `.cache`.

Because each tool is a separate MCP process, they agree on "which pass" via a
tiny pointer file `.cache/current_pass` holding the integer `n`. A tool call may
override the pass with an explicit `pass` argument, which also updates the
pointer so the rest of the pass follows suit. With no pointer and no override,
the pass defaults to 1.
"""

from pathlib import Path

_HERE = Path(__file__).resolve().parent
PROJECT_ROOT = _HERE.parent
CACHE_DIR = PROJECT_ROOT / ".cache"
_POINTER = CACHE_DIR / "current_pass"
DEFAULT_PASS = 1


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


def pass_dir(pass_no=None, create: bool = True) -> Path:
    """`.cache/Pass_<n>` for the resolved pass, created unless `create=False`."""
    d = CACHE_DIR / f"Pass_{resolve_pass(pass_no)}"
    if create:
        d.mkdir(parents=True, exist_ok=True)
    return d


def pass_subdir(name: str, pass_no=None, create: bool = True) -> Path:
    """A named subdirectory (e.g. "decl_profile") inside the pass dir."""
    d = pass_dir(pass_no, create=create) / name
    if create:
        d.mkdir(parents=True, exist_ok=True)
    return d
