#!/usr/bin/env python3
"""
Zero-dependency stdio MCP server that turns a `trace.Meta.synthInstance` dump
into an actionable diagnosis of *why typeclass synthesis is slow*.

Speaks JSON-RPC 2.0 over newline-delimited stdio (MCP stdio transport), so it
needs no third-party packages -- only the Python standard library.

Capture a trace first (manual, per-site). Name the dump after the declaration
so many can accumulate side by side under .cache/synth_trace/:
    set_option trace.Meta.synthInstance true in   -- above the slow declaration
    lake env lean FLT/Path/To/File.lean > .cache/synth_trace/<decl>.raw.txt 2>&1

Then this server parses that dump into a search tree, collapses nodes by
normalized goal, and ranks the waste:

    1. most-revisited goals        (a goal re-derived N times => cache-defeat / dead-end re-walk)
    2. goals by total subtree cost (the expensive problems, weighted by work done under them)
    3. expensive failing branches  (instances tried, subtree explored, then failed)
    4. culprit instances           (instance names dominating heavy / failing subtrees)

Exposed tool:
    analyze_synth_trace(path?, top?, write_output?)

Run standalone for a quick protocol smoke test:
    echo '{"jsonrpc":"2.0","id":1,"method":"tools/list"}' | tools/synth_trace.py
"""

import json
import re
import subprocess
import sys
from pathlib import Path

import cache_paths

_HERE = Path(__file__).resolve().parent
_PROJECT_ROOT = _HERE.parent

# Per-decl captures and reports accumulate under .cache/Pass_<n>/synth_trace/.
_CACHE_DIR = _PROJECT_ROOT / ".cache"
_TRACE_SUBDIR = "synth_trace"
# Fallback location used when no `label`/`path` is supplied (top-level, legacy).
_LEGACY_TRACE = _CACHE_DIR / "synth_trace_raw.txt"


def _trace_dir(pass_no=None, stage=cache_paths.DEFAULT_STAGE):
    """`.cache/Pass_<n>/<stage>/synth_trace`, created."""
    return cache_paths.pass_subdir(_TRACE_SUBDIR, pass_no, stage)

PROTOCOL_VERSION = "2024-11-05"
SERVER_INFO = {"name": "synth-trace", "version": "1.0.0"}

TOOLS = [
    {
        "name": "analyze_synth_trace",
        "description": (
            "Diagnose a slow typeclass-synthesis run. Parses a "
            "`trace.Meta.synthInstance true` dump into a search tree, collapses "
            "nodes by normalized goal, and ranks the waste: most-revisited goals, "
            "goals by total subtree cost, expensive failing branches, and the "
            "instances that dominate heavy/failing subtrees. Capture the dump "
            "first with `set_option trace.Meta.synthInstance true in` above the "
            "slow decl and `lake env lean <file> > .cache/synth_trace/<decl>.raw.txt 2>&1`."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "label": {
                    "type": "string",
                    "description": (
                        "Declaration name this trace is for. Used to locate the dump "
                        "(.cache/synth_trace/<label>.raw.txt) and to name the report "
                        "(.cache/synth_trace/<label>.report.txt), so many accumulate "
                        "side by side. Overridden by an explicit `path`."
                    ),
                },
                "path": {
                    "type": "string",
                    "description": (
                        "Explicit path to the captured trace dump. Overrides the "
                        "location derived from `label`."
                    ),
                },
                "top": {
                    "type": "integer",
                    "description": "How many rows per ranking (default 15).",
                },
                "write_output": {
                    "type": "boolean",
                    "description": (
                        "Also write the report to "
                        ".cache/Pass_<n>/synth_trace/<label>.report.txt (default true)."
                    ),
                },
                "pass": {
                    "type": "integer",
                    "description": (
                        "Pass number: dumps/reports live under "
                        ".cache/Pass_<n>/<stage>/synth_trace/. Also updates "
                        ".cache/current_pass. Defaults to the current pass pointer "
                        "(or 1 if unset)."
                    ),
                },
                "stage": {
                    "type": "string",
                    "enum": ["before", "after"],
                    "description": (
                        "Within-pass bucket: 'before' (default) = baseline, 'after' "
                        "= post-fix. Must match the stage the dump was captured "
                        "under, since the report is read back from "
                        ".cache/Pass_<n>/<stage>/synth_trace/."
                    ),
                },
            },
        },
    },
    {
        "name": "capture_synth_trace",
        "description": (
            "One-call capture + diagnosis of a slow declaration. Injects "
            "`set_option trace.Meta.synthInstance true in` above the named decl, "
            "elaborates the file with `lake env lean`, ALWAYS restores the source, "
            "dumps the trace to .cache/synth_trace/<decl>.raw.txt, then parses and "
            "ranks the waste (same report as analyze_synth_trace). SLOW: blocks on "
            "a single-file Lean elaboration (tens of seconds to minutes)."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "file": {
                    "type": "string",
                    "description": "Lean source file containing the decl (repo-relative or absolute).",
                },
                "decl": {
                    "type": "string",
                    "description": (
                        "Declaration name to trace. Used to locate the injection "
                        "point and to name the outputs. Omit only if passing `line`."
                    ),
                },
                "line": {
                    "type": "integer",
                    "description": (
                        "1-indexed line of the declaration, as an override when the "
                        "name can't be matched (e.g. an anonymous instance)."
                    ),
                },
                "top": {
                    "type": "integer",
                    "description": "How many rows per ranking (default 15).",
                },
                "write_output": {
                    "type": "boolean",
                    "description": "Write the report to .cache/Pass_<n>/synth_trace/<decl>.report.txt (default true).",
                },
                "pass": {
                    "type": "integer",
                    "description": (
                        "Pass number: dump + report go under "
                        ".cache/Pass_<n>/<stage>/synth_trace/. Also updates "
                        ".cache/current_pass. Defaults to the current pass pointer "
                        "(or 1 if unset)."
                    ),
                },
                "stage": {
                    "type": "string",
                    "enum": ["before", "after"],
                    "description": (
                        "Within-pass bucket: 'before' (default) = baseline "
                        "diagnosis, 'after' = post-fix. Writes to "
                        ".cache/Pass_<n>/<stage>/synth_trace/."
                    ),
                },
            },
            "required": ["file"],
        },
    }
]


# --------------------------------------------------------------------------- #
# Parsing: raw trace text -> search tree of Node objects
# --------------------------------------------------------------------------- #

# A logical node begins with `<indent>[Meta.synthInstance(.sub)?] <body>`.
_TAG = re.compile(r"^(?P<indent> *)\[Meta\.synthInstance(?P<sub>\.[A-Za-z]+)?\] (?P<body>.*)$")
# Leading status glyph (✅/❌/💥), optionally followed by a variation selector.
_STATUS = re.compile(r"^(?P<glyph>[✅❌\U0001f4a5])️?\s*(?P<rest>.*)$", re.DOTALL)
_MVAR = re.compile(r"\?m\.\d+")
_INSTHOLE = re.compile(r"inst✝+[¹²³⁴⁵⁶⁷⁸⁹⁰]*")
_WS = re.compile(r"\s+")

_GLYPH_STATUS = {"✅": "ok", "❌": "fail", "\U0001f4a5": "error"}


class Node:
    __slots__ = (
        "id", "depth", "sub", "status", "kind", "goal", "norm",
        "instance", "candidates", "line", "children", "parent", "_size",
    )

    def __init__(self, nid, depth, sub, line):
        self.id = nid
        self.depth = depth
        self.sub = sub            # '', apply, tryResolve, instances, answer, resume
        self.status = None        # ok | fail | error | None
        self.kind = None          # goal | result | apply | tryResolve | instances | answer | resume
        self.goal = None          # raw goal / target type (for goal, apply, answer)
        self.norm = None          # normalized goal key
        self.instance = None      # instance name (for apply)
        self.candidates = None    # list of candidate instance names (for instances)
        self.line = line          # 1-indexed source line of the tag
        self.children = []
        self.parent = None
        self._size = None


def _normalize(s: str) -> str:
    s = _MVAR.sub("?m", s)
    s = _INSTHOLE.sub("inst✝", s)
    return _WS.sub(" ", s).strip()


def _split_status(body: str):
    m = _STATUS.match(body)
    if m:
        return _GLYPH_STATUS[m.group("glyph")], m.group("rest")
    return None, body


def _classify(node: Node, body: str) -> None:
    """Fill in kind/goal/instance/candidates/status from the raw body text."""
    status, rest = _split_status(body)
    node.status = status

    sub = node.sub
    if sub == "":
        if rest.startswith("new goal "):
            node.kind = "goal"
            node.goal = rest[len("new goal "):]
        elif rest.startswith("no instances for "):
            node.kind = "goal"
            node.goal = rest[len("no instances for "):]
        elif rest.startswith("result "):
            node.kind = "result"
            node.goal = rest[len("result "):]
        else:
            # top-level synthesis entry: `✅️ CommSemiring A`
            node.kind = "goal"
            node.goal = rest
    elif sub == "apply":
        node.kind = "apply"
        m = re.match(r"^apply (?P<inst>.+?) to (?P<goal>.+)$", rest, re.DOTALL)
        if m:
            node.instance = _normalize(m.group("inst"))
            node.goal = m.group("goal")
    elif sub == "tryResolve":
        node.kind = "tryResolve"
        node.goal = rest  # `A ≟ B`
    elif sub == "instances":
        node.kind = "instances"
        inner = rest.strip()
        if inner.startswith("#[") and inner.endswith("]"):
            inner = inner[2:-1].strip()
        node.candidates = [_normalize(c) for c in inner.split(", ")] if inner else []
    elif sub == "answer":
        node.kind = "answer"
        node.goal = rest
    elif sub == "resume":
        node.kind = "resume"
        node.goal = rest
    else:
        node.kind = sub or "goal"
        node.goal = rest

    if node.goal is not None:
        node.norm = _normalize(node.goal)


def parse(text: str):
    """Parse a trace dump into (roots, all_nodes). Continuation lines (pretty-
    printed types wrapped across physical lines) are reattached to their node."""
    logical = []  # (depth, sub, body, line_no)
    for lineno, raw in enumerate(text.splitlines(), start=1):
        m = _TAG.match(raw)
        if m:
            depth = len(m.group("indent")) // 2
            sub = (m.group("sub") or "")[1:]
            logical.append([depth, sub, m.group("body"), lineno])
        elif logical:
            logical[-1][2] += " " + raw.strip()  # wrapped continuation

    all_nodes = []
    roots = []
    stack = []  # nodes on the current path, by increasing depth
    for depth, sub, body, lineno in logical:
        node = Node(len(all_nodes), depth, sub, lineno)
        _classify(node, body)
        all_nodes.append(node)
        while stack and stack[-1].depth >= depth:
            stack.pop()
        if stack:
            node.parent = stack[-1]
            stack[-1].children.append(node)
        else:
            roots.append(node)
        stack.append(node)
    return roots, all_nodes


def _subtree_size(node: Node) -> int:
    if node._size is None:
        node._size = 1 + sum(_subtree_size(c) for c in node.children)
    return node._size


# --------------------------------------------------------------------------- #
# Metrics + report
# --------------------------------------------------------------------------- #

def _truncate(s: str, n: int) -> str:
    s = s.replace("\n", " ")
    return s if len(s) <= n else s[: n - 1] + "…"


def analyze(text: str, top: int = 15) -> str:
    roots, nodes = parse(text)
    for r in roots:
        _subtree_size(r)

    goal_nodes = [n for n in nodes if n.kind == "goal" and n.norm]
    apply_nodes = [n for n in nodes if n.kind == "apply"]

    # 1 + 2: per-goal visit count and total subtree cost.
    visits, cost = {}, {}
    for n in goal_nodes:
        visits[n.norm] = visits.get(n.norm, 0) + 1
        cost[n.norm] = cost.get(n.norm, 0) + _subtree_size(n)

    distinct = len(visits)
    total_visits = sum(visits.values())
    redundancy = (total_visits / distinct) if distinct else 0.0

    # 3: expensive failing branches (a subgoal that ends in `no instances`, or a
    # failed apply that first explored a subtree).
    failures = []
    for n in nodes:
        if n.kind == "apply" and n.status == "fail":
            failures.append((_subtree_size(n), n))
        elif n.kind == "goal" and not n.children and n.status == "ok":
            # `no instances for X` with an empty candidate set is a dead end;
            # its parent apply already accounts for the cost, so skip bare ones.
            pass
    failures.sort(key=lambda t: t[0], reverse=True)

    # 4: culprit instances -- total work performed under each applied instance.
    inst_weight, inst_tries, inst_fails = {}, {}, {}
    for n in apply_nodes:
        name = n.instance or "?"
        inst_weight[name] = inst_weight.get(name, 0) + _subtree_size(n)
        inst_tries[name] = inst_tries.get(name, 0) + 1
        if n.status == "fail":
            inst_fails[name] = inst_fails.get(name, 0) + 1

    max_depth = max((n.depth for n in nodes), default=0)

    out = []
    w = out.append
    w("synthInstance trace diagnosis")
    w("=" * 60)
    w(f"logical nodes:        {len(nodes)}")
    w(f"top-level syntheses:  {len(roots)}")
    w(f"distinct goals:       {distinct}")
    w(f"total goal-visits:    {total_visits}")
    w(f"redundancy (visits/distinct): {redundancy:.1f}x")
    w(f"max search depth:     {max_depth}")
    w(f"instance applications: {len(apply_nodes)} "
      f"({sum(inst_fails.values())} failed)")

    w("")
    w(f"[1] MOST-REVISITED GOALS  (visits x -- a goal re-derived many times is")
    w(f"    a cache-defeat or a dead-end re-walked from many parents)")
    w(f"    {'visits':>6}  {'cost':>7}  goal")
    for g, c in sorted(visits.items(), key=lambda kv: kv[1], reverse=True)[:top]:
        w(f"    {c:>6}  {cost[g]:>7}  {_truncate(g, 90)}")

    w("")
    w(f"[2] GOALS BY TOTAL SUBTREE COST  (where synthesis actually spent work)")
    w(f"    {'cost':>7}  {'visits':>6}  goal")
    for g, c in sorted(cost.items(), key=lambda kv: kv[1], reverse=True)[:top]:
        w(f"    {c:>7}  {visits[g]:>6}  {_truncate(g, 90)}")

    w("")
    w(f"[3] EXPENSIVE FAILING BRANCHES  (instance applied, subtree explored,")
    w(f"    then failed to unify -- pure wasted work)")
    w(f"    {'cost':>7}  line   instance  ->  goal")
    for size, n in failures[:top]:
        w(f"    {size:>7}  {n.line:>5}  {_truncate(n.instance or '?', 34)}  ->  "
          f"{_truncate(n.norm or '', 44)}")

    w("")
    w(f"[4] CULPRIT INSTANCES  (total subtree work under each applied instance)")
    w(f"    {'work':>7}  {'tries':>5}  {'fail':>4}  instance")
    for name, wt in sorted(inst_weight.items(), key=lambda kv: kv[1], reverse=True)[:top]:
        w(f"    {wt:>7}  {inst_tries[name]:>5}  {inst_fails.get(name, 0):>4}  "
          f"{_truncate(name, 60)}")

    return "\n".join(out)


# --------------------------------------------------------------------------- #
# MCP plumbing
# --------------------------------------------------------------------------- #

_SLUG = re.compile(r"[^A-Za-z0-9._-]+")


def _slugify(s: str) -> str:
    return _SLUG.sub("_", s.strip()).strip("_") or "synth_trace"


def _resolve_input(label: str | None, path: str | None, pass_no=None,
                   stage=cache_paths.DEFAULT_STAGE) -> Path:
    """Locate the raw dump: explicit `path` wins, else
    `.cache/Pass_<n>/<stage>/synth_trace/<label>.raw.txt`, else the legacy
    flat location."""
    if path:
        p = Path(path)
        return p if p.is_absolute() else _PROJECT_ROOT / p
    if label:
        return _trace_dir(pass_no, stage) / f"{_slugify(label)}.raw.txt"
    return _LEGACY_TRACE


def _run(label: str | None, path: str | None, top: int, write_output: bool,
         pass_no=None, stage=cache_paths.DEFAULT_STAGE) -> str:
    p = _resolve_input(label, path, pass_no, stage)
    if not p.is_file():
        return f"error: trace file not found: {p}"
    report = analyze(p.read_text(errors="replace"), top=top)
    if not write_output:
        return report
    # Name the report after the label, or fall back to the input file's stem.
    slug = _slugify(label) if label else _slugify(p.stem.replace(".raw", ""))
    report_path = _trace_dir(pass_no, stage) / f"{slug}.report.txt"
    report_path.write_text(report + "\n")
    return f"{report}\n\n(written to {report_path.relative_to(_PROJECT_ROOT)})"


# --------------------------------------------------------------------------- #
# Capture: inject the trace option, elaborate the file, dump, restore.
# --------------------------------------------------------------------------- #

_OPTION_LINE = "set_option trace.Meta.synthInstance true in\n"
_BUILD_TIMEOUT = 600  # seconds; a single-file elaboration is usually well under this.

# A line that starts a declaration (after optional attributes / modifiers).
_DECL_KW = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private |protected |noncomputable |scoped |local |unsafe |partial )*"
    r"(?:def|theorem|lemma|instance|abbrev|structure|class|inductive|example)\b"
)


def _find_decl_line(lines: list[str], decl: str) -> int | None:
    name = re.compile(r"(?<![\w.])" + re.escape(decl) + r"(?![\w])")
    for i, line in enumerate(lines):
        if _DECL_KW.match(line) and name.search(line):
            return i
    return None


def _block_start(lines: list[str], idx: int) -> int:
    """Top of the contiguous non-blank block ending at the decl -- i.e. above any
    attributes / `set_option ... in` / doc comment attached to it. Inserting the
    trace option there scopes it over the whole declaration."""
    i = idx
    while i > 0 and lines[i - 1].strip() != "":
        i -= 1
    return i


def capture(file: str, decl: str | None, line: int | None,
            top: int, write_output: bool, pass_no=None,
            stage=cache_paths.DEFAULT_STAGE) -> str:
    src = Path(file)
    if not src.is_absolute():
        src = _PROJECT_ROOT / src
    if not src.is_file():
        return f"error: source file not found: {src}"

    original = src.read_text()
    lines = original.splitlines(keepends=True)

    if line is not None:
        if not (1 <= line <= len(lines)):
            return f"error: line {line} out of range (file has {len(lines)} lines)."
        decl_idx = line - 1
    elif decl:
        decl_idx = _find_decl_line(lines, decl)
        if decl_idx is None:
            return (f"error: no declaration named {decl!r} found in "
                    f"{src.relative_to(_PROJECT_ROOT)}. Pass an explicit `line`.")
    else:
        return "error: provide `decl` (or an explicit `line`)."

    ins = _block_start(lines, decl_idx)
    label = decl or f"{src.stem}_L{line}"
    slug = _slugify(label)
    trace_dir = _trace_dir(pass_no, stage)
    raw_path = trace_dir / f"{slug}.raw.txt"

    rel = src.relative_to(_PROJECT_ROOT) if src.is_relative_to(_PROJECT_ROOT) else src
    modified = lines[:ins] + [_OPTION_LINE] + lines[ins:]
    try:
        src.write_text("".join(modified))
        with open(raw_path, "wb") as out:
            subprocess.run(
                ["lake", "env", "lean", str(rel)],
                cwd=str(_PROJECT_ROOT), stdout=out, stderr=subprocess.STDOUT,
                timeout=_BUILD_TIMEOUT,
            )
    except subprocess.TimeoutExpired:
        return f"error: `lake env lean {rel}` timed out after {_BUILD_TIMEOUT}s (file restored)."
    except Exception as e:  # noqa: BLE001
        return f"error running lean: {e} (file restored)"
    finally:
        src.write_text(original)  # always restore, even on build failure

    if not raw_path.is_file() or raw_path.stat().st_size == 0:
        return f"error: no output captured to {raw_path.relative_to(_PROJECT_ROOT)}."
    trace_text = raw_path.read_text(errors="replace")
    if "[Meta.synthInstance" not in trace_text:
        head = "\n".join(trace_text.splitlines()[:15])
        return (f"captured {raw_path.relative_to(_PROJECT_ROOT)} but found no "
                f"synthInstance trace -- did elaboration reach {label!r}, and does "
                f"it trigger synthesis? First lines:\n{head}")

    report = analyze(trace_text, top=top)
    if not write_output:
        return report
    report_path = trace_dir / f"{slug}.report.txt"
    report_path.write_text(report + "\n")
    return (f"{report}\n\n(trace: {raw_path.relative_to(_PROJECT_ROOT)}  |  "
            f"report: {report_path.relative_to(_PROJECT_ROOT)})")


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
        try:
            if name == "analyze_synth_trace":
                text = _run(
                    label=args.get("label"),
                    path=args.get("path"),
                    top=int(args.get("top", 15)),
                    write_output=bool(args.get("write_output", True)),
                    pass_no=args.get("pass"),
                    stage=args.get("stage", cache_paths.DEFAULT_STAGE),
                )
            elif name == "capture_synth_trace":
                text = capture(
                    file=args.get("file"),
                    decl=args.get("decl"),
                    line=args.get("line"),
                    top=int(args.get("top", 15)),
                    write_output=bool(args.get("write_output", True)),
                    pass_no=args.get("pass"),
                    stage=args.get("stage", cache_paths.DEFAULT_STAGE),
                )
            else:
                return _err(msg_id, -32602, f"Unknown tool: {name}")
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
