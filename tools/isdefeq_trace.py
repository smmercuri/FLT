#!/usr/bin/env python3
"""
Zero-dependency stdio MCP server that turns a `trace.Meta.isDefEq` dump into an
actionable diagnosis of *why definitional-equality checking is slow* -- the
unification work that underlies (and often dominates) slow instance search.

Sibling of tools/synth_trace.py: same nested-trace parser, but the unit here is
a unification `LHS =?= RHS` rather than a typeclass goal. Speaks JSON-RPC 2.0
over newline-delimited stdio, stdlib only.

isDefEq is called constantly -- every `tryResolve` in instance search, every
`apply`/`rw`/`simp` lemma match, every implicit argument. Its cost is dominated
by *delta unfolding* (unfolding definitions to compare them), governed by
transparency. This server ranks:

    1. most expensive unifications  (LHS =?= RHS by subtree size = defeq recursion)
    2. most repeated unifications   (the same check re-run many times)
    3. expensive failing branches   (unify explored a subtree, then failed)
    4. delta-unfold hotspots        (which definitions get unfolded most) + stuck count

Capture (manual, per-site) -- or use capture_isdefeq_trace to do it in one call:
    set_option trace.Meta.isDefEq true in         -- above the slow declaration
    lake env lean FLT/Path/To/File.lean > .cache/isdefeq/<decl>.raw.txt 2>&1

Run standalone for a quick protocol smoke test:
    echo '{"jsonrpc":"2.0","id":1,"method":"tools/list"}' | tools/isdefeq_trace.py
"""

import json
import re
import subprocess
import sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_PROJECT_ROOT = _HERE.parent

# Persistent cache for multi-pass workflows, sitting alongside log.jsonl.
_CACHE_DIR = _PROJECT_ROOT / ".cache"
_TRACE_DIR = _CACHE_DIR / "isdefeq"
_LEGACY_TRACE = _CACHE_DIR / "isdefeq_raw.txt"

PROTOCOL_VERSION = "2024-11-05"
SERVER_INFO = {"name": "isdefeq-trace", "version": "1.0.0"}

TOOLS = [
    {
        "name": "analyze_isdefeq_trace",
        "description": (
            "Diagnose a slow definitional-equality run. Parses a "
            "`trace.Meta.isDefEq true` dump into a unification tree and ranks the "
            "waste: most expensive unifications, most repeated unifications, "
            "expensive failing branches, and delta-unfold hotspots (which "
            "definitions get unfolded most). Capture the dump first with "
            "`set_option trace.Meta.isDefEq true in` above the slow decl."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "label": {
                    "type": "string",
                    "description": (
                        "Declaration name. Locates the dump "
                        "(.cache/isdefeq/<label>.raw.txt) and names the report."
                    ),
                },
                "path": {
                    "type": "string",
                    "description": "Explicit path to the dump; overrides `label`.",
                },
                "top": {"type": "integer", "description": "Rows per ranking (default 15)."},
                "write_output": {
                    "type": "boolean",
                    "description": "Write report to .cache/isdefeq/<label>.report.txt (default true).",
                },
            },
        },
    },
    {
        "name": "capture_isdefeq_trace",
        "description": (
            "One-call capture + diagnosis of a decl whose defeq checking is slow. "
            "Injects `set_option trace.Meta.isDefEq true in` above the decl "
            "(optionally `pp.all true` for a fully-explicit drill-down view), "
            "elaborates the file, ALWAYS restores the source, dumps to "
            ".cache/isdefeq/<decl>.raw.txt, then ranks the waste. SLOW: blocks on "
            "a single-file Lean elaboration; isDefEq traces are LARGE."
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
                    "description": "Declaration name to trace. Omit only if passing `line`.",
                },
                "line": {
                    "type": "integer",
                    "description": "1-indexed decl line, as an override when the name can't be matched.",
                },
                "pp_all": {
                    "type": "boolean",
                    "description": (
                        "Also inject `set_option pp.all true` for a fully-explicit "
                        "view (shows implicit args / instances / universes to expose "
                        "diamonds). Default false -- it bloats the trace and hurts "
                        "the aggregate rankings; use it for a targeted drill-down "
                        "after a suspect has been named."
                    ),
                },
                "top": {"type": "integer", "description": "Rows per ranking (default 15)."},
                "write_output": {
                    "type": "boolean",
                    "description": "Write report to .cache/isdefeq/<decl>.report.txt (default true).",
                },
            },
            "required": ["file"],
        },
    },
]


# --------------------------------------------------------------------------- #
# Parsing: raw trace text -> unification tree of Node objects
# --------------------------------------------------------------------------- #

_TAG = re.compile(r"^(?P<indent> *)\[Meta\.isDefEq(?P<sub>\.[A-Za-z.]+)?\] (?P<body>.*)$")
_STATUS = re.compile(r"^(?P<glyph>[✅❌\U0001f4a5])️?\s*(?P<rest>.*)$", re.DOTALL)
_MVAR = re.compile(r"\?m\.\d+")
_UVAR = re.compile(r"\?u\.\d+")
_INSTHOLE = re.compile(r"inst✝+[¹²³⁴⁵⁶⁷⁸⁹⁰]*")
_ASSIGNABLE = re.compile(r"\s*\[(?:non)?assignable\]")
_WS = re.compile(r"\s+")

_GLYPH_STATUS = {"✅": "ok", "❌": "fail", "\U0001f4a5": "error"}


class Node:
    __slots__ = (
        "id", "depth", "sub", "status", "kind", "lhs", "rhs", "key",
        "body", "line", "children", "parent", "_size",
    )

    def __init__(self, nid, depth, sub, line):
        self.id = nid
        self.depth = depth
        self.sub = sub            # '', delta, delta.unfoldLeft, stuck, stuckMVar, onFailure, assign, ...
        self.status = None        # ok | fail | error | None
        self.kind = None          # unify | assign | delta | stuck | other
        self.lhs = None
        self.rhs = None
        self.key = None           # normalized "LHS =?= RHS"
        self.body = None          # normalized full body (for non-unify nodes)
        self.line = line
        self.children = []
        self.parent = None
        self._size = None


def _normalize(s: str) -> str:
    s = _ASSIGNABLE.sub("", s)
    s = _MVAR.sub("?m", s)
    s = _UVAR.sub("?u", s)
    s = _INSTHOLE.sub("inst✝", s)
    return _WS.sub(" ", s).strip()


def _split_status(body: str):
    m = _STATUS.match(body)
    if m:
        return _GLYPH_STATUS[m.group("glyph")], m.group("rest")
    return None, body


def _classify(node: Node, body: str) -> None:
    status, rest = _split_status(body)
    node.status = status
    sub = node.sub

    if sub.startswith("delta"):
        node.kind = "delta"
        node.body = _normalize(rest)
        return
    if sub in ("stuck", "stuckMVar"):
        node.kind = "stuck"
        node.body = _normalize(rest)
        return

    # Core / onFailure nodes carry `LHS =?= RHS`.
    if " =?= " in rest:
        lhs, rhs = rest.split(" =?= ", 1)
        node.lhs = _normalize(lhs)
        node.rhs = _normalize(rhs)
        node.key = f"{node.lhs} =?= {node.rhs}"
        # No status glyph + assignable annotation => a metavariable assignment probe.
        node.kind = "assign" if status is None else "unify"
    else:
        node.kind = "other"
        node.body = _normalize(rest)


def parse(text: str):
    logical = []
    for lineno, raw in enumerate(text.splitlines(), start=1):
        m = _TAG.match(raw)
        if m:
            depth = len(m.group("indent")) // 2
            sub = (m.group("sub") or "")[1:]
            logical.append([depth, sub, m.group("body"), lineno])
        elif logical:
            logical[-1][2] += " " + raw.strip()

    all_nodes, roots, stack = [], [], []
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
    s = (s or "").replace("\n", " ")
    return s if len(s) <= n else s[: n - 1] + "…"


_HEAD_NOISE = {"Type", "Sort", "Prop"}


def _head(term: str):
    """Head symbol of a term -- the definition being compared/unfolded. `↑@⇑(`
    prefixes and trailing `(` are stripped; metavariables and bare sorts are
    treated as uninformative (returns None)."""
    t = (term or "").lstrip("↑@⇑( ")
    m = re.match(r"[^\s(]+", t)
    if not m:
        return None
    h = m.group(0).rstrip("(")
    if not h or h.startswith("?") or h in _HEAD_NOISE:
        return None
    return h


def analyze(text: str, top: int = 15) -> str:
    roots, nodes = parse(text)
    for r in roots:
        _subtree_size(r)

    unify = [n for n in nodes if n.kind == "unify"]
    assigns = [n for n in nodes if n.kind == "assign"]
    deltas = [n for n in nodes if n.kind == "delta"]
    stucks = [n for n in nodes if n.kind == "stuck"]

    # per-unification visit count + total subtree cost
    visits, cost = {}, {}
    for n in unify:
        visits[n.key] = visits.get(n.key, 0) + 1
        cost[n.key] = cost.get(n.key, 0) + _subtree_size(n)

    distinct = len(visits)
    total = sum(visits.values())
    redundancy = (total / distinct) if distinct else 0.0

    failures = sorted(
        ((_subtree_size(n), n) for n in unify if n.status == "fail"),
        key=lambda t: t[0], reverse=True,
    )

    # Head-symbol hotspots: which definition, appearing on the left of a `=?=`,
    # drives the most defeq work. This is the robust proxy for delta cost --
    # the actual unfolding shows up as nested `=?=` nodes, not `.delta` subclasses
    # (which frequently don't fire), so we attribute subtree cost to the head.
    head_cost, head_hits = {}, {}
    for n in unify:
        h = _head(n.lhs) or _head(n.rhs)
        if h is None:
            continue
        head_cost[h] = head_cost.get(h, 0) + _subtree_size(n)
        head_hits[h] = head_hits.get(h, 0) + 1

    max_depth = max((n.depth for n in nodes), default=0)

    out = []
    w = out.append
    w("isDefEq trace diagnosis")
    w("=" * 60)
    w(f"logical nodes:        {len(nodes)}")
    w(f"unifications (=?=):   {len(unify)}  ({sum(1 for n in unify if n.status == 'fail')} failed)")
    w(f"distinct unifications:{distinct}")
    w(f"redundancy (checks/distinct): {redundancy:.1f}x")
    w(f"mvar-assign probes:   {len(assigns)}")
    w(f"delta unfolds:        {len(deltas)}   stuck: {len(stucks)}")
    w(f"max defeq depth:      {max_depth}")

    w("")
    w("[1] MOST EXPENSIVE UNIFICATIONS  (subtree = depth of defeq recursion under")
    w("    this check -- where the unifier actually burned time)")
    w(f"    {'cost':>7}  {'checks':>6}  LHS =?= RHS")
    for k, c in sorted(cost.items(), key=lambda kv: kv[1], reverse=True)[:top]:
        w(f"    {c:>7}  {visits[k]:>6}  {_truncate(k, 84)}")

    w("")
    w("[2] MOST REPEATED UNIFICATIONS  (same check re-run -- redundant defeq)")
    w(f"    {'checks':>6}  {'cost':>7}  LHS =?= RHS")
    for k, c in sorted(visits.items(), key=lambda kv: kv[1], reverse=True)[:top]:
        w(f"    {c:>6}  {cost[k]:>7}  {_truncate(k, 84)}")

    w("")
    w("[3] EXPENSIVE FAILING UNIFICATIONS  (explored a subtree, then failed --")
    w("    pure wasted defeq work; often a transparency/diamond mismatch)")
    w(f"    {'cost':>7}  line   LHS =?= RHS")
    for size, n in failures[:top]:
        w(f"    {size:>7}  {n.line:>5}  {_truncate(n.key, 82)}")

    w("")
    w("[4] HEAD-SYMBOL HOTSPOTS  (the definition on each `=?=` that drives the most")
    w("    defeq work -- the transparency/unfold cost; mark hot ones @[reducible]")
    w("    or abbrev so the unifier can skip through them)")
    w(f"    {'cost':>7}  {'checks':>6}  head symbol")
    for h, c in sorted(head_cost.items(), key=lambda kv: kv[1], reverse=True)[:top]:
        w(f"    {c:>7}  {head_hits[h]:>6}  {_truncate(h, 84)}")
    if deltas or stucks:
        w("")
        w(f"    (explicit .delta nodes: {len(deltas)}, .stuck nodes: {len(stucks)})")

    return "\n".join(out)


# --------------------------------------------------------------------------- #
# Shared helpers
# --------------------------------------------------------------------------- #

_SLUG = re.compile(r"[^A-Za-z0-9._-]+")


def _slugify(s: str) -> str:
    return _SLUG.sub("_", s.strip()).strip("_") or "isdefeq"


def _resolve_input(label, path):
    if path:
        p = Path(path)
        return p if p.is_absolute() else _PROJECT_ROOT / p
    if label:
        return _TRACE_DIR / f"{_slugify(label)}.raw.txt"
    return _LEGACY_TRACE


def _run(label, path, top, write_output):
    p = _resolve_input(label, path)
    if not p.is_file():
        return f"error: trace file not found: {p}"
    report = analyze(p.read_text(errors="replace"), top=top)
    if not write_output:
        return report
    slug = _slugify(label) if label else _slugify(p.stem.replace(".raw", ""))
    _TRACE_DIR.mkdir(parents=True, exist_ok=True)
    report_path = _TRACE_DIR / f"{slug}.report.txt"
    report_path.write_text(report + "\n")
    return f"{report}\n\n(written to {report_path.relative_to(_PROJECT_ROOT)})"


# --------------------------------------------------------------------------- #
# Capture: inject the trace option, elaborate the file, dump, restore.
# --------------------------------------------------------------------------- #

_OPTION_LINE = "set_option trace.Meta.isDefEq true in\n"
_PPALL_LINE = "set_option pp.all true in\n"
_BUILD_TIMEOUT = 600

_DECL_KW = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private |protected |noncomputable |scoped |local |unsafe |partial )*"
    r"(?:def|theorem|lemma|instance|abbrev|structure|class|inductive|example)\b"
)


def _find_decl_line(lines, decl):
    name = re.compile(r"(?<![\w.])" + re.escape(decl) + r"(?![\w])")
    for i, line in enumerate(lines):
        if _DECL_KW.match(line) and name.search(line):
            return i
    return None


def _block_start(lines, idx):
    i = idx
    while i > 0 and lines[i - 1].strip() != "":
        i -= 1
    return i


def capture(file, decl, line, pp_all, top, write_output):
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
    _TRACE_DIR.mkdir(parents=True, exist_ok=True)
    raw_path = _TRACE_DIR / f"{slug}.raw.txt"

    inject = ([_PPALL_LINE] if pp_all else []) + [_OPTION_LINE]
    rel = src.relative_to(_PROJECT_ROOT) if src.is_relative_to(_PROJECT_ROOT) else src
    modified = lines[:ins] + inject + lines[ins:]
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
        src.write_text(original)

    if not raw_path.is_file() or raw_path.stat().st_size == 0:
        return f"error: no output captured to {raw_path.relative_to(_PROJECT_ROOT)}."
    trace_text = raw_path.read_text(errors="replace")
    if "[Meta.isDefEq" not in trace_text:
        head = "\n".join(trace_text.splitlines()[:15])
        return (f"captured {raw_path.relative_to(_PROJECT_ROOT)} but found no isDefEq "
                f"trace -- did elaboration reach {label!r}? First lines:\n{head}")

    report = analyze(trace_text, top=top)
    if not write_output:
        return report
    report_path = _TRACE_DIR / f"{slug}.report.txt"
    report_path.write_text(report + "\n")
    return (f"{report}\n\n(trace: {raw_path.relative_to(_PROJECT_ROOT)}  |  "
            f"report: {report_path.relative_to(_PROJECT_ROOT)})")


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
        try:
            if name == "analyze_isdefeq_trace":
                text = _run(
                    label=args.get("label"),
                    path=args.get("path"),
                    top=int(args.get("top", 15)),
                    write_output=bool(args.get("write_output", True)),
                )
            elif name == "capture_isdefeq_trace":
                text = capture(
                    file=args.get("file"),
                    decl=args.get("decl"),
                    line=args.get("line"),
                    pp_all=bool(args.get("pp_all", False)),
                    top=int(args.get("top", 15)),
                    write_output=bool(args.get("write_output", True)),
                )
            else:
                return _err(msg_id, -32602, f"Unknown tool: {name}")
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
