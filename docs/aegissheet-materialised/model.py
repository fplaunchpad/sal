#!/usr/bin/env python3
"""
AegisSheet: union-merge reference versus materialised three-way merge.

Two executable designs behind one observation function:

* `Ref`: the current Lean model transcribed. State is the finite set of
  causally annotated events; merge is set union; the observation replays the
  declarative `view` of `Sal/MRDTs/Instances/AegisSheet.lean`.
* `Mat`: the candidate materialised design. State holds live keep tokens,
  latest-position registers, active cell versions, and active range versions.
  Merge is the componentwise three-way rule `(l & a & b) | (a - l) | (b - l)`
  for sets and last-writer-wins for registers.

The harness runs both designs in lockstep on random version DAGs. Operations
are generated from the reference state, applied to both states, and the two
observations are compared at every version. Merges use a recorded version
whose event set equals the two heads' intersection as the common ancestor.

Run: python3 model.py [executions] [seed]
"""
import sys
from dataclasses import dataclass, field
from random import Random
from typing import Optional

ROW, COL = "row", "col"

# ----------------------------------------------------------------- events


@dataclass(frozen=True)
class Axis:
    kind: str            # insert | move | remove | restore
    axis: str            # ROW | COL
    id: int
    before: Optional[int]
    after: Optional[int]
    kills: frozenset = frozenset()   # named-removal variant: tokens killed


@dataclass(frozen=True)
class Cell:
    row: int
    col: int
    before: frozenset
    after: frozenset
    overwrites: frozenset


@dataclass(frozen=True)
class Range:
    id: int
    before: Optional[tuple]   # (firstRow, lastRow, firstCol, lastCol)
    after: Optional[tuple]
    overwrites: frozenset


@dataclass(frozen=True)
class Event:
    t: int
    rep: int
    seen: frozenset
    action: object            # Axis | Cell | Range (the effect)
    undo_target: Optional[int] = None


def invert(action):
    if isinstance(action, Axis):
        return Axis("restore", action.axis, action.id, action.after, action.before)
    if isinstance(action, Cell):
        return Cell(action.row, action.col, action.after, action.before, frozenset())
    return Range(action.id, action.after, action.before, frozenset())


def inverse_for(target: Event):
    inv = invert(target.action)
    if isinstance(inv, (Cell, Range)):
        return type(inv)(**{**inv.__dict__, "overwrites": frozenset({target.t})})
    return inv


# ------------------------------------------------------ reference (union)


def event_times(events):
    return {e.t for e in events}


def keeps_axis(axis, id_, e):
    a = e.action
    if isinstance(a, Axis):
        return a.axis == axis and a.id == id_ and a.after is not None
    if isinstance(a, Cell):
        return (a.row if axis == ROW else a.col) == id_
    return False


def removes_axis(axis, id_, e):
    a = e.action
    return isinstance(a, Axis) and a.axis == axis and a.id == id_ and a.after is None


def axis_known(events, axis, id_):
    return any(isinstance(e.action, Axis) and e.action.axis == axis and e.action.id == id_
               for e in events)


def axis_keep_times(events, axis, id_):
    return {e.t for e in events if keeps_axis(axis, id_, e)}


def axis_token_removed(events, axis, id_, token):
    return any(removes_axis(axis, id_, e) and token in e.seen for e in events)


def live_axis_tokens(events, axis, id_):
    return {t for t in axis_keep_times(events, axis, id_)
            if not axis_token_removed(events, axis, id_, t)}


def axis_live(events, axis, id_):
    return axis_known(events, axis, id_) and bool(live_axis_tokens(events, axis, id_))


def axis_ids(events, axis):
    return {e.action.id for e in events
            if isinstance(e.action, Axis) and e.action.axis == axis}


def live_axis_ids(events, axis):
    return {i for i in axis_ids(events, axis) if axis_live(events, axis, i)}


def axis_candidate(axis, id_, e):
    a = e.action
    return isinstance(a, Axis) and a.axis == axis and a.id == id_ and a.after is not None


def axis_positions(events, axis, id_):
    cands = [e for e in events if axis_candidate(axis, id_, e)]
    return {e.action.after for e in cands
            if not any(c.t > e.t for c in cands)}


def cell_matches(row, col, e):
    a = e.action
    return isinstance(a, Cell) and a.row == row and a.col == col


def cell_overwritten(events, cand):
    return any(isinstance(l.action, Cell) and cand.t in l.action.overwrites
               for l in events)


def active_cell_events(events, row, col):
    return [e for e in events if cell_matches(row, col, e) and not cell_overwritten(events, e)]


def active_cell_times(events, row, col):
    return {e.t for e in active_cell_events(events, row, col)}


def raw_cell_values(events, row, col):
    out = set()
    for e in active_cell_events(events, row, col):
        out |= e.action.after
    return frozenset(out)


def cell_values(events, row, col):
    if axis_live(events, ROW, row) and axis_live(events, COL, col):
        return raw_cell_values(events, row, col)
    return frozenset()


def range_overwritten(events, cand):
    return any(isinstance(l.action, Range) and cand.t in l.action.overwrites for l in events)


def active_range_events(events, id_):
    return [e for e in events if isinstance(e.action, Range) and e.action.id == id_
            and not range_overwritten(events, e)]


def active_range_times(events, id_):
    return {e.t for e in active_range_events(events, id_)}


def range_values(events, id_):
    return frozenset(e.action.after for e in active_range_events(events, id_)
                     if e.action.after is not None)


def position_option(events, axis, id_):
    ps = axis_positions(events, axis, id_)
    return min(ps) if ps else None


def live_positions(events, axis):
    out = set()
    for i in live_axis_ids(events, axis):
        out |= axis_positions(events, axis, i)
    return out


def id_at_position(events, axis, position):
    ids = [i for i in live_axis_ids(events, axis) if position in axis_positions(events, axis, i)]
    return min(ids) if ids else None


def resolve_first(events, axis, endpoint):
    if axis_live(events, axis, endpoint):
        return endpoint
    old = position_option(events, axis, endpoint)
    if old is None:
        return None
    later = [p for p in live_positions(events, axis) if old < p]
    return id_at_position(events, axis, min(later)) if later else None


def resolve_last(events, axis, endpoint):
    if axis_live(events, axis, endpoint):
        return endpoint
    old = position_option(events, axis, endpoint)
    if old is None:
        return None
    earlier = [p for p in live_positions(events, axis) if p < old]
    return id_at_position(events, axis, max(earlier)) if earlier else None


def resolve_range(events, spec):
    fr, lr, fc, lc = spec
    fr = resolve_first(events, ROW, fr)
    lr = resolve_last(events, ROW, lr)
    fc = resolve_first(events, COL, fc)
    lc = resolve_last(events, COL, lc)
    if None in (fr, lr, fc, lc):
        return None
    pos = [position_option(events, ax, i) for ax, i in ((ROW, fr), (ROW, lr), (COL, fc), (COL, lc))]
    if None in pos:
        return None
    if pos[0] <= pos[1] and pos[2] <= pos[3]:
        return (fr, lr, fc, lc)
    return None


def range_ids(events):
    return {e.action.id for e in events if isinstance(e.action, Range)}


def known_cells(events):
    return {(e.action.row, e.action.col) for e in events if isinstance(e.action, Cell)}


class Ref:
    name = "ref-union"

    @staticmethod
    def init():
        return frozenset()

    @staticmethod
    def apply(s, e):
        return s | {e}

    @staticmethod
    def merge(l, a, b):
        return a | b

    @staticmethod
    def observe(s):
        return observation_ref(s)

    @staticmethod
    def size(s):
        # timestamps stored: each event stores itself plus its `seen` frontier
        # plus its `overwrites` list.
        n = 0
        for e in s:
            n += 1 + len(e.seen)
            if isinstance(e.action, (Cell, Range)):
                n += len(e.action.overwrites)
        return n


def observation_ref(events):
    rows = frozenset(live_axis_ids(events, ROW))
    cols = frozenset(live_axis_ids(events, COL))
    pos = {}
    for ax, ids in ((ROW, rows), (COL, cols)):
        for i in ids:
            pos[(ax, i)] = frozenset(axis_positions(events, ax, i))
    cells = {rc: cell_values(events, *rc) for rc in known_cells(events)}
    ranges = {}
    resolved = {}
    for rid in range_ids(events):
        vals = range_values(events, rid)
        ranges[rid] = vals
        resolved[rid] = frozenset(resolve_range(events, sp) for sp in vals)
    return Obs(rows, cols, freeze(pos), freeze(cells), freeze(ranges), freeze(resolved))


def freeze(d):
    return frozenset(d.items())


@dataclass(frozen=True)
class Obs:
    rows: frozenset
    cols: frozenset
    pos: frozenset
    cells: frozenset
    ranges: frozenset
    resolved: frozenset


# ------------------------------------------------ materialised (three-way)


def mvr(l, a, b):
    return (l & a & b) | (a - l) | (b - l)


@dataclass
class MState:
    known: dict = field(default_factory=lambda: {ROW: set(), COL: set()})
    tokens: dict = field(default_factory=dict)     # (axis,id) -> set of ts
    pos: dict = field(default_factory=dict)        # (axis,id) -> (ts, position)
    cells: dict = field(default_factory=dict)      # (row,col) -> set of (ts, frozenset)
    ranges: dict = field(default_factory=dict)     # id -> set of (ts, spec|None)

    def copy(self):
        return MState({k: set(v) for k, v in self.known.items()},
                      {k: set(v) for k, v in self.tokens.items()},
                      dict(self.pos),
                      {k: set(v) for k, v in self.cells.items()},
                      {k: set(v) for k, v in self.ranges.items()})

    def canon(self):
        return (frozenset((k, frozenset(v)) for k, v in self.known.items()),
                frozenset((k, frozenset(v)) for k, v in self.tokens.items() if v),
                frozenset(self.pos.items()),
                frozenset((k, frozenset(v)) for k, v in self.cells.items() if v),
                frozenset((k, frozenset(v)) for k, v in self.ranges.items() if v))


class Mat:
    """Materialised design. `forget` selects the dead-register policy:
    'keep' retains every position register; 'ranges' drops registers of dead
    ids not named by a live range version; 'all' drops every dead register
    (expected to fail range resolution)."""
    name = "mat-3way"

    def __init__(self, forget="keep", binary=False, eager=False, removal="clear"):
        self.forget = forget
        self.binary = binary          # negative control: ignore the ancestor
        self.eager = eager            # negative control: re-anchor ranges at remove
        self.removal = removal        # 'clear' all live tokens, or 'named' tokens only
        self.name = (f"mat-3way[{forget},{removal}{',binary' if binary else ''}"
                     f"{',eager' if eager else ''}]")

    def plain(self):
        return not self.binary and not self.eager

    def init(self):
        return MState()

    def apply(self, s, e):
        s = s.copy()
        a = e.action
        if isinstance(a, Axis):
            s.known[a.axis].add(a.id)
            key = (a.axis, a.id)
            if a.after is not None:
                s.tokens.setdefault(key, set()).add(e.t)
                cur = s.pos.get(key)
                if cur is None or e.t > cur[0]:
                    s.pos[key] = (e.t, a.after)
            else:
                if self.eager:
                    self._reanchor(s, a.axis, a.id)
                if self.removal == "named":
                    s.tokens[key] = s.tokens.get(key, set()) - a.kills
                else:
                    s.tokens[key] = set()
        elif isinstance(a, Cell):
            s.tokens.setdefault((ROW, a.row), set()).add(e.t)
            s.tokens.setdefault((COL, a.col), set()).add(e.t)
            vs = s.cells.setdefault((a.row, a.col), set())
            s.cells[(a.row, a.col)] = {v for v in vs if v[0] not in a.overwrites} | {(e.t, a.after)}
        else:
            vs = s.ranges.setdefault(a.id, set())
            s.ranges[a.id] = {v for v in vs if v[0] not in a.overwrites} | {(e.t, a.after)}
        self._gc(s)
        return s

    def merge(self, l, a, b):
        m = MState()
        for ax in (ROW, COL):
            m.known[ax] = l.known[ax] | a.known[ax] | b.known[ax]
        keys = set(l.tokens) | set(a.tokens) | set(b.tokens)
        for k in keys:
            L, A, B = (x.tokens.get(k, set()) for x in (l, a, b))
            m.tokens[k] = (A | B) if self.binary else mvr(L, A, B)
        for k in set(l.pos) | set(a.pos) | set(b.pos):
            cands = [x.pos[k] for x in (l, a, b) if k in x.pos]
            m.pos[k] = max(cands)
        for k in set(l.cells) | set(a.cells) | set(b.cells):
            L, A, B = (x.cells.get(k, set()) for x in (l, a, b))
            m.cells[k] = (A | B) if self.binary else mvr(L, A, B)
        for k in set(l.ranges) | set(a.ranges) | set(b.ranges):
            L, A, B = (x.ranges.get(k, set()) for x in (l, a, b))
            m.ranges[k] = (A | B) if self.binary else mvr(L, A, B)
        self._gc(m)
        return m

    # -- dead-register policy -------------------------------------------
    def _referenced(self, s):
        refs = set()
        for vs in s.ranges.values():
            for _, spec in vs:
                if spec is not None:
                    fr, lr, fc, lc = spec
                    refs |= {(ROW, fr), (ROW, lr), (COL, fc), (COL, lc)}
        return refs

    def _gc(self, s):
        if self.forget == "keep":
            return
        refs = self._referenced(s) if self.forget == "ranges" else set()
        for k in list(s.pos):
            if not s.tokens.get(k) and k not in refs:
                del s.pos[k]

    def _reanchor(self, s, axis, id_):
        """Negative control: rewrite live range specs naming `id_` to the
        current successor/predecessor at deletion time."""
        old = s.pos.get((axis, id_))
        if old is None:
            return
        live = [(p, i) for (ax, i), (_, p) in s.pos.items()
                if ax == axis and s.tokens.get((ax, i)) and i != id_]
        succ = min(((p, i) for p, i in live if p > old[1]), default=(None, None))[1]
        pred = max(((p, i) for p, i in live if p < old[1]), default=(None, None))[1]
        for rid, vs in s.ranges.items():
            new = set()
            for ts, spec in vs:
                if spec is None:
                    new.add((ts, spec)); continue
                fr, lr, fc, lc = spec
                if axis == ROW:
                    fr = succ if fr == id_ else fr
                    lr = pred if lr == id_ else lr
                else:
                    fc = succ if fc == id_ else fc
                    lc = pred if lc == id_ else lc
                new.add((ts, (fr, lr, fc, lc)))
            s.ranges[rid] = new

    # -- observation -------------------------------------------------------
    def live(self, s, axis, id_):
        return id_ in s.known[axis] and bool(s.tokens.get((axis, id_)))

    def live_ids(self, s, axis):
        return {i for i in s.known[axis] if self.live(s, axis, i)}

    def position(self, s, axis, id_):
        r = s.pos.get((axis, id_))
        return None if r is None else r[1]

    def resolve_first(self, s, axis, endpoint):
        if self.live(s, axis, endpoint):
            return endpoint
        old = self.position(s, axis, endpoint)
        if old is None:
            return None
        live = [(self.position(s, axis, i), i) for i in self.live_ids(s, axis)]
        later = [(p, i) for p, i in live if p is not None and old < p]
        if not later:
            return None
        pmin = min(p for p, _ in later)
        return min(i for p, i in later if p == pmin)

    def resolve_last(self, s, axis, endpoint):
        if self.live(s, axis, endpoint):
            return endpoint
        old = self.position(s, axis, endpoint)
        if old is None:
            return None
        live = [(self.position(s, axis, i), i) for i in self.live_ids(s, axis)]
        earlier = [(p, i) for p, i in live if p is not None and p < old]
        if not earlier:
            return None
        pmax = max(p for p, _ in earlier)
        return min(i for p, i in earlier if p == pmax)

    def resolve_range(self, s, spec):
        fr, lr, fc, lc = spec
        fr = self.resolve_first(s, ROW, fr)
        lr = self.resolve_last(s, ROW, lr)
        fc = self.resolve_first(s, COL, fc)
        lc = self.resolve_last(s, COL, lc)
        if None in (fr, lr, fc, lc):
            return None
        pos = [self.position(s, ax, i) for ax, i in ((ROW, fr), (ROW, lr), (COL, fc), (COL, lc))]
        if None in pos:
            return None
        if pos[0] <= pos[1] and pos[2] <= pos[3]:
            return (fr, lr, fc, lc)
        return None

    def observe(self, s):
        rows = frozenset(self.live_ids(s, ROW))
        cols = frozenset(self.live_ids(s, COL))
        pos = {}
        for ax, ids in ((ROW, rows), (COL, cols)):
            for i in ids:
                p = self.position(s, ax, i)
                pos[(ax, i)] = frozenset() if p is None else frozenset({p})
        cells = {}
        for (r, c), vs in s.cells.items():
            if r in rows and c in cols:
                vals = set()
                for _, after in vs:
                    vals |= after
                cells[(r, c)] = frozenset(vals)
            else:
                cells[(r, c)] = frozenset()
        ranges, resolved = {}, {}
        for rid, vs in s.ranges.items():
            vals = frozenset(spec for _, spec in vs if spec is not None)
            ranges[rid] = vals
            resolved[rid] = frozenset(self.resolve_range(s, sp) for sp in vals)
        return Obs(rows, cols, freeze(pos), freeze(cells), freeze(ranges), freeze(resolved))

    def size(self, s):
        return (sum(len(v) for v in s.tokens.values()) + len(s.pos)
                + sum(len(v) for v in s.cells.values())
                + sum(len(v) for v in s.ranges.values()))


# --------------------------------------------------- honest op generator


class Clock:
    def __init__(self):
        self.t = 0

    def fresh(self):
        self.t += 1
        return self.t


UNDO_REQUIRES_LIVE_AXES = False


def gen_op(rng, events, rep, clock, ids, own_log):
    """Generate one honest event from reference state `events`. Returns the
    event or None if no operation is applicable. Mirrors `directApplicable`
    and `validUndo` in the Lean model: before-images and overwrite lists are
    read from the issuing state."""
    seen = frozenset(event_times(events))
    rows = sorted(live_axis_ids(events, ROW))
    cols = sorted(live_axis_ids(events, COL))
    choices = ["insert"]
    if rows or cols:
        choices += ["move", "remove", "range"]
    if rows and cols:
        choices += ["cell", "cell", "cell"]
    if own_log:
        choices += ["undo"]
    kind = rng.choice(choices)
    t = clock.fresh()

    def mk(action, undo=None):
        return Event(t, rep, seen, action, undo)

    if kind == "insert":
        ax = rng.choice([ROW, COL])
        i = ids.fresh()
        return mk(Axis("insert", ax, i, None, rng.randint(1, 60)))
    if kind in ("move", "remove"):
        ax = rng.choice([a for a, l in ((ROW, rows), (COL, cols)) if l])
        i = rng.choice(rows if ax == ROW else cols)
        ps = axis_positions(events, ax, i)
        if len(ps) != 1:
            return None
        before = next(iter(ps))
        after = rng.randint(1, 60) if kind == "move" else None
        kills = frozenset(live_axis_tokens(events, ax, i)) if kind == "remove" else frozenset()
        return mk(Axis(kind, ax, i, before, after, kills))
    if kind == "cell":
        r, c = rng.choice(rows), rng.choice(cols)
        return mk(Cell(r, c, cell_values(events, r, c), frozenset({ids.fresh()}),
                       frozenset(active_cell_times(events, r, c))))
    if kind == "range":
        existing = sorted(range_ids(events))
        if existing and rng.random() < 0.5:
            rid = rng.choice(existing)
            vals = range_values(events, rid)
            before = next(iter(vals)) if len(vals) == 1 else None
            if len(vals) > 1:
                return None
        else:
            rid = ids.fresh()
            before = None
        if rng.random() < 0.3 and before is not None:
            after = None
        else:
            pool_r = rows or [0]
            pool_c = cols or [0]
            fr, lr = sorted(rng.choice(pool_r) for _ in range(2))
            fc, lc = sorted(rng.choice(pool_c) for _ in range(2))
            after = (fr, lr, fc, lc)
        return mk(Range(rid, before, after, frozenset(active_range_times(events, rid))))
    if kind == "undo":
        target = rng.choice(own_log)
        if target.t not in seen or target.undo_target is not None:
            return None
        inv = inverse_for(target)
        if UNDO_REQUIRES_LIVE_AXES and isinstance(inv, Cell) and not (
                axis_live(events, ROW, inv.row) and axis_live(events, COL, inv.col)):
            return None
        if isinstance(inv, Axis) and inv.after is None:
            inv = Axis(inv.kind, inv.axis, inv.id, inv.before, None,
                       frozenset(live_axis_tokens(events, inv.axis, inv.id)))
        return mk(inv, undo=target.t)
    return None


class Ids:
    def __init__(self):
        self.n = 100

    def fresh(self):
        self.n += 1
        return self.n


# ------------------------------------------------------------ harness


def run_execution(designs, rng, n_replicas, n_rounds, max_ops, p_merge, stats, return_heads=False):
    """One random DAG execution over the reference and the given materialised
    designs in lockstep. Returns a list of violation strings."""
    bad = []
    clock, ids = Clock(), Ids()
    ref0 = Ref.init()
    init = (ref0, [d.init() for d in designs])
    versions = [init]
    heads = [init] * n_replicas
    own_logs = [[] for _ in range(n_replicas)]
    by_events = {}

    def check(tag, ref_s, mats):
        obs_ref = Ref.observe(ref_s)
        for d, ms in zip(designs, mats):
            o = d.observe(ms)
            if o != obs_ref:
                bad.append(f"DIFF[{d.name}]@{tag}: {diff(obs_ref, o)}")
        for d, ms in zip(designs, mats):
            if d.forget == "keep" and d.plain():
                if d.observe(ms) != d.observe(fold(d, ref_s)):
                    bad.append(f"FOLD[{d.name}]@{tag}: merge differs from timestamp-order replay")
        key = frozenset(ref_s)
        if key in by_events:
            prev = by_events[key]
            for d, ms, pm in zip(designs, mats, prev):
                if d.observe(ms) != d.observe(pm):
                    bad.append(f"CONV[{d.name}]@{tag}: same event set, different observation")
                if d.forget == "keep" and d.plain() and ms.canon() != pm.canon():
                    bad.append(f"CANON[{d.name}]@{tag}: same event set, different state")
        else:
            by_events[key] = mats
        stats["versions"] += 1
        stats["ref_size"] += Ref.size(ref_s)
        for d, ms in zip(designs, mats):
            stats.setdefault(("size", d.name), 0)
            stats[("size", d.name)] += d.size(ms)

    for _ in range(n_rounds):
        for r in range(n_replicas):
            ref_s, mats = heads[r]
            for _ in range(rng.randint(1, max_ops)):
                e = gen_op(rng, ref_s, r, clock, ids, own_logs[r])
                if e is None:
                    stats["skipped_ops"] += 1
                    continue
                ref_s = Ref.apply(ref_s, e)
                mats = [d.apply(m, e) for d, m in zip(designs, mats)]
                own_logs[r].append(e)
                stats["ops"] += 1
                check(f"op:r{r}", ref_s, mats)
            heads[r] = (ref_s, mats)
            versions.append(heads[r])
        if n_replicas > 1 and rng.random() < p_merge:
            i, j = rng.sample(range(n_replicas), 2)
            merged = try_merge(heads, versions, i, j, designs, stats)
            if merged is not None:
                heads[i] = merged
                versions.append(merged)
                check(f"merge:r{i}<-r{j}", *merged)
    # forced convergence along different topologies
    for _ in range(3 * n_replicas):
        for i in range(n_replicas):
            for j in range(n_replicas):
                if i != j:
                    merged = try_merge(heads, versions, i, j, designs, stats)
                    if merged is not None:
                        heads[i] = merged
                        versions.append(merged)
                        check(f"final:r{i}<-r{j}", *merged)
    if return_heads:
        return heads
    return bad


def fold(d, events):
    """Replay `events` in timestamp order from the empty state."""
    s = d.init()
    for e in sorted(events, key=lambda e: e.t):
        s = d.apply(s, e)
    return s


def try_merge(heads, versions, i, j, designs, stats):
    (ri, mi), (rj, mj) = heads[i], heads[j]
    if ri == rj:
        return None
    if rj <= ri:
        return None
    inter = ri & rj
    lca = next((v for v in versions if v[0] == inter), None)
    if lca is None:
        # no registered greatest common ancestor: use the canonical state of the
        # intersection event set as the virtual merge base
        stats["virtual_merges"] += 1
        bases = [fold(d, inter) for d in designs]
    else:
        stats["merges"] += 1
        bases = lca[1]
    mats = [d.merge(l, a, b) for d, l, a, b in zip(designs, bases, mi, mj)]
    return (Ref.merge(inter, ri, rj), mats)


def diff(a: Obs, b: Obs):
    out = []
    for f in ("rows", "cols", "pos", "cells", "ranges", "resolved"):
        x, y = getattr(a, f), getattr(b, f)
        if x != y:
            out.append(f"{f}: ref-only={sorted(map(repr, x - y))[:3]} mat-only={sorted(map(repr, y - x))[:3]}")
    return "; ".join(out)


def campaign(designs, executions, seed, label):
    rng = Random(seed)
    stats = {"versions": 0, "ops": 0, "skipped_ops": 0, "merges": 0, "virtual_merges": 0,
             "ref_size": 0}
    failures = []
    for k in range(executions):
        n_rep = rng.choice([2, 3, 3, 4])
        bad = run_execution(designs, rng, n_rep, rng.randint(3, 8), 3, 0.7, stats)
        if bad:
            failures.append((k, bad[0]))
    print(f"== {label}: {executions} executions, seed {seed}")
    print(f"   versions {stats['versions']}, ops {stats['ops']} (skipped {stats['skipped_ops']}), "
          f"merges {stats['merges']} with a registered ancestor, "
          f"{stats['virtual_merges']} with a virtual base")
    for d in designs:
        n = sum(1 for _, b in failures if f"[{d.name}]" in b)
        print(f"   {d.name}: {n} failing executions"
              + (f"; first: {next(b for _, b in failures if f'[{d.name}]' in b)[:200]}" if n else ""))
    v = max(stats["versions"], 1)
    print(f"   mean stored timestamps per version: ref {stats['ref_size'] / v:.1f}"
          + "".join(f", {d.name} {stats[('size', d.name)] / v:.1f}" for d in designs))
    return failures


def growth(designs, seed, rounds_list=(4, 8, 16, 32), executions=20):
    """Final-version state size as history length grows (3 replicas)."""
    print(f"== size growth: {executions} executions per row, seed {seed}, 3 replicas")
    print("   rounds  ops   ref-timestamps  " + "  ".join(d.name for d in designs))
    for rounds in rounds_list:
        rng = Random(seed)
        tot = {"ref": 0, "ops": 0}
        for d in designs:
            tot[d.name] = 0
        for _ in range(executions):
            stats = {"versions": 0, "ops": 0, "skipped_ops": 0, "merges": 0,
                     "virtual_merges": 0, "ref_size": 0}
            heads = run_execution(designs, rng, 3, rounds, 3, 0.7, stats, return_heads=True)
            ref_s, mats = heads[0]
            tot["ref"] += Ref.size(ref_s)
            tot["ops"] += stats["ops"]
            for d, m in zip(designs, mats):
                tot[d.name] += d.size(m)
        n = executions
        print(f"   {rounds:>6}  {tot['ops']/n:>5.0f}  {tot['ref']/n:>14.1f}  "
              + "  ".join(f"{tot[d.name]/n:>{len(d.name)}.1f}" for d in designs))


# ------------------------------------------- Lean SPOT fixtures (reference)


def ax(t, rep, seen, kind, axis, id_, before, after):
    return Event(t, rep, frozenset(seen), Axis(kind, axis, id_, before, after))


def ce(t, rep, seen, row, col, before, after, ov):
    return Event(t, rep, frozenset(seen), Cell(row, col, frozenset(before), frozenset(after), frozenset(ov)))


def un(t, rep, seen, target):
    return Event(t, rep, frozenset(seen), inverse_for(target), target.t)


def ra(t, rep, seen, rid, before, after, ov):
    return Event(t, rep, frozenset(seen), Range(rid, before, after, frozenset(ov)))


def check_fixtures():
    """Hand-derived expectations copied from the Lean SPOTs in
    Instances/AegisSheet.lean. Validates the Python transcription."""
    r0, r1, c0, c1, r2 = 10, 11, 20, 21, 12
    base_row = ax(1, 0, {}, "insert", ROW, r0, None, 10)
    base_col = ax(2, 0, {1}, "insert", COL, c0, None, 10)
    base_cell = ce(3, 0, {1, 2}, r0, c0, {}, {0}, {})
    base = {base_row, base_col, base_cell}
    rem = ax(4, 1, {1, 2, 3}, "remove", ROW, r0, 10, None)
    edit = ce(5, 2, {1, 2, 3}, r0, c0, {0}, {1}, {3})
    s = base | {rem, edit}
    assert axis_live(s, ROW, r0) and cell_values(s, r0, c0) == {1}
    later_rem = ax(6, 1, {1, 2, 3, 5}, "remove", ROW, r0, 10, None)
    assert not axis_live(base | {edit, later_rem}, ROW, r0)
    edit_a = ce(4, 1, {1, 2, 3}, r0, c0, {0}, {1}, {3})
    edit_b = ce(5, 2, {1, 2, 3}, r0, c0, {0}, {2}, {3})
    conflict = base | {edit_a, edit_b}
    assert cell_values(conflict, r0, c0) == {1, 2}
    undo_a = un(6, 1, {1, 2, 3, 4, 5}, edit_a)
    assert cell_values(conflict | {undo_a}, r0, c0) == {0, 2}
    move = ax(5, 2, {1, 2, 3}, "move", ROW, r0, 10, 30)
    s = base | {rem, move}
    assert axis_live(s, ROW, r0) and axis_positions(s, ROW, r0) == {30}
    move_early = ax(4, 1, {1, 2, 3}, "move", ROW, r0, 10, 20)
    assert axis_positions(base | {move_early, move}, ROW, r0) == {30}
    ins_row = ax(4, 1, {1, 2, 3}, "insert", ROW, r1, None, 15)
    s = base | {ins_row, rem}
    assert not axis_live(s, ROW, r0) and axis_live(s, ROW, r1)
    undo_rem = un(6, 1, {1, 2, 3, 4}, rem)
    s = base | {rem, undo_rem}
    assert axis_live(s, ROW, r0) and axis_positions(s, ROW, r0) == {10}
    undo_ins = un(6, 1, {1, 2, 3, 4}, ins_row)
    s = base | {ins_row, undo_ins}
    assert not axis_live(s, ROW, r1) and axis_live(s, ROW, r0)
    t4_move = ax(4, 1, {1, 2, 3}, "move", ROW, r0, 10, 30)
    t4_ins = ax(5, 2, {1, 2, 3}, "insert", ROW, r1, None, 20)
    t4_undo = un(6, 1, {1, 2, 3, 4, 5}, t4_move)
    s = base | {t4_move, t4_ins, t4_undo}
    assert axis_positions(s, ROW, r0) == {10} and axis_positions(s, ROW, r1) == {20}
    t4_cmove = ax(5, 2, {1, 2, 3}, "move", ROW, r0, 10, 40)
    assert axis_positions(base | {t4_move, t4_cmove, t4_undo}, ROW, r0) == {10}
    # Figure 1 ranges
    second_row = ax(4, 0, {1, 2, 3}, "insert", ROW, r1, None, 20)
    second_col = ax(5, 0, {1, 2, 3, 4}, "insert", COL, c1, None, 20)
    spec = (r0, r1, c0, c1)
    add_range = ra(6, 0, {1, 2, 3, 4, 5}, 30, None, spec, {})
    ranged = base | {second_row, second_col, add_range}
    assert range_values(ranged, 30) == {spec} and resolve_range(ranged, spec) == spec
    rm_first = ax(7, 1, {1, 2, 3, 4, 5}, "remove", ROW, r0, 10, None)
    assert resolve_range(ranged | {rm_first}, spec) == (r1, r1, c0, c1)
    cross = ax(7, 1, {1, 2, 3, 4, 5}, "move", ROW, r1, 20, 5)
    assert resolve_range(ranged | {cross}, spec) is None
    third_row = ax(6, 0, {1, 2, 3, 4, 5}, "insert", ROW, r2, None, 30)
    wide = (r0, r2, c0, c1)
    add_wide = ra(7, 0, {1, 2, 3, 4, 5, 6}, 31, None, wide, {})
    wide_base = base | {second_row, second_col, third_row, add_wide}
    rm_interior = ax(8, 1, {1, 2, 3, 4, 5, 6}, "remove", ROW, r1, 20, None)
    s = wide_base | {rm_interior}
    assert resolve_range(s, wide) == (r0, r2, c0, c1) and len(live_axis_ids(s, ROW)) == 2
    rm_range = ra(7, 0, {1, 2, 3, 4, 5, 6}, 30, spec, None, {6})
    re_range = ra(8, 0, {1, 2, 3, 4, 5, 6, 7}, 30, None, spec, {7})
    assert range_values(ranged | {rm_range, re_range}, 30) == {spec}
    print("fixtures: 20 Lean SPOT expectations reproduced by the Python reference")


# ------------------------------------------------- H2 directed witnesses


def h2_witnesses():
    """Range resolution reads a dead endpoint's last position.

    PASS/FAIL pair 1 (single replica): two histories with the same live sheet
    and the same range spec resolve differently because the removed endpoint
    had different last positions.

    PASS/FAIL pair 2 (one merge): re-anchoring a range eagerly at removal time
    disagrees with the reference when a concurrent insert lands between the
    dead endpoint and its successor."""
    r0, r1, r2, c0 = 10, 11, 12, 20
    base = [ax(1, 0, {}, "insert", ROW, r0, None, 10),
            ax(2, 0, {1}, "insert", ROW, r1, None, 20),
            ax(3, 0, {1, 2}, "insert", ROW, r2, None, 30),
            ax(4, 0, {1, 2, 3}, "insert", COL, c0, None, 10),
            ra(5, 0, {1, 2, 3, 4}, 40, None, (r0, r2, c0, c0), {})]
    L = frozenset(base)
    w1 = L | {ax(6, 0, {1, 2, 3, 4, 5}, "remove", ROW, r0, 10, None)}
    w2 = L | {ax(6, 0, {1, 2, 3, 4, 5}, "move", ROW, r0, 10, 25),
              ax(7, 0, {1, 2, 3, 4, 5, 6}, "remove", ROW, r0, 25, None)}
    o1, o2 = observation_ref(w1), observation_ref(w2)
    assert (o1.rows, o1.cols, o1.pos, o1.cells, o1.ranges) == (o2.rows, o2.cols, o2.pos, o2.cells, o2.ranges), \
        "live sheets should coincide"
    res1 = resolve_range(w1, (r0, r2, c0, c0))
    res2 = resolve_range(w2, (r0, r2, c0, c0))
    assert res1 == (r1, r2, c0, c0) and res2 == (r2, r2, c0, c0), (res1, res2)
    print(f"H2 pair 1: same live sheet, range resolves to {res1} vs {res2}: "
          "the dead endpoint's last position is load-bearing (hand-derived, checked by the reference)")
    # pair 2: eager re-anchoring versus a concurrent insert between r0 and r1
    A = L | {ax(6, 1, {1, 2, 3, 4, 5}, "remove", ROW, r0, 10, None)}
    B = L | {ax(7, 2, {1, 2, 3, 4, 5}, "insert", ROW, 13, None, 15)}
    M = A | B
    lazy = resolve_range(M, (r0, r2, c0, c0))
    # eager: at removal time on branch A the successor of r0 (pos 10) is r1
    assert lazy == (13, r2, c0, c0), lazy
    print(f"H2 pair 2: reference resolves to {lazy} after the merge; eager re-anchoring at "
          "removal time would answer (11, 12, 20, 20)")


def h2_pair3():
    """Update-wins revival needs the dead row's last position. Two histories
    on branch A (move then remove; remove only) leave the same live sheet.
    A concurrent write on branch B revives the row in both merges, and the
    reference reports positions 52 and 10 respectively."""
    r0, c0 = 10, 20
    L = frozenset({ax(1, 0, {}, "insert", ROW, r0, None, 10),
                   ax(2, 0, {1}, "insert", COL, c0, None, 10),
                   ce(3, 0, {1, 2}, r0, c0, {}, {0}, {})})
    A1 = L | {ax(4, 1, {1, 2, 3}, "move", ROW, r0, 10, 52),
              ax(5, 1, {1, 2, 3, 4}, "remove", ROW, r0, 52, None)}
    A2 = L | {ax(4, 1, {1, 2, 3}, "remove", ROW, r0, 10, None)}
    B = L | {ce(6, 2, {1, 2, 3}, r0, c0, {0}, {7}, {3})}
    oa1, oa2 = observation_ref(A1), observation_ref(A2)
    assert oa1 == oa2 and not axis_live(A1, ROW, r0), "branch-A live sheets should coincide"
    m1, m2 = A1 | B, A2 | B
    assert axis_live(m1, ROW, r0) and axis_live(m2, ROW, r0)
    p1, p2 = axis_positions(m1, ROW, r0), axis_positions(m2, ROW, r0)
    assert p1 == {52} and p2 == {10}, (p1, p2)
    print(f"H2 pair 3: identical branch-A sheets (row dead); after merging the concurrent write, "
          f"the revived row sits at {p1} vs {p2}: the removed row's last position is load-bearing")


def undo_revival_witness():
    """A causally later removal is undone by undoing an earlier cell write.
    Hand-derived from the Lean definitions; checked against the reference."""
    r0, c0 = 10, 20
    base_row = ax(1, 0, {}, "insert", ROW, r0, None, 10)
    base_col = ax(2, 0, {1}, "insert", COL, c0, None, 10)
    write = ce(3, 0, {1, 2}, r0, c0, {}, {0}, {})
    remove = ax(4, 0, {1, 2, 3}, "remove", ROW, r0, 10, None)
    s = frozenset({base_row, base_col, write, remove})
    assert not axis_live(s, ROW, r0)
    undo = un(5, 0, {1, 2, 3, 4}, write)     # legal: own event, target in seen
    s2 = s | {undo}
    live = axis_live(s2, ROW, r0)
    print(f"undo-revival: row removed at t=4, undo of the t=3 write at t=5 -> row live = {live}, "
          f"position {axis_positions(s2, ROW, r0)}, cell {set(cell_values(s2, r0, c0))}")
    return live


if __name__ == "__main__":
    executions = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    check_fixtures()
    h2_witnesses()
    h2_pair3()
    undo_revival_witness()
    if "--restricted-undo" in sys.argv:
        UNDO_REQUIRES_LIVE_AXES = True
        campaign([Mat("keep", removal="named"), Mat("ranges", removal="named"),
                  Mat("all", removal="named")], executions, seed,
                 "campaign with undo restricted to live axes")
        sys.exit(0)
    designs = [Mat("keep"), Mat("keep", removal="named"), Mat("ranges", removal="named"),
               Mat("all", removal="named"), Mat("keep", binary=True), Mat("ranges", eager=True)]
    for sd in range(seed, seed + 3):
        campaign(designs, executions, sd, "differential DAG campaign")
    growth([Mat("keep", removal="named"), Mat("ranges", removal="named")], seed)
