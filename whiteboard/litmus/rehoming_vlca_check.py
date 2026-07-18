#!/usr/bin/env python3
"""Virtual-LCA soundness probe for the REHOMING RGA (#90 equivalence residue).

The rehoming RGA (Lean: Sal/MRDTs/RGA_Rehoming/RGA_Tombstone_Free_MRDT.lean;
conditioned chain: Sal/ConditionedMRDTs/MRDT_Instances/RGA_Rehoming/; the
'flat-RGA' row of litmus.py) mirrored exactly:

  state    id -> (elem, anchor); 0 = root, never stored; tombstone-free
  ops      ('ins', t, elem, pre, a)   ('del', t, pre, x)
           pre = the leaf's LIVE ancestor chain at the generation state
           (nearest first, root excluded): born accuracy, forced by
           tombstone-freedom
  do       Ins: s[t] = (elem, resolve(s, (a,)+pre))  [nearest live recorded
           ancestor];  Del: tgt = resolve(s, pre); rehome x's children to
           tgt; drop x.  Total; Del of a dead target is the identity.
  merge3   OR-set survival I = (dl&da&db) | (da-dl) | (db-dl); records read
           l-first; stored anchors CLIMBED up the LCA's chain to the nearest
           survivor (RGA_Tombstone_Free_MRDT.lean:147).
  ~=       observational state equality (eq, :172) = dict equality here.

Honesty chain mirrored: born accuracy (HonCore), applicable delivery
(applicable = accurate & fresh_ts, HonestDelivery), Lamport-fresh ids,
GenDisc2C (recorded path accurate at the dependency-prefix fold,
RGA_CanonFoldOK.lean:110), noopFeasible (applicable-or-noop along
enumerations, Framework/NoopFeasible.lean; REFUTED as derivable-from-sigma0,
memory 7a7ff9c: LCA-first enumerations pre-apply concurrent anchor-kills).

Virtual LCAs: recursive antichain merge, ascending rank, exactly the
virtual_lca_check.py rule (whiteboard/virtual-lca-note.md section 2).

Probes (paper companion: whiteboard/rehoming-vlca-probe.md):
  C1  E(virtual) = E(v1) & E(v2) at every resolution (covering).
  C2  scratch canonicity: every scratch (antichain-fold) state equals BOTH
      the datatype's own ts-order fold of its union event set AND an
      implementation-independent birth-forest hand oracle.
  C3  post-sync state = fold oracle = hand oracle; final convergence.
  C4  GenDisc2C empirically at intermediate antichain unions: per event,
      accuracy at the fold of its dependency prefix (and of its full
      causal past) WITHIN the union.
  C5  noopFeasible along ts-order and LCA-first enumerations of the
      unions.  EXPECTED to fail on the directed hEnum shape (a concurrent
      anchor-kill folded below an insert); its firing is a PASSING
      assertion (the refutation reproduced at antichain unions), because
      canonicity (C2) must hold anyway via rehome-correctness.
  P2  antichain fold-order insensitivity (ascending vs descending rank).

Directed: T1 routine criss-cross, delete under a concurrent child (L5/L12
flavor) with a single-pick FAIL companion; T2 nested depth-2 with deletes
at both levels; T3 rows/L4-style symmetric delete-heavy MCAs; T4 the
directed hEnum-at-union shapes (4a ins-anchor-dead, 4b del-path-stale);
T8 a directed 3-antichain whose ascending fold passes a STRICT intermediate
union with the hEnum shape planted inside it.  Randomized: T5 open PBT,
delete-heavy, no criss-cross gate; T6 targeted PBT forcing del/ins MCA
pairs (hEnum firing asserted per trial); T7 dense sync-heavy PBT (nesting
depth >= 2, antichain size >= 3 asserted).  ST: harness-power selftest, a
climb-free mutant merge must be caught.

Expected values in directed tests are hand-derived in the comments, never
taken from the implementation under test.  Exit 0 iff all asserted
expectations hold.
"""

from collections import Counter
import random
import sys

ROOT = 0

# ---------------------------------------------------------------------------
# The rehoming RGA, Lean-faithful.
# ---------------------------------------------------------------------------

def resolve(s, cands):
    """First LIVE candidate, else the root (RGA_Tombstone_Free_MRDT.lean:102)."""
    for c in cands:
        if c in s:
            return c
    return ROOT

def anc_of(s, v):
    """Stored anchor; absent keys read the map default (_, 0), so 0."""
    return s[v][1] if v in s else ROOT

def chain(s, a):
    """a's live ancestor chain in s, nearest first, root excluded."""
    out, v = [], anc_of(s, a)
    while v != ROOT:
        out.append(v)
        v = anc_of(s, v)
    return tuple(out)

def apply_op(s, op):
    """do_ (RGA_Tombstone_Free_MRDT.lean:130).  Total."""
    if op[0] == 'ins':
        _, t, elem, pre, a = op
        s2 = dict(s)
        s2[t] = (elem, resolve(s, (a,) + pre))
        return s2
    _, t, pre, x = op
    tgt = resolve(s, pre)
    return {k: (e, tgt if an == x else an) for k, (e, an) in s.items() if k != x}

def merge3(l, a, b):
    """Three-way merge (RGA_Tombstone_Free_MRDT.lean:147): OR-set survival,
    records read l-first, anchors climbed up the LCA chain to a survivor."""
    I = (set(l) & set(a) & set(b)) | (set(a) - set(l)) | (set(b) - set(l))
    def rec(t):
        for src in (l, a, b):
            if t in src:
                return src[t]
        raise AssertionError(f"survivor {t} in no source")
    def climb(x):
        seen = set()
        while x != ROOT and x not in I:
            assert x not in seen, "climb cycle"
            seen.add(x)
            x = anc_of(l, x)          # the LCA's chain, absent keys -> 0
        return x
    return {t: (rec(t)[0], climb(rec(t)[1])) for t in I}

def read(s):
    """Newer-first sibling DFS from the root (litmus.py FlatRGA.read)."""
    kids = {}
    for t, (_, a) in s.items():
        kids.setdefault(a, []).append(t)
    for a in kids:
        kids[a].sort(reverse=True)
    out = []
    stack = list(kids.get(ROOT, []))
    while stack:
        c = stack.pop(0)
        out.append((c, s[c][0]))
        stack = kids.get(c, []) + stack
    return tuple(out)

# ---------------------------------------------------------------------------
# The honesty-chain predicates, Lean-faithful.
# ---------------------------------------------------------------------------

def is_anc_path(s, leaf, pre):
    """IsAncPath (RGA_Tombstone_Free_MRDT.lean:332): pre is leaf's true
    root-ward chain, every member live, terminating at the root."""
    v = leaf
    for p in pre:
        if anc_of(s, v) != p or p not in s:
            return False
        v = p
    return anc_of(s, v) == ROOT

def op_leaf(op):
    return op[4] if op[0] == 'ins' else op[3]

def accurate(op, s):
    """accurate (:337): recorded path = the true live chain of the leaf."""
    leaf, pre = op_leaf(op), op[3] if op[0] == 'ins' else op[2]
    if leaf == ROOT and pre == ():
        return True
    return leaf in s and is_anc_path(s, leaf, pre)

def fresh_ts(op, s):
    """fresh_ts (:342): an Ins uses a fresh nonzero id; Del creates nothing."""
    return op[1] != ROOT and op[1] not in s if op[0] == 'ins' else True

def applicable(op, s):
    """RGACondSig.applicable = accurate & fresh_ts (RGA_CondSig.lean:307)."""
    return accurate(op, s) and fresh_ts(op, s)

def app_or_noop(op, s):
    """The noopFeasible step clause (Framework/NoopFeasible.lean:24)."""
    return applicable(op, s) or apply_op(s, op) == s

def classify_violation(op, s):
    if op[0] == 'ins':
        a = op[4]
        return 'ins-anchor-dead' if (a != ROOT and a not in s) else 'ins-path-stale'
    return 'del-path-stale' if op[3] in s else 'del-dead-nonnoop'

# ---------------------------------------------------------------------------
# Oracles.  fold_oracle is the datatype's OWN fold (what RA-lin certifies):
# ts order is a causal linearization because ids come from one global
# Lamport counter.  birth_oracle is implementation-independent: it never
# runs apply_op or merge3; rehome-on-delete means each live node hangs from
# its nearest live birth ancestor (hand-derived semantics).
# ---------------------------------------------------------------------------

def fold_oracle(events):
    s = {}
    for op in sorted(events, key=lambda o: o[1]):
        s = apply_op(s, op)
    return s

def birth_oracle(events):
    parent = {op[1]: op[4] for op in events if op[0] == 'ins'}
    elem = {op[1]: op[2] for op in events if op[0] == 'ins'}
    dead = {op[3] for op in events if op[0] == 'del'}
    live = set(parent) - dead
    def near(v):
        while v != ROOT and v not in live:
            v = parent.get(v, ROOT)
        return v
    return {t: (elem[t], near(parent[t])) for t in live}

def birth_anc_ids(events, leaf):
    """leaf plus its birth-forest ancestors (recorded-anchor closure)."""
    parent = {op[1]: op[4] for op in events if op[0] == 'ins'}
    out, v = set(), leaf
    while v != ROOT and v not in out:
        out.add(v)
        v = parent.get(v, ROOT)
    return out

# ---------------------------------------------------------------------------
# Commit DAG + virtual-LCA resolution (structure of virtual_lca_check.py,
# instrumented).  Every op is born at exactly one commit (StoreInv.origin's
# twin), so E(v) = ops along the reflexive ancestor closure.
# ---------------------------------------------------------------------------

class Dag:
    def __init__(self):
        self.parents, self.ops, self.states = {}, {}, {}
        self.next_id = 0

    def add(self, parents, op, state):
        cid = self.next_id
        self.next_id += 1
        self.parents[cid] = tuple(parents)
        self.ops[cid] = op
        self.states[cid] = state
        return cid

    def anc(self, cid):
        seen, stack = set(), [cid]
        while stack:
            u = stack.pop()
            if u not in seen:
                seen.add(u)
                stack.extend(self.parents[u])
        return seen

    def events(self, cid):
        return frozenset(self.ops[u] for u in self.anc(cid)
                         if self.ops[u] is not None)

    def mcas(self, a, b):
        ca = self.anc(a) & self.anc(b)
        nonmax = {p for c in ca for p in self.parents[c] if p in ca}
        return sorted(ca - nonmax)

class Probe:
    """Global instrumentation: C4/C5 verdicts at every scratch union."""
    def __init__(self, gendisc=True):
        self.gendisc = gendisc          # run the (quadratic) C4 probe
        self.noop_viol = Counter()      # C5 kinds, ts-order fold
        self.noop_viol_lca1st = Counter()  # C5 kinds, LCA-first fold
        self.scratches = 0
        self.antichain_sizes = Counter()
        self.res_depths = Counter()
        self.vis = None                 # op,op -> bool (set by Sim)

    def merge_stats_into(self, agg):
        agg.noop_viol.update(self.noop_viol)
        agg.noop_viol_lca1st.update(self.noop_viol_lca1st)
        agg.scratches += self.scratches
        agg.antichain_sizes.update(self.antichain_sizes)
        agg.res_depths.update(self.res_depths)

def noop_probe(events_ordered, counter):
    """Walk the enumeration; record every applicable-nor-noop step."""
    s, viols = {}, []
    for op in events_ordered:
        if not app_or_noop(op, s):
            kind = classify_violation(op, s)
            counter[kind] += 1
            viols.append((op, kind))
        s = apply_op(s, op)
    return s, viols

def check_scratch(dag, cid, inner_lca_events, probe, tag):
    """C2 + C4 + C5 at one scratch node."""
    U = dag.events(cid)
    st = dag.states[cid]
    # C2 canonicity: merge state = own fold = independent hand oracle.
    assert st == fold_oracle(U), \
        f"{tag}: C2 FAIL scratch state != ts-order fold of union"
    assert st == birth_oracle(U), \
        f"{tag}: C2 FAIL scratch state != birth-forest hand oracle"
    # C5 noopFeasible along two enumerations of the union.
    ts_order = sorted(U, key=lambda o: o[1])
    _, v1 = noop_probe(ts_order, probe.noop_viol)
    inter = sorted(inner_lca_events, key=lambda o: o[1])
    delta = sorted(U - inner_lca_events, key=lambda o: o[1])
    _, v2 = noop_probe(inter + delta, probe.noop_viol_lca1st)
    # C4 GenDisc2C empirically: accuracy at the dependency-prefix fold and
    # at the full-causal-past fold, both inside the union.
    if probe.gendisc:
        for op in U:
            aids = birth_anc_ids(U, op_leaf(op)) | {op_leaf(op)}
            dep = [z for z in U if z != op and probe.vis(z, op)
                   and (z[1] in aids if z[0] == 'ins' else z[3] in aids)]
            sdep = fold_oracle(dep)
            assert accurate(op, sdep), \
                f"{tag}: C4 FAIL dep-prefix accuracy for {op} at union"
            past = [z for z in U if z != op and probe.vis(z, op)]
            assert accurate(op, fold_oracle(past)), \
                f"{tag}: C4 FAIL full-past accuracy for {op} at union"
    return v1, v2

def resolve_lca(dag, a, b, probe, depth=0, reverse=False, check=True):
    """Virtual LCA: recursive antichain merge, ascending rank
    (virtual-lca-note.md section 2)."""
    M = dag.mcas(a, b)
    assert M, f"no common ancestor of {a}, {b}"
    if len(M) == 1:
        return M[0]
    probe.antichain_sizes[len(M)] += 1
    probe.res_depths[depth] += 1
    order = sorted(M, reverse=reverse)
    acc = order[0]
    for m in order[1:]:
        l = resolve_lca(dag, acc, m, probe, depth + 1, reverse, check)
        st = merge3(dag.states[l], dag.states[acc], dag.states[m])
        inner_ev = dag.events(l)
        acc = dag.add([acc, m], None, st)
        probe.scratches += 1
        if check:
            check_scratch(dag, acc, inner_ev, probe, f"scratch d{depth}")
    # C1: the covering proposition at every resolution.
    assert dag.events(acc) == dag.events(a) & dag.events(b), \
        "C1 FAIL: E(virtual) != E(v1) & E(v2)"
    return acc

# ---------------------------------------------------------------------------
# Replica simulator: honest head-sync, criss-cross gate REPLACED by virtual
# resolution.  Honest generator: anchors live at mint, recorded paths = the
# live chain at the head state (born accuracy), deletes name observed live
# nodes, ids from one global Lamport counter (fresh, causality-monotone).
# ---------------------------------------------------------------------------

class Sim:
    def __init__(self, nrep, probe=None):
        self.dag = Dag()
        self.root = self.dag.add([], None, {})
        self.heads = {r: self.root for r in range(nrep)}
        self.ts = 0
        self.probe = probe or Probe()
        self.born_at = {}               # op -> birth commit
        self.probe.vis = self.vis
        self.check_p2 = True

    def vis(self, z, o):
        return z != o and self.born_at[z] in self.dag.anc(self.born_at[o])

    def fresh(self):
        self.ts += 1
        return self.ts

    def head_state(self, r):
        return self.dag.states[self.heads[r]]

    def mint_ins(self, r, elem, a):
        s = self.head_state(r)
        assert a == ROOT or a in s, "dishonest mint: dead anchor"
        return ('ins', self.fresh(), elem,
                () if a == ROOT else chain(s, a), a)

    def mint_del(self, r, x):
        s = self.head_state(r)
        assert x in s, "dishonest mint: unobserved delete target"
        return ('del', self.fresh(), chain(s, x), x)

    def commit(self, r, op):
        h = self.heads[r]
        s = self.dag.states[h]
        assert applicable(op, s), "dishonest delivery at mint site"
        self.heads[r] = self.dag.add([h], op, apply_op(s, op))
        self.born_at[op] = self.heads[r]

    def sync(self, r1, r2, check=True):
        a, b = self.heads[r1], self.heads[r2]
        if a == b:
            return
        if a in self.dag.anc(b):
            self.heads[r1] = b
            return
        if b in self.dag.anc(a):
            self.heads[r2] = a
            return
        l = resolve_lca(self.dag, a, b, self.probe, 0, check=check)
        if self.check_p2 and len(self.dag.mcas(a, b)) >= 2:
            l2 = resolve_lca(self.dag, a, b, Probe(gendisc=False), 0,
                             reverse=True, check=False)
            assert self.dag.states[l] == self.dag.states[l2], \
                "P2 FAIL: antichain fold order changed the LCA state"
        st = merge3(self.dag.states[l], self.dag.states[a], self.dag.states[b])
        m = self.dag.add([a, b], None, st)
        self.heads[r1] = self.heads[r2] = m
        if check:
            ev = self.dag.events(m)
            assert st == fold_oracle(ev), "C3 FAIL: sync state != fold oracle"
            assert st == birth_oracle(ev), "C3 FAIL: sync state != hand oracle"
            assert read(st) == read(fold_oracle(ev))

    def sync_all(self):
        rs = sorted(self.heads)
        for r in rs[1:]:
            self.sync(rs[0], r)
        for r in rs[1:]:
            self.sync(r, rs[0])

    def assert_converged(self):
        sts = [self.head_state(r) for r in self.heads]
        assert all(s == sts[0] for s in sts), "convergence FAIL"
        ev = self.dag.events(self.heads[0])
        assert sts[0] == fold_oracle(ev) == birth_oracle(ev), \
            "final oracle FAIL"

# ---------------------------------------------------------------------------
# T1: routine two-pair criss-cross; one head deletes a node whose child was
# inserted concurrently (L5/L12 flavor).  PASS: virtual merge converges to
# the hand value.  FAIL companion: the single-MCA pick v resurrects id 2.
# ---------------------------------------------------------------------------

def t1_routine():
    sim = Sim(4)
    A, B, C, D = range(4)
    sim.commit(A, sim.mint_ins(A, 'a', 0))        # ts1, id 1 at root
    sim.sync_all()
    sim.commit(A, sim.mint_ins(A, 'b', 1))        # ts2, id 2 under 1 -> u
    sim.commit(B, sim.mint_del(B, 1))             # ts3, delete 1     -> v
    u, v = sim.heads[A], sim.heads[B]
    sim.sync(C, A); sim.sync(D, B)                # fast-forwards
    sim.sync(A, B); sim.sync(C, D)                # rival merges m1, m2
    # Hand: m1 = m2 = {2:(b,0)} (2 climbs its dead parent 1 to the root).
    assert sim.head_state(A) == {2: ('b', 0)}
    sim.commit(A, sim.mint_ins(A, 'c', 2))        # ts4, id 4 under 2
    sim.commit(C, sim.mint_del(C, 2))             # ts5, delete 2
    ha, hc = sim.heads[A], sim.heads[C]
    assert sim.dag.mcas(ha, hc) == sorted([u, v])
    # FAIL companion first: fixed single-MCA picks as the LCA slot.
    sa, sc = sim.dag.states[ha], sim.dag.states[hc]
    pick_v = merge3(sim.dag.states[v], sa, sc)
    assert read(pick_v) == ((2, 'b'), (4, 'c')), \
        f"T1F: pick-v gave {read(pick_v)}"       # hand: resurrects 2
    assert read(pick_v) != read(fold_oracle(sim.dag.events(ha)
                                            | sim.dag.events(hc)))
    before = sim.probe.antichain_sizes.total()
    sim.sync(A, C)                                # the criss-cross
    assert sim.probe.antichain_sizes.total() > before, "T1: no resolution"
    sim.sync_all()
    sim.assert_converged()
    got = read(sim.head_state(0))
    assert got == ((4, 'c'),), f"T1: read {got}"  # hand-derived
    return ("T1  routine criss-cross (del under concurrent child): "
            "converged to hand value ((4,c)); single-pick v resurrects 2")

# ---------------------------------------------------------------------------
# T2: NESTED depth-2 criss-cross with deletes at both levels.
# ---------------------------------------------------------------------------

def t2_nested():
    sim = Sim(8)
    A, B, C, D, E, F, G, H = range(8)
    sim.commit(A, sim.mint_ins(A, 'a', 0))        # ts1
    sim.commit(A, sim.mint_ins(A, 'b', 1))        # ts2, under 1
    sim.sync_all()
    sim.commit(A, sim.mint_ins(A, 'c', 2))        # ts3, under 2 -> u
    sim.commit(B, sim.mint_del(B, 2))             # ts4           -> v
    sim.sync(C, A); sim.sync(D, B)
    sim.sync(A, B); sim.sync(C, D)                # rivals m1, m2
    # Hand: m1 = {1:(a,0), 3:(c,1)} (3 climbs dead 2 to 1).
    assert sim.head_state(A) == {1: ('a', 0), 3: ('c', 1)}
    sim.sync(E, A); sim.sync(F, C)
    sim.sync(E, F)                                # n1 (resolves {u,v})
    sim.sync(G, B); sim.sync(H, D)
    sim.sync(G, H)                                # n2, rival of n1
    sim.commit(E, sim.mint_ins(E, 'd', 3))        # ts5, under 3 -> n1'
    sim.commit(G, sim.mint_del(G, 1))             # ts6           -> n2'
    d_before = dict(sim.probe.res_depths)
    sim.sync(E, G)                                # depth-2 criss-cross
    assert sim.probe.res_depths.get(0, 0) > d_before.get(0, 0)
    assert sim.probe.res_depths.get(1, 0) > d_before.get(1, 0), \
        "T2: nested resolution (recursion depth 2) not exercised"
    sim.sync_all()
    sim.assert_converged()
    got = read(sim.head_state(0))
    assert got == ((3, 'c'), (5, 'd')), f"T2: read {got}"  # hand-derived
    return ("T2  nested depth-2 criss-cross with deletes: converged to "
            "hand value ((3,c),(5,d)); nested resolution exercised")

# ---------------------------------------------------------------------------
# T3: rows/L4-style symmetric shape: EACH branch deletes a node whose
# children are inserted concurrently on the other branch (the rehoming
# datatype's sore spot), then delete-heavy continuations.
# ---------------------------------------------------------------------------

def t3_rows():
    sim = Sim(4)
    A, B, C, D = range(4)
    sim.commit(A, sim.mint_ins(A, 'a', 0))        # ts1
    sim.commit(A, sim.mint_ins(A, 'b', 0))        # ts2
    sim.sync_all()
    sim.commit(A, sim.mint_ins(A, 'c', 1))        # ts3, child of 1
    sim.commit(A, sim.mint_del(A, 2))             # ts4              -> u
    sim.commit(B, sim.mint_ins(B, 'd', 2))        # ts5, child of 2 (dead in u)
    sim.commit(B, sim.mint_del(B, 1))             # ts6              -> v
    u, v = sim.heads[A], sim.heads[B]
    sim.sync(C, A); sim.sync(D, B)
    sim.sync(A, B); sim.sync(C, D)                # rivals
    # Hand: both orphans climb to the root: {3:(c,0), 5:(d,0)}.
    assert sim.head_state(A) == {3: ('c', 0), 5: ('d', 0)}
    sim.commit(A, sim.mint_del(A, 3))             # ts7
    sim.commit(C, sim.mint_ins(C, 'e', 5))        # ts8, child of 5
    viol_before = sim.probe.noop_viol.total()
    sim.sync(A, C)                                # criss-cross on {u,v}
    sim.sync_all()
    sim.assert_converged()
    got = read(sim.head_state(0))
    assert got == ((5, 'd'), (8, 'e')), f"T3: read {got}"  # hand-derived
    # The union fold already trips noopFeasible here (ins 5 under dead 2).
    assert sim.probe.noop_viol.total() > viol_before, \
        "T3: expected a noopFeasible violation at the union"
    return ("T3  rows/L4 symmetric deletes-with-concurrent-children: "
            "converged to hand value ((5,d),(8,e)); union fold already "
            "trips noopFeasible (expected)")

# ---------------------------------------------------------------------------
# T4: the DIRECTED hEnum shapes at an antichain union.  4a: one MCA holds
# del 2, the other an insert anchored at 2 with a LARGER Lamport ts; every
# ts-respecting enumeration of the union folds the kill below the insert,
# so noopFeasible FAILS (ins-anchor-dead) while canonicity (C2) holds via
# rehome-correctness.  4b: the del-path-stale variant.
# ---------------------------------------------------------------------------

def t4a_henum_ins():
    sim = Sim(4)
    A, B, C, D = range(4)
    sim.commit(A, sim.mint_ins(A, 'a', 0))        # ts1
    sim.commit(A, sim.mint_ins(A, 'b', 1))        # ts2, under 1
    sim.sync_all()
    sim.commit(B, sim.mint_del(B, 2))             # ts3: the kill    -> v
    sim.commit(A, sim.mint_ins(A, 'x', 2))        # ts4: ins under 2 -> u
    sim.sync(C, A); sim.sync(D, B)
    sim.sync(A, B); sim.sync(C, D)                # rivals
    # Hand: 4 climbs dead 2 to 1: {1:(a,0), 4:(x,1)}.
    assert sim.head_state(A) == {1: ('a', 0), 4: ('x', 1)}
    sim.commit(A, sim.mint_ins(A, 'y', 4))        # ts5
    sim.commit(C, sim.mint_del(C, 4))             # ts6
    v_ts = dict(sim.probe.noop_viol)
    v_lca = dict(sim.probe.noop_viol_lca1st)
    sim.sync(A, C)                                # criss-cross on {u,v}
    fired_ts = sim.probe.noop_viol['ins-anchor-dead'] \
        - v_ts.get('ins-anchor-dead', 0)
    fired_lca = sim.probe.noop_viol_lca1st['ins-anchor-dead'] \
        - v_lca.get('ins-anchor-dead', 0)
    assert fired_ts >= 1, "T4a: hEnum shape did NOT fire on ts-order fold"
    assert fired_lca >= 1, "T4a: hEnum shape did NOT fire on LCA-first fold"
    sim.sync_all()
    sim.assert_converged()
    got = read(sim.head_state(0))
    assert got == ((1, 'a'), (5, 'y')), f"T4a: read {got}"  # hand-derived
    return ("T4a hEnum-at-union (concurrent anchor-kill below an insert): "
            "noopFeasible FAILED on both enumerations of the union "
            "(EXPECTED, the 7a7ff9c refutation reproduced at antichain "
            "unions); canonicity + convergence held via rehome-correctness")

def t4b_henum_del():
    sim = Sim(4)
    A, B, C, D = range(4)
    sim.commit(A, sim.mint_ins(A, 'a', 0))        # ts1
    sim.commit(A, sim.mint_ins(A, 'b', 1))        # ts2
    sim.commit(A, sim.mint_ins(A, 'c', 2))        # ts3, chain 3->2->1
    sim.sync_all()
    sim.commit(B, sim.mint_del(B, 2))             # ts4: kills 3's parent -> v
    sim.commit(A, sim.mint_del(A, 3))             # ts5: pre=(2,1) stale  -> u
    sim.sync(C, A); sim.sync(D, B)
    sim.sync(A, B); sim.sync(C, D)
    assert sim.head_state(A) == {1: ('a', 0)}     # hand
    sim.commit(A, sim.mint_ins(A, 'z', 1))        # ts6
    sim.commit(C, sim.mint_ins(C, 'w', 0))        # ts7
    v_ts = dict(sim.probe.noop_viol)
    sim.sync(A, C)
    fired = sim.probe.noop_viol['del-path-stale'] \
        - v_ts.get('del-path-stale', 0)
    assert fired >= 1, "T4b: del-path-stale did NOT fire at the union"
    sim.sync_all()
    sim.assert_converged()
    got = read(sim.head_state(0))
    assert got == ((7, 'w'), (1, 'a'), (6, 'z')), f"T4b: read {got}"  # hand
    return ("T4b hEnum-at-union (delete with stale recorded path): "
            "noopFeasible FAILED (del applied, accuracy false) yet the "
            "recorded path resolved to the right rehome target; "
            "canonicity + convergence held")

# ---------------------------------------------------------------------------
# T5: open randomized DAG PBT, delete-heavy, criss-cross gate removed.
# Every sync asserts C1/C2/C3/C5-well-formedness (and C4 on a slice); the
# trial asserts final convergence + both oracles.
# ---------------------------------------------------------------------------

def random_op(sim, rng, r):
    live = sorted(sim.head_state(r))
    if live and rng.random() < 0.45:
        return sim.mint_del(r, rng.choice(live))
    a = rng.choice([ROOT] + live)
    return sim.mint_ins(r, 'e', a)

def t5_pbt(ntrials=320, gendisc_trials=60):
    agg, cc_trials = Probe(gendisc=False), 0
    for trial in range(ntrials):
        rng = random.Random(trial * 7919 + 13)
        probe = Probe(gendisc=(trial < gendisc_trials))
        sim = Sim(rng.randint(3, 5), probe)
        for _ in range(rng.randint(25, 45)):
            if rng.random() < 0.55:
                r = rng.randrange(len(sim.heads))
                sim.commit(r, random_op(sim, rng, r))
            else:
                i, j = rng.sample(range(len(sim.heads)), 2)
                sim.sync(i, j)
        sim.sync_all()
        sim.assert_converged()
        if probe.antichain_sizes:
            cc_trials += 1
        probe.merge_stats_into(agg)
    return (f"T5  open PBT: {ntrials} trials (delete-heavy, no gate) "
            f"converged, all reads = both oracles; criss-cross in "
            f"{cc_trials}/{ntrials}; antichain sizes "
            f"{dict(sorted(agg.antichain_sizes.items()))}; resolution "
            f"depths {dict(sorted(agg.res_depths.items()))}; C4 full on "
            f"first {gendisc_trials}; noopFeasible violations at unions "
            f"(EXPECTED, counted not fatal): ts-order "
            f"{dict(agg.noop_viol)}, LCA-first "
            f"{dict(agg.noop_viol_lca1st)}", agg)

# ---------------------------------------------------------------------------
# T6: targeted PBT: every trial FORCES the T4a shape (one MCA deletes n,
# the other inserts under n with a larger ts) on a random base tree with
# random continuations.  The hEnum firing is asserted PER TRIAL; so are
# canonicity, convergence, and both oracles.
# ---------------------------------------------------------------------------

def t6_targeted(ntrials=150, gendisc_trials=40):
    agg = Probe(gendisc=False)
    for trial in range(ntrials):
        rng = random.Random(trial * 104729 + 7)
        probe = Probe(gendisc=(trial < gendisc_trials))
        sim = Sim(4, probe)
        A, B, C, D = range(4)
        for _ in range(rng.randint(4, 7)):
            s = sim.head_state(A)
            sim.commit(A, sim.mint_ins(A, 'b', rng.choice([ROOT] + sorted(s))))
        sim.sync_all()
        n = rng.choice(sorted(sim.head_state(A)))
        sim.commit(A, sim.mint_del(A, n))          # the kill, smaller ts
        sim.commit(B, sim.mint_ins(B, 'y', n))     # concurrent ins under n
        for r in (A, B):
            for _ in range(rng.randint(0, 2)):
                sim.commit(r, random_op(sim, rng, r))
        sim.sync(C, A); sim.sync(D, B)
        sim.sync(A, B); sim.sync(C, D)             # rival merges
        for r in (A, C):
            for _ in range(rng.randint(1, 2)):
                sim.commit(r, random_op(sim, rng, r))
        before = sum(probe.noop_viol.values())
        sim.sync(A, C)                             # criss-cross on {u,v}
        assert sum(probe.noop_viol.values()) > before, \
            f"T6 trial {trial}: forced hEnum shape did not fire"
        sim.sync_all()
        sim.assert_converged()
        probe.merge_stats_into(agg)
    return (f"T6  targeted PBT: {ntrials}/{ntrials} trials fired the hEnum "
            f"shape at the union (asserted per trial) AND converged to both "
            f"oracles; violations: ts-order {dict(agg.noop_viol)}, "
            f"LCA-first {dict(agg.noop_viol_lca1st)}", agg)

# ---------------------------------------------------------------------------
# T8: a DIRECTED 3-antichain.  Heads h1' = ((u+v)+w)+op and h2' = ((v+w)+u)+op
# share MCAs {v, u, w}; the ascending-rank fold passes through the STRICT
# intermediate union E(v) u E(u) (neither a head event set nor the meet: the
# honest per-datatype residue of virtual-lca-note.md section 5), and the
# hEnum shape is planted INSIDE it (del 2 at ts3 below ins-under-2 at ts4).
# All hand values derived in the comments.
# ---------------------------------------------------------------------------

def t8_antichain3():
    sim = Sim(6)
    A, B, C, D, E, F = range(6)
    sim.commit(A, sim.mint_ins(A, 'a', 0))        # ts1
    sim.commit(A, sim.mint_ins(A, 'b', 1))        # ts2, under 1
    sim.sync_all()                                # base {1:(a,0),2:(b,1)}
    sim.commit(B, sim.mint_del(B, 2))             # ts3            -> v
    sim.commit(A, sim.mint_ins(A, 'c', 2))        # ts4, id 4 under 2 -> u
    sim.commit(C, sim.mint_ins(C, 'e', 2))        # ts5, id 5 under 2
    sim.commit(C, sim.mint_del(C, 1))             # ts6            -> w
    sim.sync(D, A); sim.sync(E, B); sim.sync(F, C)   # ff copies of u, v, w
    sim.sync(A, B)                                # m1 = (u+v): {1:(a,0),4:(c,1)}
    assert sim.head_state(A) == {1: ('a', 0), 4: ('c', 1)}
    sim.sync(A, C)                                # h1 = m1+w
    assert sim.head_state(A) == {4: ('c', 0), 5: ('e', 0)}   # hand
    sim.sync(E, F)                                # m2 = (v+w): {5:(e,0)}
    assert sim.head_state(E) == {5: ('e', 0)}
    sim.sync(E, D)                                # h2 = m2+u
    assert sim.head_state(E) == {4: ('c', 0), 5: ('e', 0)}   # hand
    sim.commit(A, sim.mint_ins(A, 'f', 4))        # ts7, id 7 -> h1'
    sim.commit(E, sim.mint_del(E, 5))             # ts8       -> h2'
    assert len(sim.dag.mcas(sim.heads[A], sim.heads[E])) == 3
    s_before = dict(sim.probe.antichain_sizes)
    v_before = dict(sim.probe.noop_viol)
    sim.sync(A, E)                                # the 3-antichain resolution
    assert sim.probe.antichain_sizes[3] > s_before.get(3, 0)
    assert sim.probe.noop_viol['ins-anchor-dead'] \
        > v_before.get('ins-anchor-dead', 0), \
        "T8: hEnum shape did not fire inside the strict intermediate union"
    sim.sync_all()
    sim.assert_converged()
    got = read(sim.head_state(0))
    assert got == ((4, 'c'), (7, 'f')), f"T8: read {got}"    # hand-derived
    return ("T8  directed 3-antichain: ascending fold passed the strict "
            "intermediate union E(v)+E(u) with the hEnum shape planted in "
            "it (fired, expected); canonicity held there; converged to "
            "hand value ((4,c),(7,f)); P2 asc/desc agreed with "
            "order-DEPENDENT intermediates")

# ---------------------------------------------------------------------------
# T7: DENSE PBT (6 replicas, sync-heavy) to force antichain sizes >= 3 and
# resolution nesting depth >= 2 (rivalry of rival joins), all checks on.
# ---------------------------------------------------------------------------

def t7_dense(ntrials=120, gendisc_trials=120):
    agg = Probe(gendisc=False)
    for trial in range(ntrials):
        rng = random.Random(trial * 31337 + 5)
        probe = Probe(gendisc=(trial < gendisc_trials))
        sim = Sim(6, probe)
        for _ in range(rng.randint(50, 80)):
            if rng.random() < 0.38:
                r = rng.randrange(6)
                sim.commit(r, random_op(sim, rng, r))
            else:
                i, j = rng.sample(range(6), 2)
                sim.sync(i, j)
        sim.sync_all()
        sim.assert_converged()
        probe.merge_stats_into(agg)
    assert max(agg.antichain_sizes) >= 3, \
        "T7: dense PBT never produced an antichain of size >= 3"
    assert max(agg.res_depths) >= 2, \
        "T7: dense PBT never nested resolutions to depth >= 2"
    return (f"T7  dense PBT: {ntrials} trials (6 replicas, sync-heavy) "
            f"converged; antichain sizes "
            f"{dict(sorted(agg.antichain_sizes.items()))}; resolution depths "
            f"{dict(sorted(agg.res_depths.items()))}; C4 full on all; "
            f"noopFeasible violations (EXPECTED): ts-order "
            f"{dict(agg.noop_viol)}, LCA-first {dict(agg.noop_viol_lca1st)}",
            agg)

# ---------------------------------------------------------------------------
# Harness-power selftest: a MUTANT merge (climb dropped: stored anchors kept
# raw) must be CAUGHT by the canonicity/oracle assertions.  Guards against a
# vacuously-passing harness.
# ---------------------------------------------------------------------------

def selftest_mutant_caught():
    good = merge3
    def merge3_noclimb(l, a, b):
        I = (set(l) & set(a) & set(b)) | (set(a) - set(l)) | (set(b) - set(l))
        def rec(t):
            for src in (l, a, b):
                if t in src:
                    return src[t]
        return {t: rec(t) for t in I}
    globals()['merge3'] = merge3_noclimb
    caught = False
    try:
        t3_rows()
    except AssertionError:
        caught = True
    finally:
        globals()['merge3'] = good
    assert caught, "SELFTEST FAIL: climb-free mutant merge went undetected"
    return "ST  selftest: the climb-free mutant merge IS caught (harness has teeth)"

def main():
    r1 = t1_routine()
    r2 = t2_nested()
    r3 = t3_rows()
    r4a = t4a_henum_ins()
    r4b = t4b_henum_del()
    r8 = t8_antichain3()
    r5, agg5 = t5_pbt(gendisc_trials=320)
    r6, agg6 = t6_targeted(gendisc_trials=150)
    r7, agg7 = t7_dense()
    rst = selftest_mutant_caught()
    for r in (r1, r2, r3, r4a, r4b, r8, r5, r6, r7, rst):
        print(r)
    print()
    print("VERDICT: SURVIVES (on all probes).")
    print("  C1 covering, C2 scratch canonicity (fold + independent birth")
    print("  oracle), C3 convergence/oracles, C4 GenDisc2C at unions, P2")
    print("  fold-order insensitivity: asserted at every resolution, never")
    print("  failed.")
    print("  C5 noopFeasible at antichain unions: REFUTED AGAIN, as")
    print("  expected (the hEnum shape fires under every ts-respecting")
    print("  enumeration once a concurrent anchor-kill has a smaller")
    print("  Lamport stamp than a cross-branch insert); firings:")
    print(f"    open PBT      ts-order {dict(agg5.noop_viol)} "
          f"LCA-first {dict(agg5.noop_viol_lca1st)}")
    print(f"    targeted PBT  ts-order {dict(agg6.noop_viol)} "
          f"LCA-first {dict(agg6.noop_viol_lca1st)}")
    print(f"    dense PBT     ts-order {dict(agg7.noop_viol)} "
          f"LCA-first {dict(agg7.noop_viol_lca1st)}")
    print("  The Lean mirrors must therefore take the GenDisc2C/K1 route")
    print("  at intermediate antichain unions, not a noopFeasible route.")
    print("ALL CHECKS PASSED")

if __name__ == '__main__':
    main()
