#!/usr/bin/env python3
"""Virtual-LCA (recursive merge) validation. Task #90, design phase.

A commit-DAG simulator with git-recursive-style virtual LCAs, run over two
MRDTs: the embed RGA (immutable chain coordinates, delete = pure removal,
live-set merge; minimal port of runtime/src/datatypes/embedRGA.js /
whiteboard/litmus/embed_tree.py semantics) and the OR-set.

Checks (paper companion: whiteboard/virtual-lca-note.md):
  P1  E(virtual) = E(v1) & E(v2), asserted at EVERY virtual resolution
      (the covering proposition: the union of the maximal common
      ancestors' event sets is exactly the head intersection).
  P2  antichain fold-order insensitivity (ascending vs descending rank),
      asserted at every head sync that resolves a criss-cross.
  T1  the runtime's routine criss-cross shape (two replica pairs merging
      the same diverged heads, then cross-syncing) converges; reads equal
      across all replicas after full sync; embed matches the fold oracle.
  T1F FAIL companion: picking a SINGLE maximal common ancestor as the LCA
      (any fixed pick) resurrects a deleted element on a directed shape;
      the virtual LCA does not.
  T2  randomized honest head-sync WITHOUT the criss-cross gate: 500+
      trials, 3-5 replicas; convergence after a final all-pairs round and
      a full-history fold-oracle match at every merge (embed and OR-set).
  T3  directed NESTED criss-cross: a criss-cross among the antichain
      members themselves; recursion depth >= 2 exercised.
  T4  antichain-size / recursion-depth statistics (directed + randomized).
  T5  keep-set check: the runtime's one-layer MCA seed set (gc.js) prunes
      the versions a depth-2 virtual merge needs (FAIL demonstrated); the
      mcas-closure seed set retains them (PASS demonstrated).

Expected values in directed tests are hand-derived, never taken from the
implementation under test.
"""

from collections import Counter
import random

# ---------------------------------------------------------------------------
# Commit DAG. A commit is (parents, op); op None for root/merge commits.
# Event sets are implicit in ancestry (as in runtime/src/dag.js): every op
# is born at exactly one commit, so E(v) = ops along the reflexive ancestor
# closure, and unique origin holds by construction (StoreInv.origin's twin).
# ---------------------------------------------------------------------------

class PrunedError(Exception):
    pass

class Dag:
    def __init__(self):
        self.parents = {}   # id -> tuple of parent ids
        self.ops = {}       # id -> op or None
        self.states = {}    # id -> state payload; None once pruned
        self.next_id = 0

    def add(self, parents, op, state):
        cid = self.next_id
        self.next_id += 1
        self.parents[cid] = tuple(parents)
        self.ops[cid] = op
        self.states[cid] = state
        return cid

    def state(self, cid):
        st = self.states[cid]
        if st is None:
            raise PrunedError(f"state of commit {cid} was pruned")
        return st

    def anc(self, cid):
        """Reflexive ancestor closure (skeleton is never pruned,
        matching GC_Safety.dropVer: payload dropped, parents kept)."""
        seen, stack = set(), [cid]
        while stack:
            u = stack.pop()
            if u in seen:
                continue
            seen.add(u)
            stack.extend(self.parents[u])
        return seen

    def events(self, cid):
        return frozenset(self.ops[u] for u in self.anc(cid)
                         if self.ops[u] is not None)

    def mcas(self, a, b):
        """All maximal common ancestors (runtime/src/lca.js mcas):
        CA is downward closed, so a member is non-maximal iff some member
        lists it as an immediate parent."""
        ca = self.anc(a) & self.anc(b)
        nonmax = set()
        for c in ca:
            for p in self.parents[c]:
                if p in ca:
                    nonmax.add(p)
        return sorted(ca - nonmax)

    def descendants_of(self, seeds):
        """Reflexive upward closure of a seed set (gc.js Keep shape)."""
        children = {}
        for c, ps in self.parents.items():
            for p in ps:
                children.setdefault(p, []).append(c)
        seen, stack = set(), list(seeds)
        while stack:
            u = stack.pop()
            if u in seen:
                continue
            seen.add(u)
            stack.extend(children.get(u, []))
        return seen

# ---------------------------------------------------------------------------
# Virtual-LCA resolution: recursive merge of the MCA antichain, folded in
# ascending commit-rank order (canonical, deterministic). Scratch merge
# commits are materialized in the DAG (parents = the merged pair) so that
# nested mcas queries work; nothing ever references them, so they are never
# ancestors of real heads and cannot pollute later head queries.
# ---------------------------------------------------------------------------

class Stats:
    def __init__(self):
        self.antichain_sizes = Counter()   # |M| at resolutions with |M|>=2
        self.res_depths = Counter()        # nesting depth of those (0-based)
        self.reads = set()                 # real commit ids whose state is read

    def merge_with(self, other):
        self.antichain_sizes.update(other.antichain_sizes)
        self.res_depths.update(other.res_depths)

def resolve_lca(dag, dt, a, b, stats, depth=0, reverse=False):
    """Commit id of the (possibly virtual) LCA of a and b."""
    M = dag.mcas(a, b)
    assert M, f"no common ancestor of {a}, {b}"
    if len(M) == 1:
        stats.reads.add(M[0])
        return M[0]
    stats.antichain_sizes[len(M)] += 1
    stats.res_depths[depth] += 1
    stats.reads.update(M)
    order = sorted(M, reverse=reverse)
    acc = order[0]
    for m in order[1:]:
        acc = merge_pair(dag, dt, acc, m, stats, depth + 1, reverse)
    # P1: the covering proposition, checked at every resolution.
    assert dag.events(acc) == dag.events(a) & dag.events(b), (
        f"P1 FAIL: E(virtual) != E({a}) & E({b})")
    return acc

def merge_pair(dag, dt, a, b, stats, depth, reverse=False):
    l = resolve_lca(dag, dt, a, b, stats, depth, reverse)
    st = dt.merge3(dag.state(l), dag.state(a), dag.state(b))
    return dag.add([a, b], None, st)

# ---------------------------------------------------------------------------
# Replicas with head-sync by construction (runtime/src/runtime.js shape),
# except the criss-cross gate is REPLACED by virtual-LCA resolution.
# ---------------------------------------------------------------------------

class Sim:
    def __init__(self, dt, nrep):
        self.dag = Dag()
        self.dt = dt
        self.root = self.dag.add([], None, dt.init())
        self.heads = {r: self.root for r in range(nrep)}
        self.stats = Stats()
        self.ts = 0
        self.check_p2 = True

    def fresh_ts(self):
        self.ts += 1
        return self.ts

    def head_state(self, r):
        return self.dag.state(self.heads[r])

    def commit(self, r, op):
        h = self.heads[r]
        st = self.dt.apply(self.dag.state(h), op)
        self.heads[r] = self.dag.add([h], op, st)

    def sync(self, r1, r2):
        a, b = self.heads[r1], self.heads[r2]
        if a == b:
            return
        if a in self.dag.anc(b):        # b subsumes a: fast-forward
            self.heads[r1] = b
            return
        if b in self.dag.anc(a):
            self.heads[r2] = a
            return
        l = resolve_lca(self.dag, self.dt, a, b, self.stats, 0)
        if self.check_p2 and len(self.dag.mcas(a, b)) >= 2:
            l2 = resolve_lca(self.dag, self.dt, a, b, Stats(), 0, reverse=True)
            fa, fb = self.dt.fp(self.dag.state(l)), self.dt.fp(self.dag.state(l2))
            assert fa == fb, "P2 FAIL: antichain fold order changed the LCA state"
        st = self.dt.merge3(self.dag.state(l), self.dag.state(a),
                            self.dag.state(b))
        m = self.dag.add([a, b], None, st)
        self.heads[r1] = self.heads[r2] = m

    def sync_all(self):
        """Two passes: r0 joins everyone, then everyone fast-forwards."""
        rs = sorted(self.heads)
        for r in rs[1:]:
            self.sync(rs[0], r)
        for r in rs[1:]:
            self.sync(r, rs[0])

# ---------------------------------------------------------------------------
# Datatype 1: the embed RGA. State: dict id -> (elem, coord). Coordinates
# are immutable chains coord(anchor) + enc(ts - anchor_ts), unary code
# (order-preserving prefix-free; reads are code-invariant). Delete = pure
# removal. Display: descending lexicographic on coord + '2' sentinel
# (anchor above its descendants, newer sibling first).
# Ops (hashable, globally unique by ts):
#   ('ins', ts, elem, anchor_ts, coord)   -- coord carried, Lean-style pi
#   ('del', ts, target_ts)
# ---------------------------------------------------------------------------

def enc(d):
    assert d >= 1
    return '1' * d + '0'

class EmbedRGA:
    name = 'embedRGA'

    def init(self):
        return {}

    def fp(self, s):
        return frozenset(s.items())

    def apply(self, s, op):
        s = dict(s)
        if op[0] == 'ins':
            _, ts, elem, anchor, coord = op
            if anchor == 0:
                acoord = ''
            else:
                assert anchor in s, f"insert under dead anchor {anchor}"
                acoord = s[anchor][1]
            assert coord == acoord + enc(ts - anchor), "inaccurate ins op"
            s[ts] = (elem, coord)
        else:
            _, _, target = op
            s.pop(target, None)
        return s

    def merge3(self, l, a, b):
        surv = (set(a) & set(b)) | (set(a) - set(l)) | (set(b) - set(l))
        out = {}
        for t in surv:
            recs = [src[t] for src in (a, b, l) if t in src]
            assert all(r == recs[0] for r in recs), "record divergence"
            out[t] = recs[0]
        return out

    def read(self, s):
        key = lambda t: (s[t][1] + '2', t)
        return tuple((t, s[t][0]) for t in sorted(s, key=key, reverse=True))

    def oracle(self, events):
        """Full-history fold: state determined by the event set alone."""
        s = {}
        for op in sorted((o for o in events if o[0] == 'ins'),
                         key=lambda o: o[1]):
            _, ts, elem, _, coord = op
            s[ts] = (elem, coord)
        for op in events:
            if op[0] == 'del':
                s.pop(op[2], None)
        return self.read(s)

# ---------------------------------------------------------------------------
# Datatype 2: the OR-set. State: frozenset of (tag, elem); tag = birth ts.
# Ops: ('add', ts, elem)   ('rem', ts, elem, frozenset_of_observed_tags)
# ---------------------------------------------------------------------------

class ORSet:
    name = 'orset'

    def init(self):
        return frozenset()

    def fp(self, s):
        return s

    def apply(self, s, op):
        if op[0] == 'add':
            _, ts, e = op
            return s | {(ts, e)}
        _, _, e, observed = op
        return s - {(t, e) for t in observed}

    def merge3(self, l, a, b):
        return (a & b) | (a - l) | (b - l)

    def read(self, s):
        return frozenset(e for _, e in s)

    def oracle(self, events):
        adds = {(op[1], op[2]) for op in events if op[0] == 'add'}
        removed = {(t, op[2]) for op in events if op[0] == 'rem'
                   for t in op[3]}
        return self.read(frozenset(adds - removed))

# ---------------------------------------------------------------------------
# Directed test T1: the runtime's routine criss-cross shape.
# Replicas A,B,C,D. A,B diverge at heads x,y; pairs (A,B) and (C,D) build
# rival merges m1, m2 of the same {x, y}; each side commits once more; the
# cross sync finds MCAs {x, y} and must resolve them virtually.
# ---------------------------------------------------------------------------

def ins_op(sim, r, elem, anchor):
    ts = sim.fresh_ts()
    acoord = '' if anchor == 0 else sim.head_state(r)[anchor][1]
    return ('ins', ts, elem, anchor, acoord + enc(ts - anchor))

def t1_embed():
    dt = EmbedRGA()
    sim = Sim(dt, 4)
    A, B, C, D = range(4)
    sim.commit(A, ins_op(sim, A, 'p', 0))          # ts 1
    sim.sync_all()
    sim.commit(A, ins_op(sim, A, 'q', 1))          # ts 2, under p -> head x
    sim.commit(B, ins_op(sim, B, 'r', 0))          # ts 3 -> head y
    sim.sync(C, A)                                  # ff C -> x
    sim.sync(D, B)                                  # ff D -> y
    sim.sync(A, B)                                  # m1 = merge{x,y}
    sim.sync(C, D)                                  # m2 = rival merge{x,y}
    sim.commit(A, ins_op(sim, A, 's', 2))          # ts 4, under q
    sim.commit(C, ('del', sim.fresh_ts(), 3))      # ts 5, delete r
    sim.sync(A, C)                                  # criss-cross: MCAs {x,y}
    assert sim.stats.antichain_sizes[2] >= 1, "T1: no criss-cross resolved"
    sim.sync_all()
    # Hand-derived: p='10', q='1010', s='1010110' (r deleted). Descending
    # sentinel order: p > q > s.
    expect = ((1, 'p'), (2, 'q'), (4, 's'))
    for r in range(4):
        assert dt.read(sim.head_state(r)) == expect, \
            f"T1 embed: replica {r} read {dt.read(sim.head_state(r))}"
        assert dt.read(sim.head_state(r)) == \
            dt.oracle(sim.dag.events(sim.heads[r])), "T1 embed: oracle mismatch"
    return "T1  embed routine criss-cross: converged, reads = hand value = oracle"

def t1_orset():
    dt = ORSet()
    sim = Sim(dt, 4)
    A, B, C, D = range(4)
    sim.commit(A, ('add', sim.fresh_ts(), 'a'))
    sim.sync_all()
    sim.commit(A, ('add', sim.fresh_ts(), 'x'))    # tag 2 -> head x
    sim.commit(B, ('add', sim.fresh_ts(), 'y'))    # tag 3 -> head y
    sim.sync(C, A); sim.sync(D, B)
    sim.sync(A, B); sim.sync(C, D)                 # rival merges
    sim.commit(A, ('rem', sim.fresh_ts(), 'x', frozenset({2})))
    sim.commit(C, ('rem', sim.fresh_ts(), 'y', frozenset({3})))
    sim.sync(A, C)                                  # criss-cross
    assert sim.stats.antichain_sizes[2] >= 1
    sim.sync_all()
    for r in range(4):
        assert dt.read(sim.head_state(r)) == frozenset({'a'}), \
            f"T1 orset: replica {r} read {dt.read(sim.head_state(r))}"
        assert dt.read(sim.head_state(r)) == \
            dt.oracle(sim.dag.events(sim.heads[r]))
    return "T1  orset routine criss-cross: converged, reads = {a} = oracle"

# ---------------------------------------------------------------------------
# T1F FAIL companion: on the same shape with symmetric concurrent inserts
# then cross-deletes, EVERY single-MCA pick resurrects one deleted element;
# the virtual LCA resurrects neither. Hand-derived verdicts.
# ---------------------------------------------------------------------------

def t1f_single_pick_fails():
    dt = EmbedRGA()
    sim = Sim(dt, 4)
    A, B, C, D = range(4)
    sim.commit(A, ins_op(sim, A, 'w', 0))          # ts 1
    sim.sync_all()
    sim.commit(A, ins_op(sim, A, 'x', 0))          # ts 2 -> head u
    sim.commit(B, ins_op(sim, B, 'y', 0))          # ts 3 -> head v
    u, v = sim.heads[A], sim.heads[B]
    sim.sync(C, A); sim.sync(D, B)
    sim.sync(A, B); sim.sync(C, D)                 # rivals m1, m2 of {u,v}
    sim.commit(A, ('del', sim.fresh_ts(), 2))      # kill x on the m1 side
    sim.commit(C, ('del', sim.fresh_ts(), 3))      # kill y on the m2 side
    ha, hc = sim.heads[A], sim.heads[C]
    assert sim.dag.mcas(ha, hc) == sorted([u, v])
    sa, sc = sim.dag.state(ha), sim.dag.state(hc)
    # virtual LCA: merge(u, v) through their true LCA
    lv = resolve_lca(sim.dag, dt, ha, hc, Stats(), 0)
    got = dt.read(dt.merge3(sim.dag.state(lv), sa, sc))
    assert got == ((1, 'w'),), f"T1F: virtual LCA wrong: {got}"
    # single picks: u sees x but not y => y resurrects; v dually
    pick_u = dt.read(dt.merge3(sim.dag.state(u), sa, sc))
    pick_v = dt.read(dt.merge3(sim.dag.state(v), sa, sc))
    # display is descending: the resurrected later root insert sorts first
    assert pick_u == ((3, 'y'), (1, 'w')), f"T1F: pick-u gave {pick_u}"
    assert pick_v == ((2, 'x'), (1, 'w')), f"T1F: pick-v gave {pick_v}"
    return ("T1F single-MCA picks resurrect a deleted element each "
            "(u->y, v->x); the virtual LCA resurrects neither")

# ---------------------------------------------------------------------------
# T2: randomized honest head-sync WITHOUT the criss-cross gate.
# ---------------------------------------------------------------------------

def random_embed_op(sim, rng, r):
    live = sorted(sim.head_state(r))
    if live and rng.random() < 0.3:
        return ('del', sim.fresh_ts(), rng.choice(live))
    anchor = rng.choice([0] + live)
    ts = sim.fresh_ts()
    return ins_op_at(sim, r, f'e{ts}', anchor, ts)

def ins_op_at(sim, r, elem, anchor, ts):
    acoord = '' if anchor == 0 else sim.head_state(r)[anchor][1]
    return ('ins', ts, elem, anchor, acoord + enc(ts - anchor))

def random_orset_op(sim, rng, r):
    present = sorted(sim.dt.read(sim.head_state(r)))
    if present and rng.random() < 0.4:
        e = rng.choice(present)
        observed = frozenset(t for t, x in sim.head_state(r) if x == e)
        return ('rem', sim.fresh_ts(), e, observed)
    return ('add', sim.fresh_ts(), rng.choice('abcdef'))

def t2_random(dt_cls, opgen, ntrials, tag):
    agg_sizes, agg_depths = Counter(), Counter()
    cc_trials = 0
    for trial in range(ntrials):
        rng = random.Random(trial * 7919 + 13)
        dt = dt_cls()
        nrep = rng.randint(3, 5)
        sim = Sim(dt, nrep)
        for _ in range(rng.randint(30, 60)):
            if rng.random() < 0.55:
                r = rng.randrange(nrep)
                sim.commit(r, opgen(sim, rng, r))
            else:
                i, j = rng.sample(range(nrep), 2)
                sim.sync(i, j)
                h = sim.heads[i]
                assert dt.read(sim.dag.state(h)) == \
                    dt.oracle(sim.dag.events(h)), \
                    f"T2 {tag} trial {trial}: post-sync oracle mismatch"
        sim.sync_all()
        fps = {dt.fp(sim.head_state(r)) for r in range(nrep)}
        assert len(fps) == 1, f"T2 {tag} trial {trial}: states diverged"
        h = sim.heads[0]
        assert dt.read(sim.dag.state(h)) == dt.oracle(sim.dag.events(h)), \
            f"T2 {tag} trial {trial}: final oracle mismatch"
        if sim.stats.antichain_sizes:
            cc_trials += 1
        agg_sizes.update(sim.stats.antichain_sizes)
        agg_depths.update(sim.stats.res_depths)
    return (f"T2  {tag}: {ntrials} trials converged, all reads = fold oracle; "
            f"criss-cross in {cc_trials}/{ntrials} trials; "
            f"antichain sizes {dict(sorted(agg_sizes.items()))}; "
            f"resolution depths {dict(sorted(agg_depths.items()))}")

# ---------------------------------------------------------------------------
# T3/T5 shared builder: a directed NESTED criss-cross. Rival merges m1,m2
# of diverged heads {u,v}; then rival merges n1,n2 of {m1,m2}; heads end at
# n1' and n2'. Syncing n1' with n2' finds MCAs {m1,m2}, and resolving THEM
# finds MCAs {u,v}: recursion depth 2. Commit c1 sits below the common base
# c2 and is needed by nothing (strict-pruning witness).
# ---------------------------------------------------------------------------

def build_nested(dt_cls=EmbedRGA):
    dt = dt_cls()
    sim = Sim(dt, 8)
    A, B, C, D, E, F, G, H = range(8)
    sim.commit(A, ins_op(sim, A, 'a0', 0))         # c1 (interior, prunable)
    sim.commit(A, ins_op(sim, A, 'a', 0))          # c2 = common base
    sim.sync_all()
    base = sim.heads[A]
    sim.commit(A, ins_op(sim, A, 'b', 0))          # -> u
    sim.commit(B, ins_op(sim, B, 'c', 0))          # -> v
    u, v = sim.heads[A], sim.heads[B]
    sim.sync(C, A); sim.sync(D, B)                 # ff
    sim.sync(A, B); sim.sync(C, D)                 # rivals m1, m2 (LCA base)
    m1, m2 = sim.heads[A], sim.heads[C]
    sim.sync(E, A); sim.sync(F, C)                 # ff E->m1, F->m2
    sim.sync(E, F)                                  # n1 (resolves {u,v})
    sim.sync(G, B); sim.sync(H, D)                 # ff G->m1, H->m2
    sim.sync(G, H)                                  # n2, rival of n1
    n1, n2 = sim.heads[E], sim.heads[G]
    assert sorted([m1, m2]) == sim.dag.mcas(n1, n2)
    sim.commit(E, ins_op(sim, E, 'd', 0))          # -> n1'
    sim.commit(G, ins_op(sim, G, 'e', 0))          # -> n2'
    for r, tgt in ((A, E), (B, E), (F, E), (C, G), (D, G), (H, G)):
        sim.sync(r, tgt)                            # ff stragglers
    assert {sim.heads[r] for r in (A, B, E, F)} == {sim.heads[E]}
    assert {sim.heads[r] for r in (C, D, G, H)} == {sim.heads[G]}
    ids = dict(c1=base - 1, base=base, u=u, v=v, m1=m1, m2=m2,
               n1=n1, n2=n2, n1p=sim.heads[E], n2p=sim.heads[G])
    return sim, dt, ids

def t3_nested():
    sim, dt, ids = build_nested()
    E, G = 4, 6
    sim.stats = Stats()
    sim.sync(E, G)
    assert sim.stats.res_depths.get(0, 0) >= 1, "T3: no top resolution"
    assert sim.stats.res_depths.get(1, 0) >= 1, \
        "T3: nested resolution (recursion depth 2) not exercised"
    sim.sync_all()
    # Hand-derived: root-anchored a0(1) a(2) b(3) c(4) d(5) e(6), no
    # deletes; descending delta order.
    expect = ((6, 'e'), (5, 'd'), (4, 'c'), (3, 'b'), (2, 'a'), (1, 'a0'))
    for r in range(8):
        assert dt.read(sim.head_state(r)) == expect, \
            f"T3: replica {r} read {dt.read(sim.head_state(r))}"
        assert dt.read(sim.head_state(r)) == \
            dt.oracle(sim.dag.events(sim.heads[r]))
    return (f"T3  nested criss-cross: recursion depth 2 exercised "
            f"(resolution depths {dict(sim.stats.res_depths)}), converged, "
            f"reads = hand value = oracle")

# ---------------------------------------------------------------------------
# T5: keep-set check. Runtime rule (gc.js): seeds = pairwise MCAs of the
# current heads (self-pairs included), Keep = upward closure. Revised rule:
# seeds = the mcas-CLOSURE of the head set (fixpoint under pairwise mcas),
# Keep = upward closure. The depth-2 resolution reads {m1,m2,u,v,base}:
# outside the runtime Keep (PrunedError demonstrated), inside the revised.
# ---------------------------------------------------------------------------

def keep_runtime(dag, heads):
    seeds = set()
    hs = sorted(set(heads))
    for i in hs:
        for j in hs:
            seeds.update(dag.mcas(i, j))
    return dag.descendants_of(seeds), seeds

def keep_revised(dag, heads):
    seeds = set(heads)
    while True:
        new = set()
        for i in sorted(seeds):
            for j in sorted(seeds):
                new.update(dag.mcas(i, j))
        if new <= seeds:
            break
        seeds |= new
    return dag.descendants_of(seeds), seeds

def prune_outside(dag, keep):
    dropped = []
    for cid in list(dag.states):
        if cid not in keep and cid != 0 and dag.states[cid] is not None:
            dag.states[cid] = None
            dropped.append(cid)
    return dropped

def t5_keepset():
    E, G = 4, 6
    # control: what does the depth-2 sync read?
    sim, dt, ids = build_nested()
    sim.stats = Stats()
    sim.sync(E, G)
    needed = set(sim.stats.reads)
    expect_needed = {ids['m1'], ids['m2'], ids['u'], ids['v'], ids['base']}
    assert needed == expect_needed, f"T5: reads {needed} != {expect_needed}"
    sim.sync_all()
    control_read = dt.read(sim.head_state(0))

    # runtime keep loses u, v, base
    sim, dt, ids = build_nested()
    kr, seeds_r = keep_runtime(sim.dag, sim.heads.values())
    missing = expect_needed - kr
    assert missing == {ids['u'], ids['v'], ids['base']}, \
        f"T5: runtime keep unexpectedly retains {expect_needed & kr}"
    prune_outside(sim.dag, kr)
    try:
        sim.sync(E, G)
        raise AssertionError("T5: sync after runtime-keep prune succeeded")
    except PrunedError:
        pass

    # revised keep retains everything the recursion reads, yet still prunes
    sim, dt, ids = build_nested()
    kv, seeds_v = keep_revised(sim.dag, sim.heads.values())
    assert expect_needed <= kv
    assert ids['c1'] not in kv, "T5: revised keep is not strict"
    dropped = prune_outside(sim.dag, kv)
    assert ids['c1'] in dropped
    sim.sync(E, G)
    sim.sync_all()
    assert dt.read(sim.head_state(0)) == control_read
    return ("T5  keep-set: runtime one-layer MCA seeds drop {u,v,base}; "
            "depth-2 sync raises PrunedError. mcas-closure seeds keep them "
            f"(still pruning {len(dropped)} commits incl. the interior c1); "
            "post-GC sync matches the no-GC control")

def main():
    results = [
        t1_embed(),
        t1_orset(),
        t1f_single_pick_fails(),
        t2_random(EmbedRGA, random_embed_op, 500, 'embedRGA'),
        t2_random(ORSet, random_orset_op, 300, 'orset'),
        t3_nested(),
        t5_keepset(),
    ]
    for r in results:
        print(r)
    print("ALL CHECKS PASSED (P1 covering + P2 order-insensitivity asserted "
          "at every resolution throughout)")

if __name__ == '__main__':
    main()
