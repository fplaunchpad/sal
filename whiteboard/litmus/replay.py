#!/usr/bin/env python3
"""
Task #68 -- the OP-REPLAY layer of the delta tree (DeltaTreeV3), tested
empirically.  New file; touches nothing existing.

Op model (the linearization-replay operations, cf. the path-carrying RGA's
"why-the-path-matters" note: rc = Either for ALL pairs, so an insert must be
applicable on states where its anchor is already dead):

  ins op:  ('ins', x, ch, path, slice)
      path  = the anchor's root->anchor id path in the MINT state's live tree
              (a tuple; () means anchored at the root sentinel 0),
      slice = ONE ABSOLUTE (lo, hi): the absolute range the local carve would
              assign at mint time.
  del op:  ('del', d, ts)          (ts only orders linearizations)

  apply_op(state, op, rule):
      ins: host := deepest LIVE id on path (nearest live ancestor; 0 if none);
           re-relativize the carried absolute slice into host's CURRENT
           absolute frame;  led[x] := MINT anchor (path[-1], or 0) -- NOT the
           rehomed host.  Total and deterministic in (state, op).
      del: the isometric fold, byte-identical to DeltaTreeV3.apply's delete.

Collision rules for same-anchor concurrent inserts applied in sequence:
  R0  none: pure carried-slice placement.
  R1  exact-slice collision -> re-carve above the level head (task's proposal).
  R2i insert-side canonical repair only (ablation of R2's delete half).
  R2  ledger-canonical placement: EVERY op leaves its touched level canonical.
      After the plain placement (insert) or the isometric fold (delete), if
      the touched child level is no longer in canonical birth-chain order
      (the merge's arbitration order), or an insert landed uncontained
      (relative slice outside [0,1] -- a stale carried slice against a
      re-rendered frame), re-render THAT LEVEL with the merge's sequential
      carve.  Geometry never arbitrates; the ledger does -- now also at op
      application time, not only at merges.

================================ FINDINGS ====================================
(reproduce: python3 replay.py   -- fixed seeds, exact-fraction arithmetic)

SANITY A (origin consistency)      R0/R1/R2: PASS, 2860 cases (inserts at
   every anchor + deletes of every live element over 254 harvested reachable
   states), EXACT state equality.  R2's repairs never fire at origin: the
   plain placement of a fresh op is already canonical there.
T1 FOLD-INVARIANCE (ins||del anchor) R0/R1/R2: PASS, 1303 diamonds, EXACT
   state equality in both orders -- the PDF's central claim ("a reordered
   application lands exactly where insert-then-delete would have put it")
   holds at every harvested reachable state, as strict state equality, not
   just up to ~.
T2 DIAMOND SWEEP (8 pair shapes, ~3400 diamonds/rule)
   R0: every shape STATE-EQUAL.  Reason (and the design's payoff): carried
       absolute slices + isometric folds mean NOTHING EVER MOVES -- a node's
       absolute range is a birth invariant, so the replay state is a function
       of the op SET (see permutation invariance).
   R1: ii_same_* DIVERGENT (the collision re-carve is order-dependent).
   R2: no DIVERGENT pair; ii_same_forked has 13/424 EQUIV(~) cases (exactly
       one order fires a repair; read-equal + merge-future-equal + read-equal
       under common random suffixes), all other shapes state-equal.
T3 LOCKSTEP vs merge-based V3 (60 DAG executions, reads compared at every op
   and merge):   R0 55/60 DIVERGE, R1 48/60, R2i 11/60, R2 CLEAN 60/60.
   The crack is NOT the exact-slice collision per se (equal slices tie-break
   by id descending = newest-first = canonical) but CANONICAL-ORDER MISMATCH:
   geometry minted against one sibling set contradicts the ledger order the
   merge renders.  Strict counterexample ladder (encoded as CE1/CE2/CE3):
     CE1 (3 ops, kills R0):  A: ins1@0, ins2@0   B: ins3@0
         replay R0 reads [2,3,1], merge renders [3,2,1]: ins3's slice
         (1/4,1/2) collides with ins1's; 2 sits above both.  R1 fixes it.
     CE2 (4 ops, kills R1):  A: ins1@0, ins2@0, del1   B: ins4@0
         same mismatch with the colliding node DELETED: no exact collision
         ever fires, replay reads [2,4] vs merge [4,2].  R1 is also
         linearization-DEPENDENT (whether del1 precedes ins4 decides whether
         its re-carve fires): permutation invariance FAILS for R1.
     CE3 (4 ops, kills R2i): A: ins1@0, ins2@1, del1   B: ins5@0
         the LATENT TIE: ins5 exactly collides with ins1; the id tiebreak
         orders {1,5} canonically, so insert-side repair sees nothing.  But
         2 lives INSIDE the shared slice, and del1's fold drops it into the
         root level, where the 5-vs-2 order is RE-DECIDED BY POSITION:
         replay [2,5] vs merge [5,2].  Same mechanism class that refuted
         delta-tree v1/v2 at merges (a ts-decided pair re-decided by
         geometry), resurfacing at the op layer; forces R2's delete half.
   Repair frequency (60 runs): R2 fired ins-side 4533x, del-side 102x -- the
   lazy repair is common (stale carried slices), so a Lean port may prefer
   an always-render insert; the LAZY rule is what keeps sanity A exact.
PERMUTATION INVARIANCE (final converged op sets, random linear extensions of
   the op dependency order):
   R0: final STATE equal 48/48 -- the replay layer is a pure op-based CRDT
       (state = f(op set)); it is convergent, just not to the MERGE's order.
   R1: read-equal 4/48 -- refuted a second way (not even read-invariant).
   R2: final READ equal 48/48; state equal only 7/48 (which re-renders fired
       is order-dependent) -- the framework's ~ quotient made concrete.
==============================================================================
"""
import sys, os
from fractions import Fraction
from random import Random

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import litmus as L                      # noqa: E402
from delta_tree import DeltaTreeV3     # noqa: E402

V = DeltaTreeV3()
F0, F1 = Fraction(0), Fraction(1)

# --------------------------------------------------------------- geometry
def _abs(r, u):
    """Absolute (lo, hi) of live node u (0 = the root frame [0,1])."""
    chain = []
    while u != 0:
        chain.append(u); u = r[u][0]
    lo, hi = F0, F1
    for v in reversed(chain):
        _, l, h = r[v]
        w = hi - lo
        lo, hi = lo + w * l, lo + w * h
    return lo, hi

def _tree_path(r, a):
    """root->a id path in the live tree (a live or 0)."""
    p = []
    while a != 0:
        p.append(a); a = r[a][0]
    p.reverse(); return p

def _chain(led, x):
    ch = []
    while x != 0:
        ch.append(-x); x = led[x]
    ch.reverse(); return ch

def _kids_geo(r, p):
    """Child level of p in READ order (top -> bottom): descending (lo, id)."""
    return sorted((x for x in r if r[x][0] == p),
                  key=lambda x: (r[x][1], x), reverse=True)

def _render_level(r, led, p):
    """The merge's sequential-carve render, restricted to p's child level
    (descendants are relative and follow automatically)."""
    ks = sorted((x for x in r if r[x][0] == p), key=lambda x: _chain(led, x))
    base = F0
    for k in reversed(ks):                      # oldest first, bottom-up
        w = F1 - base
        r[k] = (p, base + w / 4, base + w / 2)
        base = base + w / 2

# --------------------------------------------------------------- op model
def mint_ins(s, x, a, ch=None):
    """Mint an insert op against state s: anchor a must be live (or 0)."""
    r, _ = s
    p = a if a != 0 else 0
    path = tuple(_tree_path(r, p))
    base = max((r[k][2] for k in r if r[k][0] == p), default=F0)
    w = F1 - base
    plo, phi = _abs(r, p)
    pw = phi - plo
    return ('ins', x, ch, path,
            (plo + pw * (base + w / 4), plo + pw * (base + w / 2)))

def mint_del(d, ts):
    return ('del', d, ts)

def op_ts(op):
    return op[1] if op[0] == 'ins' else op[2]

DEGENERATE = []          # zero-width host frames ever hit (never expected)
REPAIRS = {'ins': 0, 'del': 0}   # how often R2's level re-render fires

def apply_op(s, op, rule='R0'):
    """Total, deterministic op application. Returns the (mutated) state."""
    r, led = s
    if op[0] == 'ins':
        _, x, ch, path, sl = op
        h = 0
        for u in reversed(path):                # deepest live id on the path
            if u in r:
                h = u; break
        hlo, hhi = _abs(r, h)
        hw = hhi - hlo
        if hw == 0:                             # totality guard (flagged)
            DEGENERATE.append((x, h))
            rel = (Fraction(1, 4), Fraction(1, 2))
        else:
            rel = ((sl[0] - hlo) / hw, (sl[1] - hlo) / hw)
        if rule == 'R1' and any((r[k][1], r[k][2]) == rel
                                for k in r if r[k][0] == h):
            base = max((r[k][2] for k in r if r[k][0] == h), default=F0)
            w = F1 - base
            rel = (base + w / 4, base + w / 2)  # re-carve above the level
        r[x] = (h, rel[0], rel[1])
        led[x] = path[-1] if path else 0        # the MINT anchor, not h
        if rule in ('R2', 'R2i'):
            geo = _kids_geo(r, h)
            can = sorted(geo, key=lambda k: _chain(led, k))
            # re-render if geometry contradicts the ledger OR the placement
            # broke containment (stale carried slice vs a re-rendered frame):
            # an uncontained child survives folds at the wrong position, so
            # containment is part of the invariant, not just order.
            if geo != can or not (F0 <= rel[0] < rel[1] <= F1):
                REPAIRS['ins'] += 1
                _render_level(r, led, h)
    else:
        d = op[1]
        if d in r:
            dp, dl, dh = r.pop(d)
            dw = dh - dl
            for c in list(r):
                if r[c][0] == d:                # isometric fold
                    _, cl, ch2 = r[c]
                    r[c] = (dp, dl + dw * cl, dl + dw * ch2)
            if rule == 'R2':                    # (R2i deliberately omits this)
                # symmetric repair: a fold can re-decide a tie that the id
                # tiebreak was carrying (exact-collision slices), so the
                # DELETE must also leave its touched level canonical.
                geo = _kids_geo(r, dp)
                can = sorted(geo, key=lambda k: _chain(led, k))
                if geo != can:
                    REPAIRS['del'] += 1
                    _render_level(r, led, dp)
    return (r, led)

def replay_all(opset, rule):
    """Fold apply_op over a linearization (ascending ts) from the empty state."""
    s = V.init()
    for op in sorted(opset, key=op_ts):
        s = apply_op(s, op, rule)
    return s

# ---------------------------------------------------- reachable-state harvest
def harvest(n_seeds=8, n_replicas=4, n_rounds=8, max_ops=2,
            p_del=0.3, p_merge=0.4):
    """Merge-based DeltaTreeV3 executions (same generator shape as
    pbt.run_execution, re-implemented here so pbt.py stays untouched);
    returns [(state, next_fresh_id)] snapshots, fp-deduplicated."""
    states, seen = [], set()

    def snap(st, nid):
        f = V.fp(st)
        if f not in seen:
            seen.add(f)
            states.append((V.copy(st), nid))

    for seed in range(n_seeds):
        rng = Random(1000 + seed)
        init = V.init()
        versions = [(frozenset(), init)]
        heads = [(frozenset(), init)] * n_replicas
        nid = [1]
        for _ in range(n_rounds):
            for rep in range(n_replicas):
                if rng.random() < p_merge:
                    j = rng.randrange(n_replicas)
                    (ei, si), (ej, sj) = heads[rep], heads[j]
                    if j == rep or ei == ej:
                        continue
                    inter = ei & ej
                    lca = next(((ev, st) for (ev, st) in versions
                                if ev == inter), None)
                    if lca is None:
                        continue
                    m = V.merge(V.copy(lca[1]), V.copy(si), V.copy(sj))
                    heads[rep] = (ei | ej, m)
                    versions.append(heads[rep])
                    snap(m, nid[0])
                else:
                    ev, st = heads[rep]
                    st = V.copy(st); ev = set(ev)
                    for _ in range(rng.randint(1, max_ops)):
                        doc = V.read(st)
                        if doc and rng.random() < p_del:
                            d = rng.choice(doc)
                            st = V.apply(st, ('del', d)); ev.add(('d', d))
                        else:
                            a = rng.choice([0] + doc) if doc else 0
                            x = nid[0]; nid[0] += 1
                            st = V.apply(st, ('ins', x, a)); ev.add(x)
                        snap(st, nid[0])
                    heads[rep] = (frozenset(ev), st)
                    versions.append(heads[rep])
    return states

# ------------------------------------------------------------------ sanity A
def sanity_A(states, rule):
    """Freshly minted op applied at its origin == the local intention
    (inserts at every anchor, deletes of every live element)."""
    bad, n = [], 0
    for (s, nid) in states:
        for a in [0] + V.read(s):
            i = mint_ins(s, nid, a)
            s1 = apply_op(V.copy(s), i, rule)
            s2 = V.apply(V.copy(s), ('ins', nid, a))
            n += 1
            if V.fp(s1) != V.fp(s2):
                bad.append(('ins', a))
        for d in V.read(s):
            o = mint_del(d, nid)
            s1 = apply_op(V.copy(s), o, rule)
            s2 = V.apply(V.copy(s), ('del', d))
            n += 1
            if V.fp(s1) != V.fp(s2):
                bad.append(('del', d))
    return n, bad

# ----------------------------------------------------------- equivalence (~)
def canonical_render(s):
    """V.merge(s,s,s): survivor set = all live ids, so this is exactly the
    merge's canonical render of s -- every merge-future of two states with
    equal live ids + ledger is decided by this (merge reads only ids + led)."""
    return V.merge(V.copy(s), V.copy(s), V.copy(s))

def futeq(s1, s2, rng, nid, rule, rounds=8):
    """Empirical ~: read-equal now, merge-future equal, and read-equal under a
    common random op suffix applied to both."""
    if V.read(s1) != V.read(s2):
        return False
    if V.read(canonical_render(s1)) != V.read(canonical_render(s2)):
        return False
    s1, s2 = V.copy(s1), V.copy(s2)
    for _ in range(rounds):
        doc = V.read(s1)
        if doc and rng.random() < 0.35:
            op = mint_del(rng.choice(doc), nid); nid += 1
        else:
            a = rng.choice([0] + doc) if doc else 0
            op = mint_ins(s1, nid, a); nid += 1
        s1 = apply_op(s1, op, rule)
        s2 = apply_op(s2, op, rule)
        if V.read(s1) != V.read(s2):
            return False
    return True

def classify(s, o1, o2, rng, nid, rule):
    s1 = apply_op(apply_op(V.copy(s), o1, rule), o2, rule)
    s2 = apply_op(apply_op(V.copy(s), o2, rule), o1, rule)
    if V.fp(s1) == V.fp(s2):
        return 'state-equal'
    if futeq(s1, s2, rng, nid, rule):
        return 'EQUIV(~)'
    return 'DIVERGENT'

# ------------------------------------------------------- T1: fold invariance
def t1_fold_invariance(states, rule):
    counts = {'state-equal': 0, 'EQUIV(~)': 0, 'DIVERGENT': 0}
    worst = []
    for si, (s, nid) in enumerate(states):
        rng = Random(20000 + si)
        for a in V.read(s):
            i = mint_ins(s, nid, a)
            d = mint_del(a, nid + 1)
            v = classify(s, i, d, rng, nid + 2, rule)
            counts[v] += 1
            if v == 'DIVERGENT':
                worst.append((si, a))
    return counts, worst

# ---------------------------------------------------------- T2: diamond sweep
def t2_diamonds(states, rule, per_state=2):
    shapes = ['ii_same_co', 'ii_same_forked', 'ii_diff',
              'id_anchor', 'id_ancestor', 'id_unrel', 'dd_diff', 'dd_same']
    out = {sh: {'state-equal': 0, 'EQUIV(~)': 0, 'DIVERGENT': 0}
           for sh in shapes}
    worst = []
    for si, (s0, nid0) in enumerate(states):
        rng = Random(30000 + si)
        for t in range(per_state):
            doc = V.read(s0)
            nid = nid0 + 100 * t
            for sh in shapes:
                s = V.copy(s0)
                if sh == 'ii_same_co':
                    a = rng.choice([0] + doc) if doc else 0
                    o1 = mint_ins(s, nid, a); o2 = mint_ins(s, nid + 1, a)
                elif sh == 'ii_same_forked':
                    # two branches from s mint under the SAME anchor after
                    # divergent local histories; diamond at the join state.
                    a = rng.choice([0] + doc) if doc else 0
                    f1, f2 = V.copy(s), V.copy(s)
                    e1 = e2 = None
                    k1 = rng.randint(0, 2); k2 = rng.randint(0, 2)
                    m = nid + 2
                    fork_ops = []
                    for f, k in ((f1, k1), (f2, k2)):
                        for _ in range(k):
                            dd = V.read(f)
                            if dd and rng.random() < 0.4:
                                e = mint_del(rng.choice(dd), m)
                            else:
                                aa = rng.choice([0] + dd) if dd else 0
                                e = mint_ins(f, m, aa)
                            m += 1
                            apply_op(f, e, rule); fork_ops.append(e)
                    if not (a == 0 or (a in f1[0] and a in f2[0])):
                        continue                    # anchor died on a fork
                    o1 = mint_ins(f1, m, a); o2 = mint_ins(f2, m + 1, a)
                    s = V.copy(s0)                  # join state = s0 + both forks
                    for e in sorted(fork_ops, key=op_ts):
                        apply_op(s, e, rule)
                elif sh == 'ii_diff':
                    if len(doc) < 1:
                        continue
                    a1 = rng.choice([0] + doc); a2 = rng.choice([0] + doc)
                    if a1 == a2:
                        continue
                    o1 = mint_ins(s, nid, a1); o2 = mint_ins(s, nid + 1, a2)
                elif sh == 'id_anchor':
                    if not doc:
                        continue
                    a = rng.choice(doc)
                    o1 = mint_ins(s, nid, a); o2 = mint_del(a, nid + 1)
                elif sh == 'id_ancestor':
                    r = s[0]
                    deep = [x for x in doc if x in r and r[x][0] != 0]
                    if not deep:
                        continue
                    a = rng.choice(deep)
                    anc = rng.choice(_tree_path(r, r[a][0]))
                    o1 = mint_ins(s, nid, a); o2 = mint_del(anc, nid + 1)
                elif sh == 'id_unrel':
                    r = s[0]
                    if len(doc) < 2:
                        continue
                    a, b = rng.sample(doc, 2)
                    if b in _tree_path(r, a):
                        continue
                    o1 = mint_ins(s, nid, a); o2 = mint_del(b, nid + 1)
                elif sh == 'dd_diff':
                    if len(doc) < 2:
                        continue
                    a, b = rng.sample(doc, 2)
                    o1 = mint_del(a, nid); o2 = mint_del(b, nid + 1)
                else:  # dd_same
                    if not doc:
                        continue
                    a = rng.choice(doc)
                    o1 = mint_del(a, nid); o2 = mint_del(a, nid + 1)
                v = classify(s, o1, o2, rng, nid + 50, rule)
                out[sh][v] += 1
                if v == 'DIVERGENT':
                    worst.append((si, sh))
    return out, worst

# ------------------------------------------ T3: lockstep replay vs merge model
def lockstep(rule, seed, n_replicas=4, n_rounds=8, max_ops=2,
             p_del=0.3, p_merge=0.4, snap=None):
    """Run the op-replay model and the merge-based DeltaTreeV3 side by side on
    ONE random schedule; compare reads at every op and merge.  Returns the
    first divergence or None."""
    rng = Random(seed)
    init_v, init_r = V.init(), V.init()
    versions = [(frozenset(), init_v)]
    # replica -> (events, v3-state, op-set, replay-state)
    heads = [(frozenset(), init_v, frozenset(), init_r)] * n_replicas
    ctr = [1]

    def diverged(tag, rv, vv):
        return (seed, tag, rv, vv)

    for rnd in range(n_rounds + 1):
        reps = list(range(n_replicas))
        for rep in reps:
            if rng.random() < p_merge or rnd == n_rounds:
                j = rng.randrange(n_replicas)
                (ei, vi, oi, ri) = heads[rep]
                (ej, vj, oj, rj) = heads[j]
                if j == rep or ei == ej:
                    continue
                inter = ei & ej
                lca = next(((ev, st) for (ev, st) in versions
                            if ev == inter), None)
                if lca is None:
                    continue
                mv = V.merge(V.copy(lca[1]), V.copy(vi), V.copy(vj))
                mo = oi | oj
                mr = replay_all(mo, rule)
                if V.read(mr) != V.read(mv):
                    return diverged(f'merge:r{rep}+r{j}',
                                    V.read(mr), V.read(mv))
                heads[rep] = (ei | ej, mv, mo, mr)
                versions.append((ei | ej, mv))
                if snap is not None:
                    snap(mr, ctr[0])
            else:
                ev, vs, os_, rs = heads[rep]
                vs, rs = V.copy(vs), V.copy(rs)
                ev, os_ = set(ev), set(os_)
                for _ in range(rng.randint(1, max_ops)):
                    doc = V.read(vs)
                    if V.read(rs) != doc:
                        return diverged(f'op:r{rep}', V.read(rs), doc)
                    if doc and rng.random() < p_del:
                        d = rng.choice(doc)
                        op = mint_del(d, ctr[0]); ctr[0] += 1
                        vs = V.apply(vs, ('del', d)); ev.add(('d', d))
                    else:
                        a = rng.choice([0] + doc) if doc else 0
                        x = ctr[0]; ctr[0] += 1
                        op = mint_ins(rs, x, a)         # minted on the op model
                        vs = V.apply(vs, ('ins', x, a)); ev.add(x)
                    rs = apply_op(rs, op, rule); os_.add(op)
                    if V.read(rs) != V.read(vs):
                        return diverged(f'op:r{rep}', V.read(rs), V.read(vs))
                    if snap is not None:
                        snap(rs, ctr[0])
                heads[rep] = (frozenset(ev), vs, frozenset(os_), rs)
                versions.append((frozenset(ev), vs))

    # forced convergence sweep (same discipline as pbt)
    for _ in range(6 * n_replicas):
        pairs = [(i, j) for i in range(n_replicas) for j in range(n_replicas)
                 if i != j and heads[i][0] != heads[j][0]]
        if not pairs:
            break
        rng.shuffle(pairs)
        merged = False
        for (i, j) in pairs:
            (ei, vi, oi, ri) = heads[i]
            (ej, vj, oj, rj) = heads[j]
            inter = ei & ej
            lca = next(((ev, st) for (ev, st) in versions
                        if ev == inter), None)
            if lca is None:
                continue
            mv = V.merge(V.copy(lca[1]), V.copy(vi), V.copy(vj))
            mo = oi | oj
            mr = replay_all(mo, rule)
            if V.read(mr) != V.read(mv):
                return diverged(f'conv:r{i}+r{j}', V.read(mr), V.read(mv))
            heads[i] = (ei | ej, mv, mo, mr)
            versions.append((ei | ej, mv))
            merged = True
            break
        if not merged:
            break
    return None

def t3_sweep(rule, n=60):
    fails = []
    for seed in range(n):
        d = lockstep(rule, seed)
        if d:
            fails.append(d)
    return fails

# ------------------------------------------------ minimized counterexamples
def two_branch(rule, scriptA, scriptB):
    """Two branches from the empty LCA; each script is a list of
    ('ins', id, anchor) / ('del', d, ts) intentions executed locally (op model
    mints them).  Returns (replay read, merge-based v3 read)."""
    ops = []

    def run(script):
        sv, sr = V.init(), V.init()
        for it in script:
            if it[0] == 'ins':
                op = mint_ins(sr, it[1], it[2])
                sv = V.apply(sv, ('ins', it[1], it[2]))
            else:
                op = mint_del(it[1], it[2])
                sv = V.apply(sv, ('del', it[1]))
            sr = apply_op(sr, op, rule)
            ops.append(op)
        return sv

    vA = run(scriptA)
    vB = run(scriptB)
    mv = V.merge(V.init(), vA, vB)
    mr = replay_all(frozenset(ops), rule)
    return V.read(mr), V.read(mv)

CE1 = ("CE1: A=[ins1@0, ins2@0]  B=[ins3@0]        (3 ops)",
       [('ins', 1, 0), ('ins', 2, 0)],
       [('ins', 3, 0)])
CE2 = ("CE2: A=[ins1@0, ins2@0, del1]  B=[ins4@0]  (4 ops)",
       [('ins', 1, 0), ('ins', 2, 0), ('del', 1, 3)],
       [('ins', 4, 0)])
# CE3 (found by minimizing lockstep seed 14): the latent id-tie.  ins5@0 on B
# EXACTLY collides with ins1@0's slice (both minted against the empty root
# level); the replay orders {1,5} by the id tiebreak -- which MATCHES the
# canonical order, so an insert-side-only repair (R2i) sees nothing to fix.
# But 2 lives INSIDE the shared slice; del1's fold drops 2 into the root
# level, where the 5-vs-(1's subtree) tie is RE-DECIDED BY POSITION:
# geo [2,5] vs ledger [5,2].  Same mechanism class that refuted delta-tree
# v1/v2 at merges (ts-decided pair re-decided by geometry), resurfacing at
# the op layer.  Forces the delete-side half of R2.
CE3 = ("CE3: A=[ins1@0, ins2@1, del1(ts8)]  B=[ins5@0]  (4 ops; latent tie + fold)",
       [('ins', 1, 0), ('ins', 2, 1), ('del', 1, 8)],
       [('ins', 5, 0)])

# ------------------------------------------------- permutation invariance
def op_deps(opset):
    """Dependency partial order every valid linearization must extend:
    an insert after the inserts of all its path ids; a delete after the
    insert of its target."""
    ins_of = {op[1]: op for op in opset if op[0] == 'ins'}
    deps = {op: set() for op in opset}
    for op in opset:
        if op[0] == 'ins':
            for u in op[3]:
                if u in ins_of:
                    deps[op].add(ins_of[u])
        else:
            if op[1] in ins_of:
                deps[op].add(ins_of[op[1]])
    return deps

def rand_linext(opset, deps, rng):
    ops = sorted(opset, key=op_ts)       # canonical base order: determinism
    ready = [op for op in ops if not deps[op]]
    done, out = set(), []
    pend = {op: set(d) for op, d in deps.items()}
    while ready:
        op = ready.pop(rng.randrange(len(ready)))
        out.append(op); done.add(op)
        for q in ops:
            if q not in done and q not in ready and pend[q] <= done:
                ready.append(q)
    assert len(out) == len(opset)
    return out

def perm_invariance(rule, n_exec=12, n_perms=5):
    """Final converged op sets from lockstep runs, replayed under random
    linear extensions of the dependency order."""
    state_eq, read_eq, total = 0, 0, 0
    bad = []
    for seed in range(n_exec):
        opset = set()
        _collect_ops(rule, seed, opset)
        if not opset:
            continue
        deps = op_deps(opset)
        rng = Random(50000 + seed)
        base = None
        for _ in range(n_perms):
            lin = rand_linext(opset, deps, rng)
            s = V.init()
            for op in lin:
                s = apply_op(s, op, rule)
            if base is None:
                base = s
            else:
                total += 1
                if V.fp(s) == V.fp(base):
                    state_eq += 1; read_eq += 1
                elif V.read(s) == V.read(base):
                    read_eq += 1
                else:
                    bad.append(seed)
    return state_eq, read_eq, total, bad

def _collect_ops(rule, seed, sink):
    """Run a replay-only execution (no merge model) and put all minted ops in
    sink; mirrors lockstep's schedule shape."""
    rng = Random(70000 + seed)
    n_replicas, n_rounds, max_ops, p_del, p_merge = 4, 6, 2, 0.3, 0.4
    heads = [(frozenset(), V.init())] * n_replicas
    ctr = [1]
    for _ in range(n_rounds):
        for rep in range(n_replicas):
            if rng.random() < p_merge:
                j = rng.randrange(n_replicas)
                if j == rep:
                    continue
                (oi, ri), (oj, rj) = heads[rep], heads[j]
                mo = oi | oj
                heads[rep] = (mo, replay_all(mo, rule))
            else:
                os_, rs = heads[rep]
                os_, rs = set(os_), V.copy(rs)
                for _ in range(rng.randint(1, max_ops)):
                    doc = V.read(rs)
                    if doc and rng.random() < p_del:
                        op = mint_del(rng.choice(doc), ctr[0])
                    else:
                        a = rng.choice([0] + doc) if doc else 0
                        op = mint_ins(rs, ctr[0], a)
                    ctr[0] += 1
                    rs = apply_op(rs, op, rule); os_.add(op)
                heads[rep] = (frozenset(os_), rs)
    for (os_, _) in heads:
        sink |= os_
    return None

# ---------------------------------------------------------------- reporting
def main():
    rules = ['R0', 'R1', 'R2']
    print("harvesting reachable states from merge-based V3 executions ...")
    states = harvest()
    print(f"  {len(states)} distinct reachable states\n")

    print("== SANITY A: origin consistency (minted op at origin == local intention) ==")
    for rule in rules:
        n, bad = sanity_A(states, rule)
        print(f"  {rule}: {n} cases  "
              f"{'PASS (exact state equality)' if not bad else 'FAIL x' + str(len(bad))}")

    print("\n== T1 FOLD-INVARIANCE: mint(ins x under a) vs del(a), both orders ==")
    for rule in rules:
        counts, worst = t1_fold_invariance(states, rule)
        tot = sum(counts.values())
        print(f"  {rule}: {tot} diamonds  {counts}  "
              f"{'PASS' if not counts['DIVERGENT'] else 'FAIL first=' + str(worst[0])}")

    print("\n== T2 DIAMOND EQ-COMMUTATION SWEEP (per pair shape) ==")
    for rule in rules:
        out, worst = t2_diamonds(states, rule)
        print(f"  {rule}:")
        for sh, c in out.items():
            tot = sum(c.values())
            tag = ('DIVERGENT!' if c['DIVERGENT'] else
                   ('state-equal' if c['EQUIV(~)'] == 0 else
                    f"state-equal {c['state-equal']}, ~ {c['EQUIV(~)']}"))
            print(f"    {sh:16} n={tot:4}  {tag}")
        if worst:
            print(f"    first divergence: {worst[0]}")

    print("\n== T3 LOCKSTEP: op-replay model vs merge-based DeltaTreeV3 (60 runs) ==")
    for rule in ['R0', 'R1', 'R2i', 'R2']:
        REPAIRS['ins'] = REPAIRS['del'] = 0
        fails = t3_sweep(rule)
        rep = (f"   [repairs fired: ins {REPAIRS['ins']}, del {REPAIRS['del']}]"
               if rule in ('R2', 'R2i') else '')
        if not fails:
            print(f"  {rule}: CLEAN 60/60{rep}")
        else:
            s, tag, rv, vv = fails[0]
            print(f"  {rule}: {len(fails)}/60 DIVERGE  first: seed {s} @{tag}{rep}")
            print(f"        replay={rv}")
            print(f"        merge ={vv}")

    print("\n== MINIMIZED COUNTEREXAMPLES ==")
    for (name, sa, sb) in (CE1, CE2, CE3):
        print(f"  {name}")
        for rule in ['R0', 'R1', 'R2i', 'R2']:
            rr, vv = two_branch(rule, sa, sb)
            verdict = 'agree' if rr == vv else f'DIVERGE  replay={rr} merge={vv}'
            print(f"    {rule:3}: {verdict}")

    print("\n== PERMUTATION INVARIANCE (random linear extensions of op deps) ==")
    for rule in rules:
        se, re, tot, bad = perm_invariance(rule)
        print(f"  {rule}: {tot} replays  state-equal {se}/{tot}  "
              f"read-equal {re}/{tot}  "
              f"{'PASS' if re == tot else 'FAIL seeds=' + str(sorted(set(bad)))}")

    if DEGENERATE:
        print(f"\n!! degenerate zero-width host frames hit: {len(DEGENERATE)}")
    else:
        print("\n(zero-width host-frame fallback never exercised)")

if __name__ == '__main__':
    main()
