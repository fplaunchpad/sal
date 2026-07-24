#!/usr/bin/env python3
"""vc_minimality_check.py -- task #114 phase 1, the VC MINIMALITY SWEEP.

Validation harness for whiteboard/vc-minimality-note.md.  The flat metatheory
of the conditioned-MRDT framework (Sal/ConditionedMRDTs/Framework/VC_Set.lean,
Sigma_LoOn3.lean) has EIGHT verification conditions, and ADEQUACY proves

    VC1 .. VC8  =>  RA-linearizability.

MINIMALITY is the converse-flavoured irredundancy half.  For each VC_i:

  * INDEPENDENCE (H_i): exhibit a datatype satisfying the OTHER seven, failing
    VC_i, and NOT RA-linearizable.  Witnesses that VC_i is load-bearing (the
    reduced bundle {VC_j : j != i} no longer implies RA-lin).

  * DERIVABILITY (H_i'): show {VC_j : j != i}  =>  VC_i.  Shrinks the set.

#57 (Refutations/CD_Not_Derivable_Ternary.lean) already settled VC8 = CDVC3 as
INDEPENDENT (the AWSetF3 separator).  This sweep does VC1..VC7, starting from the
boundary datatypes MVR / OR-set / mergeable-queue.

THE EIGHT VCs (exact forms transcribed from VC_Set.lean + Sigma_LoOn3.lean;
tex labels fvc:rcnc..fvc:cd):

  VC1 rc_non_comm_directional : forall distinct cross-replica o1 o2,
        ~comm o1 o2  <->  (rc o1 o2 = Fst  or  rc o2 o1 = Fst)
  VC2 no_rc_chain           : forall o1 o2 o3 (o1!=o2, o2!=o3),
        ~(rc o1 o2 = Fst  and  rc o2 o3 = Fst)
  VC3 cond_comm_lift        : distinct e e' e''; rc e e' = Fst; ~comm e' e'';
        e''(fold(e(e'(s)),pi)) = e''(fold(e'(e(s)),pi))
  VC4 mergeL_comm           : mergeL l a b = mergeL l b a
  VC5 feasible_init         : Can_C(ev,s)  =>  mergeL s0 s0 s = s
  VC6 feasible_local_redist : (big local-redistribute identity on feasible tuples)
  VC7 feasible_redistribute : (redistribute identity on feasible tuples)
  VC8 CDVC3                 : e loOn(U)-maximal, A=sig(U-e), B=sig(down(e)-e):
        mergeL B A (e(B)) = e(A)

SEMANTIC LAYER (faithful to the Lean).  An Op is (ts, rep, appop).
  comm(e1,e2)     := forall s in state universe, do(do(s,e1),e2)=do(do(s,e2),e1)
  visNC(a,b)      := vis a b  and  ~comm a b
  down(C,e)       := {e} U {x : x -->visNC--> e transitively}
  weakly-closed U := forall a b, vis a b, ~comm a b, b in U => a in U
  loOn(C,ev,x,y)  := (vis x y and ~comm x y)
                     or (~vis x y and ~vis y x and rc x y = Fst
                         and not exists e3 in ev. vis y e3 and ~comm y e3)
  respects pi loOn: x loOn y  =>  x placed before y   (topological sort of loOn)
  Can_C(ev,.)     := folds of the loOn(C,ev)-respecting perms of ev; the datatype
                     CONVERGES on ev iff all such folds agree (unique canonical).

RA-LIN CHECKER (the reused loOn-fold witness, specialised to the Join step).
The master theorem is  Core+Feasible+CD => JoinLemma3 => RA-lin, and #57 refutes
RA-lin exactly by refuting the Join.  So over honest vis-DAGs we check the
JOIN LEMMA on every mergeable pair of weakly-closed sets E1,E2:

    mergeL( sig(E1 & E2), sig(E1), sig(E2) )  must be a canonical state of E1 | E2.

sig(.) is the loOn-fold canonical state (this file's IsCanonicalState).  A single
violation is a non-RA-linearizable countermodel: the merged version's operational
state is no linearization-fold of its event set.  (This is the litmus loOn-fold
RA-lin idiom of rga_byzantine_check.ra_linearizable -- causal fold + convergence
+ compare -- adapted to the conditioned three-way merge and exact-intersection
LCA of stability_vc_check.World.)

PASS+FAIL: every datatype prints its 8-vector (green/red) AND its RA-lin verdict;
expected vectors are HAND-DERIVED in the note and in per-spec comments, never read
off the checker for the same object it judges.

Run:  python3 whiteboard/litmus/vc_minimality_check.py [seed] [trials]
      (defaults seed 114, trials 400).  Exit 0 iff every hand-derived expected
      verdict matches.
"""

import sys
import random
from itertools import combinations, product

# ----------------------------------------------------------------------------
# Op = (ts, rep, appop).  appop is any hashable token (tuples below).
# ----------------------------------------------------------------------------

def ts(e):  return e[0]
def rep(e): return e[1]
def ap(e):  return e[2]

FST, SND, EITHER = "Fst", "Snd", "Either"


class Spec:
    """A conditioned-MRDT signature <Sigma, sigma0, do, mergeL, rc>.

    do(state, event)  -> state
    mergeL(l, a, b)   -> state
    rc(e1, e2)        -> FST | SND | EITHER
    states            -> finite state universe (for comm / VC4 / VC5 enumeration)
    """
    def __init__(self, name, init, do, mergeL, rc, states, appop_events):
        self.name = name
        self.init = init
        self.do = do
        self.mergeL = mergeL
        self.rc = rc
        self._states = states           # callable -> iterable of states
        self._appop_events = appop_events  # callable -> list of representative Ops

    def states(self):
        return list(self._states())

    def appop_events(self):
        return list(self._appop_events())

    def fold(self, seq, s=None):
        s = self.init if s is None else s
        for e in seq:
            s = self.do(s, e)
        return s

    def commutes(self, e1, e2):
        return all(self.do(self.do(s, e1), e2) == self.do(self.do(s, e2), e1)
                   for s in self.states())


# ----------------------------------------------------------------------------
# Configuration: a set of events + a valid vis (strict partial order, same-rep
# total, vis => ts<).  Generated as a random ts-monotone DAG, transitively
# closed, with same-replica pairs forced in.
# ----------------------------------------------------------------------------

class Config:
    def __init__(self, events, vis_pairs):
        self.events = list(events)
        self._vis = set(vis_pairs)          # set of (a,b) with a vis-before b

    def vis(self, a, b):
        return (a, b) in self._vis


def gen_config(spec, rng, n_events, appop_choices, honest_fixup=None):
    """Random valid Configuration over n_events events drawn from appop_choices
    (a list of appop tokens).  ts = 1..n unique; replicas random in {0,1,2}.
    vis: random ts-monotone edges, same-replica forced, transitively closed."""
    n = n_events
    tss = list(range(1, n + 1))
    rng.shuffle(tss)
    events = []
    for i in range(n):
        appop = rng.choice(appop_choices)
        events.append((tss[i], rng.randint(0, 2), appop))
    if honest_fixup is not None:
        events = honest_fixup(events, rng)
    # base edges only low-ts -> high-ts
    order = sorted(events, key=ts)
    vis = set()
    for i in range(len(order)):
        for j in range(i + 1, len(order)):
            a, b = order[i], order[j]
            if rep(a) == rep(b):
                vis.add((a, b))                    # same-replica total
            elif rng.random() < 0.45:
                vis.add((a, b))
    # transitive closure
    changed = True
    evs = order
    while changed:
        changed = False
        for a in evs:
            for b in evs:
                if (a, b) in vis:
                    for c in evs:
                        if (b, c) in vis and (a, c) not in vis:
                            vis.add((a, c)); changed = True
    return Config(events, vis)


# ----------------------------------------------------------------------------
# Core relations: visNC, downset, weak closure, loOn, respecting perms, sigma.
# ----------------------------------------------------------------------------

def visNC(spec, C, a, b):
    return C.vis(a, b) and not spec.commutes(a, b)


def downset(spec, C, e):
    """{e} U {x : x -->visNC--> e transitively}."""
    ds = {e}
    frontier = [e]
    while frontier:
        y = frontier.pop()
        for x in C.events:
            if x not in ds and visNC(spec, C, x, y):
                ds.add(x); frontier.append(x)
    return frozenset(ds)


def weakly_closed(spec, C, ev):
    evset = set(ev)
    for b in evset:
        for a in C.events:
            if a not in evset and visNC(spec, C, a, b):
                return False
    return True


def closed_subsets(spec, C, cap=None):
    """All weakly-closed subsets of C.events (bounded by cap events)."""
    evs = C.events
    if cap is not None and len(evs) > cap:
        return []
    out = []
    for r in range(len(evs) + 1):
        for sub in combinations(evs, r):
            if weakly_closed(spec, C, sub):
                out.append(frozenset(sub))
    return out


def loOn(spec, C, ev, x, y):
    if C.vis(x, y) and not spec.commutes(x, y):
        return True
    if (not C.vis(x, y) and not C.vis(y, x)
            and spec.rc(x, y) == FST
            and not any((e3 in ev) and C.vis(y, e3) and not spec.commutes(y, e3)
                        for e3 in C.events)):
        return True
    return False


def respecting_folds(spec, C, ev):
    """Set of fold results over ALL loOn(C,ev)-respecting perms of ev.
    Empty set iff loOn is cyclic on ev (no canonical state exists)."""
    evl = list(ev)
    # loOn edges restricted to ev
    edges = {(x, y) for x in evl for y in evl
             if x != y and loOn(spec, C, ev, x, y)}
    results = set()
    def rec(placed, remaining):
        if not remaining:
            results.add(spec.fold(placed))
            return
        for y in list(remaining):
            # y placeable iff no un-placed x with loOn(x,y)
            if all((x, y) not in edges for x in remaining if x != y):
                rec(placed + [y], remaining - {y})
    rec([], set(evl))
    return frozenset(results)


class Sigma:
    """Canonical-state oracle with memoisation and convergence tracking."""
    def __init__(self, spec, C):
        self.spec = spec; self.C = C; self._memo = {}

    def folds(self, ev):
        ev = frozenset(ev)
        if ev not in self._memo:
            self._memo[ev] = respecting_folds(self.spec, self.C, ev)
        return self._memo[ev]

    def converges(self, ev):
        f = self.folds(ev)
        return len(f) == 1

    def canon(self, ev):
        """The unique canonical state, or None if non-convergent / cyclic."""
        f = self.folds(ev)
        return next(iter(f)) if len(f) == 1 else None


# ----------------------------------------------------------------------------
# The eight VC checkers.  VC1-4 are universe/pool predicates; VC5-8 are
# config-driven over canonical (loOn-fold) tuples.  Each returns (ok, witness).
# ----------------------------------------------------------------------------

def distinctOps(a, b):        return ts(a) != ts(b)
def differentReplicas(a, b):  return rep(a) != rep(b)


def check_vc1(spec):
    """rc_non_comm_directional: distinct cross-replica o1 o2 =>
       (~comm o1 o2  <->  rc o1 o2 = Fst or rc o2 o1 = Fst)."""
    evs = spec.appop_events()
    for o1, o2 in product(evs, evs):
        if o1 == o2 or not distinctOps(o1, o2) or not differentReplicas(o1, o2):
            continue
        lhs = not spec.commutes(o1, o2)
        rhs = (spec.rc(o1, o2) == FST) or (spec.rc(o2, o1) == FST)
        if lhs != rhs:
            return False, ("VC1", o1, o2, "ncomm=%s rcFst=%s" % (lhs, rhs))
    return True, None


def check_vc2(spec):
    """no_rc_chain: o1!=o2, o2!=o3 => ~(rc o1 o2 = Fst and rc o2 o3 = Fst)."""
    evs = spec.appop_events()
    for o1, o2, o3 in product(evs, evs, evs):
        if not distinctOps(o1, o2) or not distinctOps(o2, o3):
            continue
        if spec.rc(o1, o2) == FST and spec.rc(o2, o3) == FST:
            return False, ("VC2", o1, o2, o3)
    return True, None


def check_vc3(spec, pi_len=2):
    """cond_comm_lift: distinct e e' e''; rc e e' = Fst; ~comm e' e'' =>
       e''(fold(e(e'(s)),pi)) = e''(fold(e'(e(s)),pi)), pi bounded."""
    evs = spec.appop_events()
    states = spec.states()
    pis = [()]
    pool = evs
    for L in range(1, pi_len + 1):
        pis += list(product(pool, repeat=L))
    for e, ep in product(evs, evs):
        if not distinctOps(e, ep) or spec.rc(e, ep) != FST:
            continue
        for epp in evs:
            if not distinctOps(e, epp) or not distinctOps(ep, epp):
                continue
            if spec.commutes(ep, epp):
                continue
            for s in states:
                left0 = spec.do(spec.do(s, ep), e)
                right0 = spec.do(spec.do(s, e), ep)
                for pi in pis:
                    lhs = spec.do(spec.fold(pi, left0), epp)
                    rhs = spec.do(spec.fold(pi, right0), epp)
                    if lhs != rhs:
                        return False, ("VC3", e, ep, epp, s, pi)
    return True, None


def check_vc4(spec):
    """mergeL l a b = mergeL l b a."""
    S = spec.states()
    for l, a, b in product(S, S, S):
        if spec.mergeL(l, a, b) != spec.mergeL(l, b, a):
            return False, ("VC4", l, a, b)
    return True, None


# ---- config-driven VCs (VC5..VC8) : checked over one config -----------------

def is_loOn_maximal(spec, C, ev, e):
    return all(not loOn(spec, C, ev, e, x) for x in ev if x != e)


def vc5_on_config(spec, C, sig, cap_sub=5):
    """feasible_init: Can_C(ev,s) => mergeL init init s = s."""
    evs = C.events
    if len(evs) > cap_sub:
        subs = [downset(spec, C, e) for e in evs] + \
               closed_subsets(spec, C, cap=cap_sub)
    else:
        subs = [frozenset(c) for r in range(len(evs) + 1)
                for c in combinations(evs, r)]
    for ev in subs:
        for s in sig.folds(ev):
            if spec.mergeL(spec.init, spec.init, s) != s:
                return False, ("VC5", ev, s)
    return True, None


def vc8_on_config(spec, C, sig):
    """CDVC3: U weakly-closed, e in U loOn(U)-maximal; A=sig(U-e),
       B=sig(down(e)-e): mergeL B A (e(B)) = e(A)."""
    for U in closed_subsets(spec, C, cap=6):
        for e in U:
            if not is_loOn_maximal(spec, C, U, e):
                continue
            Aset = sig.folds(U - {e})
            Bset = sig.folds(downset(spec, C, e) - {e})
            for A in Aset:
                for B in Bset:
                    if spec.mergeL(B, A, spec.do(B, e)) != spec.do(A, e):
                        return False, ("VC8", U, e, A, B)
    return True, None


def vc6_on_config(spec, C, sig):
    """feasible_local_redistribute."""
    cs = closed_subsets(spec, C, cap=6)
    for E1, E2 in product(cs, cs):
        U = E1 | E2
        for e in E1:
            if e in E2 or not is_loOn_maximal(spec, C, U, e):
                continue
            s0s = sig.folds(E1 & E2)
            Bs = sig.folds(downset(spec, C, e) - {e})
            t1s = sig.folds(E1 - {e})
            s2s = sig.folds(E2)
            for s0, B, t1, s2 in product(s0s, Bs, t1s, s2s):
                u = spec.do(B, e)
                lhs = spec.mergeL(s0, spec.mergeL(B, t1, u), s2)
                rhs = spec.mergeL(B, spec.mergeL(s0, t1, s2), u)
                if lhs != rhs:
                    return False, ("VC6", E1, E2, e)
    return True, None


def vc7_on_config(spec, C, sig):
    """feasible_redistribute."""
    cs = closed_subsets(spec, C, cap=6)
    for E1, E2 in product(cs, cs):
        U = E1 | E2
        for e in E1:
            if e not in E2 or not is_loOn_maximal(spec, C, U, e):
                continue
            t0s = sig.folds((E1 & E2) - {e})
            Bs = sig.folds(downset(spec, C, e) - {e})
            t1s = sig.folds(E1 - {e})
            t2s = sig.folds(E2 - {e})
            for t0, B, t1, t2 in product(t0s, Bs, t1s, t2s):
                u = spec.do(B, e)
                lhs = spec.mergeL(spec.mergeL(B, t0, u), spec.mergeL(B, t1, u),
                                  spec.mergeL(B, t2, u))
                rhs = spec.mergeL(B, spec.mergeL(t0, t1, t2), u)
                if lhs != rhs:
                    return False, ("VC7", E1, E2, e)
    return True, None


def ra_lin_on_config(spec, C, sig):
    """The Join Lemma over every mergeable pair of weakly-closed sets:
       mergeL(sig(E1&E2), sig(E1), sig(E2)) must be a canonical state of E1|E2.
       A failure is the non-RA-linearizable countermodel."""
    cs = closed_subsets(spec, C, cap=6)
    for E1, E2 in combinations_with_self(cs):
        s0s = sig.folds(E1 & E2)
        s1s = sig.folds(E1)
        s2s = sig.folds(E2)
        unionfolds = sig.folds(E1 | E2)
        if not unionfolds:
            continue
        for s0, s1, s2 in product(s0s, s1s, s2s):
            m = spec.mergeL(s0, s1, s2)
            if m not in unionfolds:
                return False, ("RA-lin/Join", E1, E2, s0, s1, s2, m, unionfolds)
    return True, None


def combinations_with_self(xs):
    for i in range(len(xs)):
        for j in range(len(xs)):
            yield xs[i], xs[j]


# ============================================================================
# DATATYPES.  States are frozensets of tags (ts, elem); the OR-shape merge is
#   mergeL(l,a,b) = (l & a & b) | (a - l) | (b - l)   (pointwise (l&a&b)|(a\l)|(b\l))
# Boundary anchors (ORSet, MVR) then minimal-mutation separators.
# ============================================================================

def orshape(l, a, b):
    return (l & a & b) | (a - l) | (b - l)


def orset_do(s, e):
    t, r, op = e
    kind, x = op
    if kind == 'add':
        return s | {(t, x)}
    else:                          # rem x : kill every tag of element x
        return frozenset(p for p in s if p[1] != x)


def orset_rc(e1, e2):
    (_, _, (k1, x1)), (_, _, (k2, x2)) = e1, e2
    if k1 == 'add' and k2 == 'rem' and x1 == x2:
        return SND
    if k1 == 'rem' and k2 == 'add' and x1 == x2:
        return FST
    return EITHER


def orset_rc_either(e1, e2):
    return EITHER


TAGDOM = [(t, x) for t in (1, 2) for x in (0, 1)]
def orset_states():
    from itertools import chain
    for r in range(len(TAGDOM) + 1):
        for c in combinations(TAGDOM, r):
            yield frozenset(c)

ORSET_APPCHOICES = [('add', 0), ('add', 1), ('rem', 0), ('rem', 1)]
def orset_pool():
    return [(1, 0, ('add', 0)), (2, 1, ('rem', 0)), (3, 0, ('add', 1)),
            (4, 1, ('rem', 1)), (5, 0, ('rem', 0)), (6, 1, ('add', 0))]


def make_orset():
    return Spec("ORSet (boundary anchor)", frozenset(), orset_do, orshape,
                orset_rc, orset_states, orset_pool)


# ---- MVR: grow-only accumulate (all ops commute), OR-shape merge ------------
# write v at ts mints tag (ts, v); state grows only, so all writes commute.
def mvr_do(s, e):
    t, r, op = e
    _, v = op                      # ('wr', v)
    return s | {(t, v)}

def mvr_rc(e1, e2):
    return EITHER

MVR_APPCHOICES = [('wr', 0), ('wr', 1)]
def mvr_pool():
    return [(1, 0, ('wr', 0)), (2, 1, ('wr', 1)), (3, 0, ('wr', 1)),
            (4, 1, ('wr', 0))]

def make_mvr():
    return Spec("MVR (boundary anchor, all-commuting)", frozenset(), mvr_do,
                orshape, mvr_rc, orset_states, mvr_pool)


# ============================================================================
# SEPARATORS.  Each is a minimal mutation of a boundary datatype designed to
# break exactly one VC.  Hand-derived expected 8-vector + RA-lin verdict live
# beside each (and in the note).  do/mergeL/rc noted where mutated.
# ============================================================================

# ---- VC1 candidate A: ORSet with rc := Either (drop add-wins arbitration) ---
# Breaks VC1 (add x / rem x non-comm but rc Either).  add-wins merge is
# SELF-WITNESSING (rem-before-add always folds to the merge's "live"), so RA-lin
# may survive -- the harness decides.
def make_vc1_orset_either():
    return Spec("VC1?  ORSet, rc:=Either", frozenset(), orset_do, orshape,
                orset_rc_either, orset_states, orset_pool)

# ---- VC1 candidate B: G-Set (add-only) with a SPURIOUS rc=Fst on a comm pair.
# Breaks VC1 (<= direction: rc orders a commuting add/add pair).  All adds
# commute so folds converge regardless -> expected RA-lin TRUE.
def gset_do(s, e):
    t, r, op = e
    _, x = op
    return s | {(t, x)}
def gset_rc_spurious(e1, e2):
    (_, _, (k1, x1)), (_, _, (k2, x2)) = e1, e2
    # order add-0 before add-1 spuriously (they commute)
    if x1 == 0 and x2 == 1:
        return FST
    return EITHER
def gset_pool():
    return [(1, 0, ('add', 0)), (2, 1, ('add', 1)), (3, 0, ('add', 1)),
            (4, 1, ('add', 0))]
def make_vc1_gset_spurious():
    return Spec("VC1?  G-Set, spurious rc(add0,add1)=Fst", frozenset(),
                gset_do, orshape, gset_rc_spurious, orset_states, gset_pool)


# ---- VC2 separator: LWW register with rc = "order by timestamp" -------------
# State = (ts, val), init (0, 0).  do(s, wr_v @ (t,r)) = (t, v)  (overwrite,
# recording the writer's timestamp).  mergeL = max by ts (LWW, drop LCA slot).
# rc(e1, e2) = Fst iff ts(e1) < ts(e2).  This rc orders EVERY pair by timestamp
# (agreeing with vis / program order), so t1<t2<t3 is an rc CHAIN -> VC2 RED.
# Yet loOn = the timestamp total order is acyclic, the register converges, and
# max-ts merge reproduces sigma(union) = the ts-latest write, so RA-lin holds.
# A textbook LWW register whose natural rc chains.  Hand-derived expected:
#   VC2 RED, VC1/VC3/VC4/VC5/VC6/VC7/VC8 GREEN, RA-lin TRUE  (weakenability:
#   no_rc_chain is sufficient-but-not-necessary; loOn-acyclicity is what is used).
def lww_do(s, e):
    t, r, (_, v) = e
    return (t, v)                        # overwrite, record ts
def lww_merge(l, a, b):
    return max(a, b)                      # lex-max (ts dominates); symmetric
def lww_rc(e1, e2):
    return FST if e1[0] < e2[0] else EITHER
def lww_states():
    return [(t, v) for t in range(4) for v in range(4)]
def lww_pool():
    return [(1, 0, ('wr', 1)), (2, 1, ('wr', 2)), (3, 0, ('wr', 3)),
            (4, 1, ('wr', 1)), (5, 2, ('wr', 2)), (6, 0, ('wr', 3))]
LWW_APPCHOICES = [('wr', 1), ('wr', 2), ('wr', 3)]
def make_vc2_lww():
    return Spec("VC2?  LWW register, rc=order-by-timestamp", (0, 0),
                lww_do, lww_merge, lww_rc, lww_states, lww_pool)


# ---- VC4 candidate: ORSet, mergeL asymmetric ONLY on an UNREACHABLE state ----
# Bias toward a exactly when a carries the SENTINEL tag (0, 9).  do never mints
# a ts-0 tag (minted ts >= 1), so no canonical / reachable state ever contains
# it: the asymmetry is invisible to every config VC and to RA-lin, yet VC4
# (unconditional over the state universe, which includes the sentinel) sees it.
#   VC4 RED, VC1/VC2/VC3/VC5/VC6/VC7/VC8 GREEN, RA-lin TRUE  (redundancy witness:
#   mergeL_comm is only needed on canonical tuples, where the union forces it).
SENT = (0, 9)
def asym_sentinel_merge(l, a, b):
    if SENT in a and SENT not in b:
        return (l & a & b) | (a - l)     # drop b's news: asymmetric
    return orshape(l, a, b)
def orset_states_sent():
    dom = TAGDOM + [SENT]
    for r in range(len(dom) + 1):
        for c in combinations(dom, r):
            yield frozenset(c)
def make_vc4_sentinel():
    return Spec("VC4?  ORSet, mergeL asym only on unreachable sentinel tag",
                frozenset(), orset_do, asym_sentinel_merge, orset_rc,
                orset_states_sent, orset_pool)

# ---- VC4 co-failure control: drop b's news everywhere (breaks VC5 too) -------
def drop_b_merge(l, a, b):
    return (l & a & b) | (a - l)
def make_vc4_dropb():
    return Spec("VC4x  ORSet, mergeL:=(l&a&b)|(a-l) (drop b, control)",
                frozenset(), orset_do, drop_b_merge, orset_rc, orset_states,
                orset_pool)


# ---- VC5 candidate: ORSet, mergeL LOSES a tag on the empty-LCA/empty-branch --
# corner with |b|>=2.  feasible_init is the E1=empty Join instance
# mergeL(init,init,sigma(E2)) = sigma(E2); breaking it on a >=2-tag canonical s
# breaks the Join at E1=empty while CD's pattern mergeL(B,A,e(B)) with a single-
# event e(B) (|.|=1) never triggers the >=2 guard.  Hand-derived expected:
#   VC5 RED, VC1..4/VC8 GREEN, RA-lin FALSE   (INDEPENDENCE witness for VC5).
def lossy_init_merge(l, a, b):
    if l == frozenset() and a == frozenset() and len(b) >= 2:
        return frozenset(sorted(b)[:-1])   # drop the largest tag
    return orshape(l, a, b)
def make_vc5_lossy():
    return Spec("VC5   ORSet, mergeL loses a tag on empty-LCA |b|>=2",
                frozenset(), orset_do, lossy_init_merge, orset_rc,
                orset_states, orset_pool)


# ---- VC6/VC7 attempts: perturb the OR-shape on a specific redistribute shape.
# The OR-shape satisfies BOTH feasible delta laws unconditionally (Boolean
# tautologies), so isolating VC6 or VC7 needs a non-ACI merge that still meets
# init + CD.  Candidate: OR-shape but on merges whose THIRD argument strictly
# contains its FIRST (the delta-application slot u = e(B) with B<u), inject an
# asymmetry between the local-redistribute and redistribute shapes.  Reported
# as evidence (see note); the OR-shape control confirms both hold for it.
def make_vc6_probe():
    # merge that keeps b's tags only if they are also in a: (l&a&b)|(a-l)|(a&b-l)
    def m(l, a, b):
        return (l & a & b) | (a - l) | ((a & b) - l)
    return Spec("VC6?  ORSet, mergeL biased (a-gated b-news)", frozenset(),
                orset_do, m, orset_rc, orset_states, orset_pool)


# ---- VC7 separator: the DOUBLE-COUNTING counter (merge ignores the LCA slot).
# State = a count in N, init 0.  do(s, inc) = s+1 (ALL incs commute, rc=Either).
# mergeL(l,a,b) = a + b  -- the LCA slot l is DROPPED (not subtracted).  This is
# the delta-counter with its "- l" cancellation removed, so the shared history is
# double-counted at a merge.  redistribute (VC7) is exactly the law whose proof
# needs that cancellation (the duplicated LCA slot must collapse); it fails
# (a+2u vs a+u).  local_redistribute (VC6) is LINEAR and survives; feasible_init
# (0+s=s), merge symmetry, and CD (all-commuting => downset empty => B=0, so
# merge(0,A,A+1)=A+1=do(A,e)) all hold.  Hand-derived expected:
#   VC7 RED, VC1..VC6/VC8 GREEN, RA-lin FALSE  (INDEPENDENCE witness, the dual of
#   AWSetF3: CD holds but the delta law fails, vs AWSetF3 where the delta laws
#   hold but CD fails).
def dcc_do(s, e):
    return s + 1
def dcc_merge(l, a, b):
    return a + b                          # drop LCA slot -> double-counts
def dcc_states():
    return [0, 1, 2, 3, 4]
def dcc_pool():
    return [(1, 0, ('inc',)), (2, 1, ('inc',)), (3, 0, ('inc',)),
            (4, 1, ('inc',))]
DCC_APPCHOICES = [('inc',)]
def make_vc7_dcc():
    return Spec("VC7   double-counting counter, mergeL(l,a,b)=a+b", 0,
                dcc_do, dcc_merge, lambda e1, e2: EITHER, dcc_states, dcc_pool)


# ---- VC3 attempt: an accumulate datatype where an rc-ordered swap is VISIBLE.
# Register overwrites make cond_comm_lift hold trivially (final e'' overwrites);
# to break VC3 the swap of an rc-ordered pair must survive under a later non-
# commuting e''.  Candidate reported as evidence.
def make_vc3_probe():
    # ORSet with rc forced Fst on add-then-rem SAME element (wrong direction):
    # rc(add x, rem x) = Fst.  Then cond_comm_lift premise rc(e,e')=Fst fires on
    # (add x, rem x); e''=add x is non-commuting with rem x; the swap add;rem vs
    # rem;add IS visible (add-wins vs removed).
    def rc(e1, e2):
        (_, _, (k1, x1)), (_, _, (k2, x2)) = e1, e2
        if k1 == 'add' and k2 == 'rem' and x1 == x2:
            return FST
        if k1 == 'rem' and k2 == 'add' and x1 == x2:
            return SND
        return EITHER
    return Spec("VC3?  ORSet, rc(add x, rem x)=Fst (reversed)", frozenset(),
                orset_do, orshape, rc, orset_states, orset_pool)


# ---- VC8 separator: AWSetF3, FAITHFUL to Sal/CRDTs/Metatheory/Assoc_Counter- --
# Model.lean (the #57 separator).  Single implicit key.  State = (added, dead,
# flag).  add e -> (added | {e.ts}, dead, True);  rem e -> (added, added|dead,
# False).  mergeL drops the LCA slot: pairwise UNION with OR-flag (a bounded
# ACI semilattice, so DeltaVCs3 holds unconditionally).  rc(rem,add)=Fst,
# rc(add,rem)=Snd, else Either (so VC1..VC7 GREEN, per AWSetF_coreVCs +
# AWSetF_latticeVCs).  The flag is DEFLATIONARY under rem, so CDVC3 (VC8) fails
# at a maximal rem: merge keeps flag True (from an add branch), do writes False.
#   Hand-derived expected: VC1..VC7 GREEN, VC8 RED, RA-lin FALSE (INDEPENDENT).
def awf_do(s, e):
    added, dead, flag = s
    t, r, (kind,) = e[0], e[1], (e[2][0],)  # op token is ('add',) or ('rem',)
    if kind == 'add':
        return (added | {t}, dead, True)
    else:
        return (added, added | dead, False)
def awf_merge(l, a, b):            # drop LCA slot l: pairwise union + OR flag
    (aa, da, fa), (ab, db, fb) = a, b
    return (aa | ab, da | db, fa or fb)
def awf_rc(e1, e2):
    (k1,), (k2,) = (e1[2][0],), (e2[2][0],)
    if k1 == 'rem' and k2 == 'add':
        return FST
    if k1 == 'add' and k2 == 'rem':
        return SND
    return EITHER
def awf_states():
    dom = [1, 2]
    for ra in range(len(dom) + 1):
        for ca in combinations(dom, ra):
            for rd in range(len(dom) + 1):
                for cd in combinations(dom, rd):
                    for fl in (False, True):
                        yield (frozenset(ca), frozenset(cd), fl)
AWF_APPCHOICES = [('add',), ('rem',)]
def awf_pool():
    return [(1, 0, ('add',)), (2, 1, ('rem',)), (3, 0, ('add',)),
            (4, 1, ('rem',)), (5, 0, ('add',)), (6, 2, ('rem',))]
def make_vc8_awsetf():
    return Spec("VC8   AWSetF3 (the #57 separator, faithful)",
                (frozenset(), frozenset(), False),
                awf_do, awf_merge, awf_rc, awf_states, awf_pool)


# ============================================================================
# DRIVER
# ============================================================================

VCNAMES = {1: "rc_noncomm", 2: "no_rc_chain", 3: "cond_comm", 4: "mergeL_comm",
           5: "feas_init", 6: "feas_lredist", 7: "feas_redist", 8: "CDVC3"}


def evaluate(spec, appchoices, n_events, rng, trials, honest_fixup=None):
    """Return (vec, rademo, conv, witnesses) where vec[i] in {'G','R'}."""
    vec = {}
    wit = {}
    ok1, w1 = check_vc1(spec); vec[1] = 'G' if ok1 else 'R'; wit[1] = w1
    ok2, w2 = check_vc2(spec); vec[2] = 'G' if ok2 else 'R'; wit[2] = w2
    ok3, w3 = check_vc3(spec); vec[3] = 'G' if ok3 else 'R'; wit[3] = w3
    ok4, w4 = check_vc4(spec); vec[4] = 'G' if ok4 else 'R'; wit[4] = w4
    # config-driven VCs
    for i in (5, 6, 7, 8):
        vec[i] = 'G'
    ra = 'RALIN'; conv = True
    for _ in range(trials):
        C = gen_config(spec, rng, n_events, appchoices, honest_fixup)
        sig = Sigma(spec, C)
        # convergence over closed subsets
        for ev in closed_subsets(spec, C, cap=6):
            f = sig.folds(ev)
            if len(f) > 1:
                conv = False
        for i, fn in ((5, vc5_on_config), (6, vc6_on_config),
                      (7, vc7_on_config), (8, vc8_on_config)):
            if vec[i] == 'G':
                ok, w = fn(spec, C, sig)
                if not ok:
                    vec[i] = 'R'; wit[i] = w
        if ra == 'RALIN':
            ok, w = ra_lin_on_config(spec, C, sig)
            if not ok:
                ra = 'NONRA'; wit['RA'] = w
    return vec, ra, conv, wit


def fmt_vec(vec):
    cells = []
    for i in range(1, 9):
        cells.append("VC%d:%s" % (i, vec[i]))
    return " ".join(cells)


def short(x, n=90):
    s = str(x)
    return s if len(s) <= n else s[:n] + "..."


REGISTRY = [
    # (make, appchoices, n_events, tag, expected_reds, expected_ra)
    (make_orset,             ORSET_APPCHOICES,       5, "anchor", [],        'RALIN'),
    (make_mvr,               MVR_APPCHOICES,         4, "anchor", [],        'RALIN'),
    (make_vc1_gset_spurious, [('add',0),('add',1)],  5, "VC1",    [1],       'RALIN'),
    (make_vc1_orset_either,  ORSET_APPCHOICES,       5, "VC1x",   None,      None),
    (make_vc2_lww,           LWW_APPCHOICES,         5, "VC2",    [2],       'RALIN'),
    (make_vc3_probe,         ORSET_APPCHOICES,       5, "VC3",    None,      None),
    (make_vc4_sentinel,      ORSET_APPCHOICES,       5, "VC4",    [4],       'RALIN'),
    (make_vc4_dropb,         ORSET_APPCHOICES,       5, "VC4x",   None,      None),
    (make_vc5_lossy,         ORSET_APPCHOICES,       5, "VC5",    None,      None),
    (make_vc6_probe,         ORSET_APPCHOICES,       5, "VC6",    None,      None),
    (make_vc7_dcc,           DCC_APPCHOICES,         4, "VC7",    [7],       'NONRA'),
    (make_vc8_awsetf,        AWF_APPCHOICES,         5, "VC8",    [8],       'NONRA'),
]


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 114
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    print("# VC minimality sweep  (seed=%d trials=%d)\n" % (seed, trials))
    mismatches = 0
    for make, appch, n_ev, tag, exp_reds, exp_ra in REGISTRY:
        rng = random.Random(seed)
        spec = make()
        vec, ra, conv, wit = evaluate(spec, appch, n_ev, rng, trials)
        reds = [i for i in range(1, 9) if vec[i] == 'R']
        print("[%s]  %s" % (tag, spec.name))
        print("   " + fmt_vec(vec))
        print("   RA-lin: %-7s  converges: %s  reds: %s"
              % (ra, conv, reds if reds else "none"))
        for i in reds:
            print("     - VC%d witness: %s" % (i, short(wit.get(i))))
        if ra == 'NONRA':
            print("     - RA-lin countermodel: %s" % short(wit.get('RA'), 140))
        # compare to hand-derived expected verdict (None = probe, no assertion)
        if exp_reds is not None:
            ok = (reds == sorted(exp_reds)) and (ra == exp_ra)
            print("   EXPECTED reds=%s RA=%s  -> %s"
                  % (exp_reds, exp_ra, "MATCH" if ok else "*** MISMATCH ***"))
            if not ok:
                mismatches += 1
        print()
    print("# mismatches vs hand-derived expected: %d" % mismatches)
    sys.exit(1 if mismatches else 0)


if __name__ == "__main__":
    main()
