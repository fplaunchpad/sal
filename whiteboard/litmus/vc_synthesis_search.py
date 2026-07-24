#!/usr/bin/env python3
"""vc_synthesis_search.py -- task #114 phase 1b: SYNTHESIS SEARCH over tiny
tabulated datatype specs, resolving the three UNRESOLVED VCs of the phase-1
minimality sweep (VC3 cond_comm_lift, VC5 feasible_init, VC6
feasible_local_redistribute).

Phase 1 (vc_minimality_check.py) probed by MUTATING boundary datatypes; that
cannot find witnesses whose violation is structurally entangled with the
mutated component.  This file replaces mutation by systematic SYNTHESIS:

  spec = <Sigma = {0..k-1}, init = 0, do = per-kind table Sigma -> Sigma,
          mergeL = symmetric table Sigma^3 -> Sigma, rc = kind-pair table>

and scans whole spaces of such specs for the target vectors
"VC_i red, the other seven green" using the phase-1 checkers unchanged
(imported, not rebuilt), then runs the phase-1 loOn-fold RA-lin oracle on the
survivors.  A survivor that is non-RA-linearizable is an INDEPENDENCE witness
for VC_i; an RA-linearizable survivor is a weakenability witness (the VC as
stated is stronger than adequacy needs).

SEARCH SPACES (bounds are exact and printed by the run):

  S2x2  k=2 states, 2 op kinds, EXHAUSTIVE:
        do-tables: all 4^2 = 16 ordered pairs from {c0, id, not, c1};
        mergeL:    all 64 branch-symmetric tables ({0,1}^(2 x 3 cells));
        rc:        derived from kind-commutativity (VC1-green by
                   construction): comm pair -> Either; non-comm -> Fst or Snd.
        <= 2048 specs, every one visited.
  S2x3  k=2 states, 3 op kinds, EXHAUSTIVE: 4^3 = 64 do-triples x 64 merges
        x rc assignments per cross pair (<= 8, kind-level rc-chains pruned =
        VC2-green by construction).  This is where cond_comm_lift's premise
        (rc e e' = Fst plus a THIRD non-commuting kind) has room.
  S3    k=3 states, 2 op kinds, GUIDED: curated 8-table do-pool (64 pairs) x
        (9 structured l-using merges + all 27 l-free commutative unital
        magmas + budgeted random symmetric tables) x derived rc.
        NOT exhaustive; the bound is printed.

CALIBRATION (mandatory): the searcher must RE-FIND, inside S2x2, from
scratch, (a) a VC8-only non-RA-lin spec matching the minimized AWSetF3
(enable-wins flag: add=c1, rem=c0, mergeL = a|b LCA-dropped, rc rem-first)
and (b) a VC7-only non-RA-lin spec matching the mod-2 parity counter
(do = not, mergeL = a xor b LCA-dropped).  Both are hand-derived below and
verified PASS+FAIL against the phase-1 checkers.  Without this calibration a
"found nothing" verdict for VC3/VC6 would be meaningless.

LIMITS of the space (stated, not hidden): do is a function of the op KIND
only (no timestamp minting, so tag-based datatypes like ORSet are outside);
mergeL is branch-symmetric by construction (VC4-green corner cut); rc is a
function of the kind pair.  "No witness in these spaces" is EVIDENCE for
derivability at the stated bounds, never proof.

Run:  python3 whiteboard/litmus/vc_synthesis_search.py [--full] [seed]
      default: S2x2 + named-spec selfcheck (fast); --full adds S2x3 and S3.
      Exit 0 iff every hand-derived expectation matches and calibration
      re-finds both dual-core witnesses.
"""

import os
import sys
import random
from itertools import combinations, product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from vc_minimality_check import (
    Spec, gen_config, Sigma, closed_subsets,
    check_vc1, check_vc2, check_vc3, check_vc4,
    vc5_on_config, vc6_on_config, vc7_on_config, vc8_on_config,
    ra_lin_on_config, FST, SND, EITHER, ap,
)

# ----------------------------------------------------------------------------
# Tabulated specs.  appop token = (kind_index,).
# ----------------------------------------------------------------------------

def _pool_for(nkinds):
    """Event pool for the universe checkers VC1..VC3: two+ replicas per kind,
    distinct timestamps, cross-replica pairs of every kind combination."""
    if nkinds == 1:
        return [(1, 0, (0,)), (2, 1, (0,)), (3, 2, (0,)), (4, 0, (0,))]
    if nkinds == 2:
        return [(1, 0, (0,)), (2, 1, (0,)), (3, 0, (1,)), (4, 1, (1,)),
                (5, 2, (0,)), (6, 2, (1,))]
    return [(1, 0, (0,)), (2, 1, (0,)), (3, 0, (1,)), (4, 1, (1,)),
            (5, 0, (2,)), (6, 1, (2,))]


class TabSpec(Spec):
    """<Sigma = range(k), init = 0, tabulated do/mergeL, kind-pair rc>."""

    def __init__(self, name, k, do_tables, merge_cells, rc_pairs):
        # do_tables: tuple of tuples, do_tables[kind][s] = new state
        # merge_cells: dict {(l, lo, hi): v} on unordered branch pairs
        # rc_pairs: dict {(k1, k2): FST|SND|EITHER} on ordered kind pairs
        self.k = k
        self.do_tables = tuple(tuple(t) for t in do_tables)
        self.merge_cells = dict(merge_cells)
        self.rc_pairs = dict(rc_pairs)
        self.appchoices = [(i,) for i in range(len(do_tables))]
        self._comm_cache = {}

        def do(s, e):
            return self.do_tables[e[2][0]][s]

        def mergeL(l, a, b):
            lo, hi = (a, b) if a <= b else (b, a)
            return self.merge_cells[(l, lo, hi)]

        def rc(e1, e2):
            return self.rc_pairs.get((e1[2][0], e2[2][0]), EITHER)

        Spec.__init__(self, name, 0, do, mergeL, rc,
                      lambda: range(k), lambda: _pool_for(len(do_tables)))

    def commutes(self, e1, e2):
        key = (ap(e1)[0], ap(e2)[0])
        if key not in self._comm_cache:
            t1 = self.do_tables[key[0]]
            t2 = self.do_tables[key[1]]
            self._comm_cache[key] = all(
                t2[t1[s]] == t1[t2[s]] for s in range(self.k))
        return self._comm_cache[key]

    def signature(self):
        """Canonical form modulo kind renaming: sort the kinds by do-table,
        carrying the rc table through the permutation."""
        n = len(self.do_tables)
        perm = sorted(range(n), key=lambda i: self.do_tables[i])
        do_sorted = tuple(self.do_tables[i] for i in perm)
        inv = {old: new for new, old in enumerate(perm)}
        rc_sorted = tuple(sorted((inv[a], inv[b], v)
                                 for (a, b), v in self.rc_pairs.items()
                                 if v != EITHER))
        cells = tuple(sorted(self.merge_cells.items()))
        return (self.k, do_sorted, rc_sorted, cells)

    def describe(self):
        dt = ",".join("".join(str(x) for x in t) for t in self.do_tables)
        fs = ";".join("%d>%d:%s" % (a, b, v[0])
                      for (a, b), v in sorted(self.rc_pairs.items())
                      if v != EITHER)
        mc = "".join(str(v) for _, v in sorted(self.merge_cells.items()))
        return "k=%d do=[%s] rc=[%s] M=%s" % (self.k, dt, fs or "E", mc)


def kind_comm(t1, t2, k):
    return all(t2[t1[s]] == t1[t2[s]] for s in range(k))


def sym_merge_tables(k):
    """All branch-symmetric merge tables as merge_cells dicts (k=2: 64)."""
    cells = [(l, lo, hi) for l in range(k)
             for lo in range(k) for hi in range(lo, k)]
    for vals in product(range(k), repeat=len(cells)):
        yield dict(zip(cells, vals))


def rc_choices(do_tables, k):
    """All rc kind-pair tables that keep VC1 and VC2 green by construction:
    non-comm cross pair -> Fst one way or the other; comm pair -> Either;
    same kind -> Either (same-kind ops share a table, hence commute);
    kind-level Fst chains pruned (VC2)."""
    n = len(do_tables)
    cross = [(i, j) for i in range(n) for j in range(i + 1, n)]
    optlists = []
    for (i, j) in cross:
        if kind_comm(do_tables[i], do_tables[j], k):
            optlists.append([None])
        else:
            optlists.append([(i, j), (j, i)])   # winner declared first
    for choice in product(*optlists):
        table = {}
        firsts = set()
        for c in choice:
            if c is None:
                continue
            table[c] = FST
            table[(c[1], c[0])] = SND
            firsts.add(c)
        # kind-level rc chain: rc(a,b)=Fst and rc(b,c)=Fst
        if any((b, c) in firsts for (a, b) in firsts for (bb, c) in firsts
               if b == bb):
            continue
        yield table


# ----------------------------------------------------------------------------
# Scan machinery: cheap universe checkers first, then config-driven VCs with
# early abort at two distinct reds, then a multi-seed confirmation pass and
# the RA-lin oracle for exactly-one-red survivors.
# ----------------------------------------------------------------------------

CONFIG_FNS = ((5, vc5_on_config), (8, vc8_on_config),
              (6, vc6_on_config), (7, vc7_on_config))


def cheap_reds(spec):
    reds = []
    for i, fn in ((1, check_vc1), (2, check_vc2), (3, check_vc3),
                  (4, check_vc4)):
        ok, _ = fn(spec)
        if not ok:
            reds.append(i)
        if len(reds) >= 2:
            break
    return reds


def config_reds(spec, seed, budget, n_events, reds0):
    """Config-driven VC5..VC8 over `budget` random honest DAGs; aborts as
    soon as two distinct VCs are red (the vector cannot be one-red)."""
    reds = set(reds0)
    rng = random.Random(seed)
    wits = {}
    for _ in range(budget):
        C = gen_config(spec, rng, n_events, spec.appchoices)
        sig = Sigma(spec, C)
        for i, fn in CONFIG_FNS:
            if i in reds:
                continue
            ok, w = fn(spec, C, sig)
            if not ok:
                reds.add(i)
                wits[i] = w
        if len(reds) >= 2:
            return reds, wits
    return reds, wits


def ra_all_violations(spec, C, sig):
    """Every Join violation on this config (the phase-1 oracle logs only the
    first): list of (E1, E2, merged, unionfolds)."""
    out = []
    cs = closed_subsets(spec, C, cap=6)
    for E1 in cs:
        for E2 in cs:
            s0s = sig.folds(E1 & E2)
            s1s = sig.folds(E1)
            s2s = sig.folds(E2)
            uf = sig.folds(E1 | E2)
            if not uf:
                continue
            for s0, s1, s2 in product(s0s, s1s, s2s):
                m = spec.mergeL(s0, s1, s2)
                if m not in uf:
                    out.append((E1, E2, m, uf))
    return out


def confirm(spec, seeds=(114, 7, 2026), budgets=((20, 4), (10, 5))):
    """Full re-evaluation: reds over all eight VCs, RA-lin verdict,
    convergence, and the set of Join-violation shapes (for the VC5
    empty-corner classification)."""
    reds = set(cheap_reds(spec))
    ra = 'RALIN'
    conv = True
    viol_shapes = set()
    for seed in seeds:
        rng = random.Random(seed)
        for budget, n_ev in budgets:
            for _ in range(budget):
                C = gen_config(spec, rng, n_ev, spec.appchoices)
                sig = Sigma(spec, C)
                for ev in closed_subsets(spec, C, cap=6):
                    if len(sig.folds(ev)) > 1:
                        conv = False
                for i, fn in CONFIG_FNS:
                    if i not in reds:
                        ok, _ = fn(spec, C, sig)
                        if not ok:
                            reds.add(i)
                vs = ra_all_violations(spec, C, sig)
                if vs:
                    ra = 'NONRA'
                    for (E1, E2, _, _) in vs:
                        viol_shapes.add((len(E1), len(E2)))
    return sorted(reds), ra, conv, sorted(viol_shapes)


# ----------------------------------------------------------------------------
# Table shorthands for k=2:  do-tables over {0,1}.
# ----------------------------------------------------------------------------

C0, ID2, NOT2, C1 = (0, 0), (0, 1), (1, 0), (1, 1)


def or_cells():
    """mergeL(l,a,b) = a|b, LCA slot dropped (the bounded-lattice shape)."""
    return {(l, lo, hi): (lo | hi) for l in (0, 1)
            for lo in (0, 1) for hi in range(lo, 2)}


def xor_cells():
    """mergeL(l,a,b) = a^b, LCA slot dropped (parity counter, no -l)."""
    return {(l, lo, hi): (lo ^ hi) for l in (0, 1)
            for lo in (0, 1) for hi in range(lo, 2)}


def xor3_cells():
    """mergeL(l,a,b) = a^b^l (the honest mod-2 delta counter: a+b-l)."""
    return {(l, lo, hi): (lo ^ hi ^ l) for l in (0, 1)
            for lo in (0, 1) for hi in range(lo, 2)}


def poisoned_or_cells():
    """a|b except mergeL(0,0,0) := 1: the unit law broken EXACTLY at the
    all-init corner (the merge of two fresh replicas)."""
    cells = or_cells()
    cells[(0, 0, 0)] = 1
    return cells


# ----------------------------------------------------------------------------
# NAMED SPECS with hand-derived expected verdicts (PASS+FAIL: each carries
# its expected red set, RA verdict, and where relevant a negative companion
# pinning the tempting degenerate reading).  Expectations are derived in the
# comments, never read off the checkers.
# ----------------------------------------------------------------------------

def make_ewflag2():
    """CALIBRATION (VC8).  Minimized AWSetF3: add = c1, rem = c0, mergeL =
    a|b (LCA dropped), rc(rem, add) = Fst (rem loses: add-wins).
    Hand-derivation: VC1 (add,rem non-comm, rc directional) green; VC2 (only
    Fst edge is rem->add, no chain) green; VC3 (every e'' ends both sides,
    and both kinds are constant maps, so the final op erases the swap) green;
    VC4 (a|b symmetric) green; VC5 (0|s = s) green; VC6/VC7 (a|b is ACI with
    unit, LCA-free: rearrangement identities) green.  VC8 RED: U = {add, rem}
    with vis add -> rem (visNC since they do not commute): rem is loOn-maximal,
    A = sig({add}) = 1, B = sig(downset(rem)-rem) = sig({add}) = 1, so
    mergeL(B, A, rem(B)) = 1|1|0 = 1 but rem(A) = 0.  Join fails at
    E1 = {add}, E2 = {add, rem}: mergeL(1, 1, 0) = 1 not in folds(U) = {0}.
    Expected: reds [8], NONRA."""
    return TabSpec("EWFlag2 (minimized AWSetF3)", 2, (C1, C0),
                   or_cells(), {(1, 0): FST, (0, 1): SND})


def make_parity():
    """CALIBRATION (VC7).  Mod-2 parity counter: do = not (self-commuting),
    mergeL = a^b with the LCA slot DROPPED (not subtracted), rc = Either.
    Hand-derivation: VC1..VC3 vacuous-green (single kind, commuting, no rc);
    VC4 green (xor symmetric); VC5 green (0^s = s); VC6 green (xor is
    associative-commutative, LCA-free: both sides = t1^u^s2); VC8 green (all
    ops commute so every punctured downset is empty, B = 0, and
    mergeL(0, A, not(0)) = A^1 = not(A)).  VC7 RED: with E1 = E2 = {e},
    t0 = t1 = t2 = 0, B = 0, u = 1: LHS = (t1^u)^(t2^u) = 0 but
    RHS = (t0^t1^t2)^u = 1 (the duplicated delta cancels itself mod 2 on the
    left, is counted once on the right).  Join fails at E1 = E2 = {e}:
    mergeL(1,1,1) = 0 not in folds({e}) = {1}.  Expected: reds [7], NONRA.
    This is the mod-2 shadow of the phase-1 double-counting counter."""
    return TabSpec("Parity counter (mergeL = a^b, LCA dropped)", 2,
                   (NOT2,), xor_cells(), {})


def make_delta_xor():
    """CONTROL (negative companion to Parity): the SAME datatype with the
    honest delta merge a^b^l (= a+b-l mod 2).  Every VC and the Join close:
    the LCA slot cancels the duplicate.  Expected: reds [], RALIN."""
    return TabSpec("Delta counter mod 2 (mergeL = a^b^l)", 2,
                   (NOT2,), xor3_cells(), {})


def make_poisoned_empty():
    """THE VC5 SEPARATOR.  G-set-style: do = c1 (mint the one element),
    mergeL = a|b EXCEPT mergeL(0,0,0) := 1, rc = Either.
    Hand-derivation: VC1..VC3 vacuous-green (single kind, commuting); VC4
    green (the poisoned cell is on the diagonal, table symmetric); VC8 green
    (u = e(B) = 1 always, so the CD tuple (B, A, 1) never hits (0,0,0), and
    mergeL(B, A, 1) = 1 = e(A)); VC6 green (LHS = (t1|u)|s2 = 1 since u = 1;
    RHS-inner mergeL(s0,t1,s2) is 0, 1, or the junk-free poisoned value 1,
    and outer |u = 1 either way); VC7 green (same collapse: every side = 1).
    VC5 RED at exactly ev = {} (s = init): mergeL(0,0,0) = 1 != 0; at every
    nonempty canonical s = 1: mergeL(0,0,1) = 1 green.  RA-lin: the ONLY
    Join violation is E1 = E2 = {} (two fresh replicas merge to junk 1,
    folds({}) = {0}); every other pair has a nonempty side, hence a 1
    somewhere, and the or-merge lands on sig(union) = 1.
    Expected: reds [5], NONRA, all Join violations of shape (0, 0).
    NEGATIVE COMPANION: the same spec with the poison removed (pure a|b) is
    all-green RALIN -- the redness comes from the empty corner alone."""
    return TabSpec("Poisoned-empty-merge G-set (M(0,0,0):=1)", 2,
                   (C1,), poisoned_or_cells(), {})


def make_pure_or():
    """CONTROL for the VC5 separator: poison removed.  Expected [] RALIN."""
    return TabSpec("Pure or-merge G-set (control)", 2,
                   (C1,), or_cells(), {})


def make_changewins():
    """THE VC6 SEPARATOR (found by the S2x2 exhaustive scan, then hand-
    derived).  The CHANGE-WINS FLAG: Sigma = {0,1}, init 0; set = c1,
    clear = c0; rc(clear, set) = Fst (set wins concurrent races: add-wins);
    mergeL(l,a,b) = a|b if l = 0 else a&b ("a change from the LCA wins").
    Hand-derivation of the vector: VC1 (set/clear non-comm, rc directional),
    VC2 (single Fst edge clear->set), VC3 (both kinds are constants, the
    final e'' erases any swap), VC4 (both rows symmetric), VC5 (the l = 0
    row is a|b, so mergeL(0,0,s) = s) green.  VC8 green: for e = set every
    element of downset(e)-e reaches e through a clear, so every
    loOn-maximal element there is a clear and B = 0, giving
    mergeL(0, A, 1) = A|1 = 1 = set(A); for e = clear either
    downset(e)-e is nonempty, B = 1, mergeL(1, A, 0) = A&0 = 0 = clear(A),
    or it is empty, and then e's maximality forces every concurrent set in
    U to be visNC-followed by a clear, so A = 0 and mergeL(0,0,0) = 0.
    VC7 green: e = set gives B = 0, u = 1, all inner slots saturate to 1
    and both sides are 1; e = clear with B = 1, u = 0 collapses both sides
    to 0; e = clear with B = u = 0 makes the inner merges identities.
    VC6 RED: e = set concurrent with a clear b, re-asserting the LCA value.
    Countermodel: a = set, b = clear with vis a -> b, e = set concurrent
    with b; E1 = {a,e}, E2 = {a,b}: s0 = sig({a}) = 1, B = sig({}) = 0,
    t1 = 1, s2 = sig({a,b}) = 0, u = set(0) = 1:
      LHS = mergeL(1, mergeL(0,1,1), 0) = mergeL(1,1,0) = 1&0 = 0
      RHS = mergeL(0, mergeL(1,1,0), 1) = mergeL(0,0,1) = 0|1 = 1.
    The same instance breaks the Join: sig(U) = 1 (rc orders b before the
    concurrent e, so the re-assertion wins) but the merge of s1 = 1 with
    s2 = 0 over s0 = 1 is 1&0 = 0: the merge cannot distinguish "changed
    to the same value" from "unchanged", while rc promises the set wins.
    Expected: reds [6], NONRA, convergent, and NO Join violation with a
    side smaller than two events (hand-derived: every (0,n)/(1,n) merge is
    green because a lone set is loOn-maximal in the union and a lone clear
    can be enumerated first), so the minimal violation shape is (2,2)."""
    cells = {(0, 0, 0): 0, (0, 0, 1): 1, (0, 1, 1): 1,
             (1, 0, 0): 0, (1, 0, 1): 0, (1, 1, 1): 1}
    return TabSpec("Change-wins flag (VC6 separator)", 2,
                   (C0, C1), cells, {(0, 1): FST, (1, 0): SND})


def make_changewins_flipped():
    """NEGATIVE COMPANION to the VC6 separator: the SAME change-wins merge
    with the arbitration flipped, rc(set, clear) = Fst (clear wins).  The
    isolation is destroyed: VC8 co-breaks.  Hand-derivation of the VC8
    failure: U = {set s, clear c} concurrent; the only loOn edge is s -> c
    (rc Fst, c unblocked), so c is maximal; A = sig({s}) = 1,
    B = sig(downset(c)-c) = sig({}) = 0; CD demands
    mergeL(0, 1, clear(0)) = clear(1) = 0, but the change-wins merge sees
    the clear-at-init as no change and gives 1|0 = 1.  VC6 also red (the
    dual instance: e = clear with a set parent, B = 1, u = 0, s0 = 0,
    s2 = 1 gives LHS = mergeL(0,0,1) = 1 vs RHS = mergeL(1,1,0) = 0).
    Expected: reds [6, 8], NONRA -- NOT an isolating witness; the vector
    [6] of the add-wins direction is rc-direction-specific."""
    cells = {(0, 0, 0): 0, (0, 0, 1): 1, (0, 1, 1): 1,
             (1, 0, 0): 0, (1, 0, 1): 0, (1, 1, 1): 1}
    return TabSpec("Change-wins flag, rc flipped (companion)", 2,
                   (C0, C1), cells, {(1, 0): FST, (0, 1): SND})


def make_vc3_sentinel():
    """THE VC3 SENTINEL (weakenability witness, mirror of phase-1's VC4
    sentinel).  k = 3; state 2 is UNREACHABLE (init 0, both ops fix {0,1}
    pointwise and map 2 into {0,1}).  P = (0,1,0), Q = (0,1,1): they commute
    on {0,1} but not at 2 (Q(P(2)) = Q(0) = 0, P(Q(2)) = P(1) = 1), so
    ~comm(P,Q) holds (it is a forall over the WHOLE universe) and VC1 forces
    an rc edge: rc(P,Q) = Fst.  mergeL = max(a,b), LCA dropped.
    Hand-derivation: VC1 green (the only non-comm pair carries the edge);
    VC2 green (single edge); VC4 green (max symmetric).  Reachable world:
    every fold fixes 0, all canonical states are 0, both ops fix 0, so VC5
    (max(0,0)=0), VC6, VC7, VC8 (mergeL(0,0,e(0)=0) = 0 = e(0)) and the Join
    are all green and the datatype converges.  VC3 RED at the unreachable
    s = 2 with pi = []: e = P-event, e' = Q-event, e'' = P-event
    (~comm(Q,P)): e''(P(Q(2))) = P(1) = 1 vs e''(Q(P(2))) = P(0) = 0.
    Expected: reds [3], RALIN.  Reading: cond_comm_lift quantifies over the
    whole state universe; its content beyond reachable states is not
    load-bearing for adequacy -- the same weakenability class as VC4."""
    do_p = (0, 1, 0)
    do_q = (0, 1, 1)
    cells = {(l, lo, hi): hi for l in range(3)
             for lo in range(3) for hi in range(lo, 3)}   # max(a,b)
    return TabSpec("VC3 sentinel (break only at unreachable state 2)", 3,
                   (do_p, do_q), cells, {(0, 1): FST, (1, 0): SND})


NAMED = [
    # (make, expected_reds, expected_ra, exact_viol_shapes_or_None,
    #  min_viol_shape_or_None)
    (make_ewflag2,            [8],    'NONRA', None,     None),
    (make_parity,             [7],    'NONRA', None,     None),
    (make_delta_xor,          [],     'RALIN', None,     None),
    (make_poisoned_empty,     [5],    'NONRA', [(0, 0)], None),
    (make_pure_or,            [],     'RALIN', None,     None),
    (make_changewins,         [6],    'NONRA', None,     (2, 2)),
    (make_changewins_flipped, [6, 8], 'NONRA', None,     None),
    (make_vc3_sentinel,       [3],    'RALIN', None,     None),
]


# ----------------------------------------------------------------------------
# Search spaces.
# ----------------------------------------------------------------------------

K2_TABLES = [C0, ID2, NOT2, C1]


def space_s2x2():
    merges = list(sym_merge_tables(2))
    n = 0
    for t0, t1 in product(K2_TABLES, repeat=2):
        for rc_table in rc_choices((t0, t1), 2):
            for cells in merges:
                n += 1
                yield TabSpec("S2x2#%d" % n, 2, (t0, t1), dict(cells),
                              rc_table)


def space_s2x3():
    merges = list(sym_merge_tables(2))
    n = 0
    for tabs in product(K2_TABLES, repeat=3):
        for rc_table in rc_choices(tabs, 2):
            for cells in merges:
                n += 1
                yield TabSpec("S2x3#%d" % n, 2, tabs, dict(cells), rc_table)


K3_DO_POOL = [
    (0, 0, 0), (1, 1, 1), (2, 2, 2),          # constants
    (1, 2, 0),                                 # +1 mod 3
    (1, 2, 2),                                 # capped increment
    (0, 1, 2),                                 # identity
    (1, 0, 2), (0, 2, 1),                      # transpositions
]


def k3_structured_merges():
    """Structured l-USING merges on {0,1,2} (branch-symmetric)."""
    def med3(l, a, b):
        return sorted((l, a, b))[1]
    fns = [
        ("a+b-l", lambda l, a, b: (a + b - l) % 3),
        ("a+b",   lambda l, a, b: (a + b) % 3),
        ("max",   lambda l, a, b: max(a, b)),
        ("min",   lambda l, a, b: min(a, b)),
        ("max3",  lambda l, a, b: max(l, a, b)),
        ("min3",  lambda l, a, b: min(l, a, b)),
        ("med3",  med3),
        ("cap+",  lambda l, a, b: min(a + b, 2)),
        ("cap+-l", lambda l, a, b: max(min(a + b - l, 2), 0)),
    ]
    out = []
    for name, f in fns:
        cells = {(l, lo, hi): f(l, lo, hi) for l in range(3)
                 for lo in range(3) for hi in range(lo, 3)}
        out.append((name, cells))
    return out


def k3_unital_magmas():
    """All 27 l-free commutative merges with 0 a two-sided unit: the cells
    (1,1), (1,2), (2,2) are free.  VC5 forces the unit only on canonical
    states; fixing it outright focuses the scan on the VC6-vs-VC7 gap
    (l-free VC6 = associativity, l-free VC7 = the exchange law)."""
    out = []
    for v11, v12, v22 in product(range(3), repeat=3):
        m2 = {(0, 0): 0, (0, 1): 1, (0, 2): 2,
              (1, 1): v11, (1, 2): v12, (2, 2): v22}
        cells = {(l, lo, hi): m2[(lo, hi)] for l in range(3)
                 for lo in range(3) for hi in range(lo, 3)}
        out.append(("magma%d%d%d" % (v11, v12, v22), cells))
    return out


def random_sym_cells(k, rng):
    return {(l, lo, hi): rng.randrange(k) for l in range(k)
            for lo in range(k) for hi in range(lo, k)}


def space_s3(seed, random_budget):
    structured = k3_structured_merges() + k3_unital_magmas()
    n = 0
    for t0, t1 in product(K3_DO_POOL, repeat=2):
        for rc_table in rc_choices((t0, t1), 3):
            for _, cells in structured:
                n += 1
                yield TabSpec("S3#%d" % n, 3, (t0, t1), dict(cells),
                              rc_table)
    rng = random.Random(seed)
    do_pairs = list(product(K3_DO_POOL, repeat=2))
    for _ in range(random_budget):
        t0, t1 = do_pairs[rng.randrange(len(do_pairs))]
        rcs = list(rc_choices((t0, t1), 3))
        rc_table = rcs[rng.randrange(len(rcs))]
        cells = random_sym_cells(3, rng)
        n += 1
        yield TabSpec("S3#%d(rand)" % n, 3, (t0, t1), cells, rc_table)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def scan(space_name, spec_iter, seed, filter_budget=12, n_events=4,
         progress_every=4000):
    """Scan a space: cheap checkers -> config filter (early two-red abort) ->
    multi-seed confirmation for exactly-one-red survivors.  Returns
    (visited, finds) where finds = [(spec, reds, ra, conv, shapes)]."""
    visited = 0
    finds = []
    seen = set()
    for idx, spec in enumerate(spec_iter):
        visited += 1
        if progress_every and visited % progress_every == 0:
            print("  ... %s: %d specs visited, %d finds so far"
                  % (space_name, visited, len(finds)), flush=True)
        reds14 = cheap_reds(spec)
        if len(reds14) >= 2:
            continue
        reds, _ = config_reds(spec, seed + idx * 9973, filter_budget,
                              n_events, reds14)
        if len(reds) != 1:
            continue
        sig = spec.signature()
        if sig in seen:
            continue
        creds, ra, conv, shapes = confirm(spec)
        if len(creds) != 1:
            continue                    # broke elsewhere under confirmation
        seen.add(sig)
        finds.append((spec, creds, ra, conv, shapes))
    return visited, finds


def report_finds(space_name, visited, finds):
    print("\n== %s: %d specs visited, %d confirmed one-red specs =="
          % (space_name, visited, len(finds)))
    by_vc = {}
    for spec, reds, ra, conv, shapes in finds:
        by_vc.setdefault((reds[0], ra), []).append((spec, conv, shapes))
    for (vc, ra) in sorted(by_vc):
        group = by_vc[(vc, ra)]
        print("  [VC%d]-only, %s: %d specs%s" % (
            vc, ra, len(group),
            "  <-- INDEPENDENCE WITNESSES" if ra == 'NONRA' else
            "  (weakenability witnesses: red but RA-linearizable)"))
        for spec, conv, shapes in group[:6]:
            extra = "" if ra == 'RALIN' else "  joinviol=%s" % (shapes,)
            print("      %s  conv=%s%s" % (spec.describe(), conv, extra))
        if len(group) > 6:
            print("      ... and %d more" % (len(group) - 6))
    for target in (3, 5, 6):
        if not any(vc == target for (vc, _) in by_vc):
            print("  [VC%d]-only: NO spec found in this space" % target)


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    full = "--full" in sys.argv
    seed = int(args[0]) if args else 114
    print("# VC synthesis search (task #114 phase 1b)  seed=%d  full=%s"
          % (seed, full), flush=True)

    # ---- 1. Named specs: hand-derived expectations (PASS+FAIL) ----
    print("\n== Named specs (hand-derived expected verdicts) ==")
    mismatches = 0
    for make, exp_reds, exp_ra, exp_shapes, exp_min in NAMED:
        spec = make()
        reds, ra, conv, shapes = confirm(spec)
        ok = (reds == exp_reds and ra == exp_ra
              and (exp_shapes is None or shapes == exp_shapes)
              and (exp_min is None or (shapes and min(shapes) == exp_min)))
        print("  %-48s reds=%-6s ra=%-6s conv=%-5s%s -> %s"
              % (spec.name[:48], reds, ra, conv,
                 (" minviol=%s" % (min(shapes),)) if shapes else "",
                 "MATCH" if ok else
                 "*** MISMATCH (expected %s %s %s min=%s) ***"
                 % (exp_reds, exp_ra, exp_shapes, exp_min)))
        if not ok:
            mismatches += 1

    # ---- 2. S2x2 exhaustive scan + CALIBRATION ----
    visited, finds = scan("S2x2", space_s2x2(), seed)
    report_finds("S2x2 (k=2, 2 kinds, EXHAUSTIVE)", visited, finds)
    sigs = {spec.signature() for spec, _, _, _, _ in finds}
    cal8 = make_ewflag2().signature() in sigs
    xorsig = tuple(sorted(xor_cells().items()))
    cal7 = any(reds == [7] and ra == 'NONRA'
               and spec.signature()[3] == xorsig
               and all(t == NOT2 for t in spec.do_tables)
               for spec, reds, ra, _, _ in finds)
    cal5 = any(reds == [5] and ra == 'NONRA' and shapes == [(0, 0)]
               for _, reds, ra, _, shapes in finds)
    print("\n== CALIBRATION (must re-find the dual core from scratch) ==")
    print("  re-found VC8 witness (EWFlag2 signature):    %s"
          % ("PASS" if cal8 else "*** FAIL ***"))
    print("  re-found VC7 witness (parity xor signature): %s"
          % ("PASS" if cal7 else "*** FAIL ***"))
    print("  re-found VC5 empty-corner witness class:     %s"
          % ("PASS" if cal5 else "*** FAIL ***"))
    if not (cal7 and cal8):
        mismatches += 1

    # ---- 3. Optional big spaces ----
    if full:
        visited3, finds3 = scan("S2x3", space_s2x3(), seed + 1)
        report_finds("S2x3 (k=2, 3 kinds, EXHAUSTIVE)", visited3, finds3)
        visitedk3, findsk3 = scan("S3", space_s3(seed + 2, 4000), seed + 2)
        report_finds("S3 (k=3, 2 kinds, GUIDED: structured+27 magmas"
                     "+4000 random)", visitedk3, findsk3)

    print("\n# named-spec mismatches + calibration failures: %d" % mismatches)
    sys.exit(1 if mismatches else 0)


if __name__ == "__main__":
    main()
