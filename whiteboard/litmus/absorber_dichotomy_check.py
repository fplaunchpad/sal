#!/usr/bin/env python3
"""absorber_dichotomy_check.py -- task #114 phase 3: THE ABSORBER DICHOTOMY.

The VC-minimality sweep (whiteboard/vc-minimality-note.md) exposed the eight
verification conditions as a four-law core plus a proof-technique shell.  This
probe turns the same lens on the RA-linearizability DEFINITION itself, and
interrogates ONE clause of the linearization order: the ABSORBER.

THE ORDER (def:lo of Sal/ConditionedMRDTs/sal-mrdts.tex, mirrored by
Sal.Emulation.loOn in Sal/CRDTs/Metatheory/Merge_Linearization_Set.lean):

    loOn(ev, x, y)  :=  (vis x y and not comm x y)                    [vis arm]
                     or (x || y and rc x y = Fst                      [rc  arm]
                         and NOT (exists e3 in ev.                    [ABSORBER]
                                  vis y e3 and not comm y e3))

The rc arm orders a concurrent pair x, y by the conflict resolver rc UNLESS y
is "absorbed": a later non-commuting visible successor e3 (in the version's own
event set ev) cancels the rc-edge x -> y.  The absorber's SCOPE (ranging over
ev, not the whole configuration) was itself a forced soundness correction: the
whole-configuration variant Sal.Emulation.lo is UNSOUND inside a version, the
defeater of sec:defeater realizes it.

THE EDGE-DIRECTION FACT (it determines the whole probe).  RA-linearizability
asks each version's operational state to be the fold of SOME order-respecting
enumeration of its event set (def:ralin).  An enumeration respects an order
iff it never reverses an edge.  The absorber REMOVES edges.  Fewer edges =
fewer constraints = MORE enumerations qualify = MORE folds reachable.  So

    plain-order (absorber clause DROPPED, every rc-resolved pair keeps its
                 edge) is STRICTER: its edge set is a SUPERSET of loOn's,
                 hence its respecting perms are a SUBSET, hence

        folds_plain(ev)  SUBSETEQ  folds_absorber(ev)   for every ev.

    Therefore, for a FIXED operational state op(v) computed by the DAG
    dynamics (order-independent):

        op(v) in folds_plain(ev)   ==>   op(v) in folds_absorber(ev),

    i.e.  RA-lin-under-plain  ==>  RA-lin-under-absorber  (absorber is WEAKER).

The ONLY possible separator is a datatype RA-lin under the ABSORBER order but
NOT under the plain order -- such a separator makes the absorber LOAD-BEARING.

HYPOTHESES.
  H-redundant  : on reachable (honest-DAG) versions, the two orders agree
                 (no separator); the absorber clause is a presentation
                 artifact; every absorber witness repairs to a plain witness
                 with the same fold (the absorbing e3 makes the pair's order
                 fold-irrelevant).
  H-loadbearing: some datatype, on some reachable version, is RA-lin under
                 the absorber order but not the plain order.  Then split:
                 OBSERVABLE (the plain fold set has no state query-equal to
                 op) vs INTERNAL (a plain fold is eqObs-equal to op, so the
                 gap is a fold-quotient artifact absorbable into eqObs).

METHOD.  Two oracles forked from the loOn-fold checker of
vc_minimality_check / vc_synthesis_search, one per order, applied to the
ACTUAL operational state of every version of an honest ternary merge DAG
(faithful to def:ralin, not the Join proxy: op(v) is order-independent, so
the monotonicity above holds by construction).  Calibrated against the four
anchors (ORSet, MVR RA-lin; change-wins flag, AWSetF3 non-RA-lin); any anchor
whose two-order verdict differs IS a separator.  Then a synthesis search
(reusing the vc_synthesis_search spec spaces) plus directed LWW/overwrite
candidates, and an explicit antitonicity demo (E subset E' with a vanishing
edge, the defeater's shape).

Run:  python3 whiteboard/litmus/absorber_dichotomy_check.py [seed] [--full]
      Exit 0 iff every hand-derived expectation matches.
"""

import os
import sys
import random
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from vc_minimality_check import (
    Config, FST,
    make_orset, make_mvr, make_vc8_awsetf, make_vc2_lww,
)
from vc_synthesis_search import (
    make_changewins, space_s2x2, space_s2x3,
)


# ---------------------------------------------------------------------------
# The two linearization orders.  loon2(..., absorber=True) is loOn (the
# set-relative order of Merge_Linearization_Set.lean); absorber=False is the
# strict PLAIN order (drop the ~exists-e3 clause: every rc-resolved concurrent
# pair keeps its edge).
# ---------------------------------------------------------------------------

def loon2(spec, C, ev, x, y, absorber):
    if C.vis(x, y) and not spec.commutes(x, y):
        return True                                   # vis arm (both orders)
    if (not C.vis(x, y)) and (not C.vis(y, x)) and spec.rc(x, y) == FST:
        if not absorber:
            return True                               # plain: keep every edge
        # absorber: drop the edge if y has a later non-commuting successor in ev
        if not any((e3 in ev) and C.vis(y, e3) and not spec.commutes(y, e3)
                   for e3 in C.events):
            return True
    return False


def loon_edges(spec, C, ev, absorber):
    evl = list(ev)
    return {(x, y) for x in evl for y in evl
            if x != y and loon2(spec, C, ev, x, y, absorber)}


def folds_on(spec, C, ev, absorber):
    """Set of fold results over ALL loon2(absorber)-respecting enumerations of
    ev.  Empty iff the order is cyclic on ev (no witness exists); for ev = {}
    it is {init}."""
    evl = list(ev)
    edges = loon_edges(spec, C, ev, absorber)
    results = set()

    def rec(placed, remaining):
        if not remaining:
            results.add(spec.fold(placed))
            return
        for y in list(remaining):
            if all((x, y) not in edges for x in remaining if x != y):
                rec(placed + [y], remaining - {y})

    rec([], set(evl))
    return frozenset(results)


class Folds:
    """Memoised fold-set oracle for a fixed (spec, config)."""
    def __init__(self, spec, C):
        self.spec = spec
        self.C = C
        self._memo = {}

    def get(self, ev, absorber):
        key = (frozenset(ev), absorber)
        if key not in self._memo:
            self._memo[key] = folds_on(self.spec, self.C, ev, absorber)
        return self._memo[key]


# ---------------------------------------------------------------------------
# Honest ternary merge DAGs (a faithful Step3 model: Apply mints a fresh event
# seeing its parent's whole event set; Merge is 3-way at an honest LCA, gated
# on the LCA existing as a stored version -- criss-cross merges are skipped).
# Every version carries its OPERATIONAL state op (from do / mergeL) and its
# event set; op is order-independent, which is what makes the dichotomy clean.
# ---------------------------------------------------------------------------

class Version:
    __slots__ = ('vid', 'events', 'op', 'parents')

    def __init__(self, vid, events, op, parents):
        self.vid = vid
        self.events = frozenset(events)
        self.op = op
        self.parents = parents


def _find_lca(versions, ev1, ev2):
    inter = ev1 & ev2
    best = None
    for v in versions:
        if v.events == inter:
            return v                       # exact LCA realized as a version
    return best                            # None -> criss-cross, gate the merge


def build_honest_dag(spec, rng, n_replicas, n_steps, appchoices, max_events=6):
    v0 = Version(0, frozenset(), spec.init, ())
    versions = [v0]
    events = []
    vis = set()
    heads = [v0 for _ in range(n_replicas)]
    tsc = [0]
    for _ in range(n_steps):
        if rng.random() < 0.58:                        # Apply
            r = rng.randrange(n_replicas)
            v = heads[r]
            if len(v.events) >= max_events:
                continue
            tsc[0] += 1
            e = (tsc[0], r, rng.choice(appchoices))
            for ep in v.events:
                vis.add((ep, e))
            events.append(e)
            nv = Version(len(versions), v.events | {e},
                         spec.do(v.op, e), (v.vid,))
            versions.append(nv)
            heads[r] = nv
        else:                                          # Merge
            r1 = rng.randrange(n_replicas)
            r2 = rng.randrange(n_replicas)
            if r1 == r2:
                continue
            v1, v2 = heads[r1], heads[r2]
            if v1.vid == v2.vid or v1.events == v2.events:
                continue
            lca = _find_lca(versions, v1.events, v2.events)
            if lca is None:
                continue
            merged = v1.events | v2.events
            if len(merged) > max_events:
                continue
            nv = Version(len(versions), merged,
                         spec.mergeL(lca.op, v1.op, v2.op), (v1.vid, v2.vid))
            versions.append(nv)
            heads[r1] = nv
    return Config(events, vis), versions


def build_explicit_dag(spec, moves):
    """moves: list of ('apply', parent_idx, event) | ('merge', i1, i2, lca_idx).
    Returns (Config, versions).  Asserts LCA event-set correctness."""
    versions = [Version(0, frozenset(), spec.init, ())]
    events = []
    vis = set()
    for mv in moves:
        if mv[0] == 'apply':
            _, pi, e = mv
            v = versions[pi]
            for ep in v.events:
                vis.add((ep, e))
            events.append(e)
            versions.append(Version(len(versions), v.events | {e},
                                    spec.do(v.op, e), (pi,)))
        else:
            _, i1, i2, il = mv
            v1, v2, vl = versions[i1], versions[i2], versions[il]
            assert vl.events == (v1.events & v2.events), \
                ("bad LCA", sorted(vl.events), sorted(v1.events & v2.events))
            versions.append(Version(len(versions), v1.events | v2.events,
                                    spec.mergeL(vl.op, v1.op, v2.op), (i1, i2)))
    return Config(events, vis), versions

# ---------------------------------------------------------------------------
# The two oracles.  RA-lin (def:ralin) at a version = its operational state is
# a fold of SOME order-respecting enumeration of its event set.  op is fixed
# by the DAG dynamics; only the fold set depends on the order, so
# folds_plain subseteq folds_absorber gives  RA_plain ==> RA_absorber cleanly.
# ---------------------------------------------------------------------------

CYCLIC = "CYCLIC"          # marker: order has no linear extension on this ev


def version_status(spec, F, v, absorber, eqobs=None):
    """Return True (op is a witness fold), False (op reproducible by no
    respecting fold), or CYCLIC (the order itself has no extension)."""
    eq = eqobs or (lambda a, b: a == b)
    folds = F.get(v.events, absorber)
    if not folds:
        return CYCLIC
    return any(eq(v.op, f) for f in folds)


def config_report(spec, C, versions, eqobs=None):
    """Per-config summary under BOTH orders.  Fields:
      abs_ra / plain_ra : is EVERY version a witness under that order?
      abs_cyclic        : some version where the absorber order is cyclic
      sep_cyclic        : separator versions where plain is CYCLIC (absorber ok)
      sep_foldval       : separator versions where plain is acyclic but op is
                          no plain fold (absorber ok)          [(v, fp, fa)]
    """
    F = Folds(spec, C)
    r = dict(abs_ra=True, plain_ra=True, abs_cyclic=False,
             sep_cyclic=[], sep_foldval=[])
    for v in versions:
        sa = version_status(spec, F, v, True, eqobs)
        sp = version_status(spec, F, v, False, eqobs)
        if sa is not True:
            r['abs_ra'] = False
            if sa is CYCLIC:
                r['abs_cyclic'] = True
        if sp is not True:
            r['plain_ra'] = False
        if sa is True and sp is not True:            # separator version
            fp = F.get(v.events, False)
            fa = F.get(v.events, True)
            if sp is CYCLIC:
                r['sep_cyclic'].append((v, fp, fa))
            else:
                r['sep_foldval'].append((v, fp, fa))
    return r


def scan_config_verdict(spec, appch, seeds, budget, nrep=3, nsteps=13,
                        max_events=6):
    """Aggregate config_report over many honest DAGs.  Returns
    (abs_ra, plain_ra, saw_cyclic_sep, saw_foldval_sep, abs_cyclic,
     example_cyclic_sep)."""
    abs_ra = True
    plain_ra = True
    saw_cyc = False
    saw_fv = False
    abs_cyc = False
    ex = None
    for s in seeds:
        rng = random.Random(s)
        for _ in range(budget):
            C, vs = build_honest_dag(spec, rng, nrep, nsteps, appch, max_events)
            rep_ = config_report(spec, C, vs)
            abs_ra = abs_ra and rep_['abs_ra']
            plain_ra = plain_ra and rep_['plain_ra']
            abs_cyc = abs_cyc or rep_['abs_cyclic']
            if rep_['sep_cyclic']:
                saw_cyc = True
                if ex is None:
                    ex = (C, rep_['sep_cyclic'][0][0])
            if rep_['sep_foldval']:
                saw_fv = True
    return abs_ra, plain_ra, saw_cyc, saw_fv, abs_cyc, ex


# ---------------------------------------------------------------------------
# Two deterministic hand-built witness DAGs (honest, LCA-legal).
# ---------------------------------------------------------------------------

def orset_minimal_separator():
    """The MINIMAL absorber separator: two replicas each ADD then REMOVE the
    same element x, then merge (LCA = the empty root).  A completely mundane
    honest execution.  Events a=add,ra=rem on replica 0; b=add,rb=rem on
    replica 1.  In the merged version's event set {a,ra,b,rb} the PLAIN order
    is CYCLIC:
        a ->(vis, add before its own later rem) ra
        ra->(rc,  rem before concurrent add: add-wins)   b
        b ->(vis) rb
        rb->(rc)  a
    a -> ra -> b -> rb -> a has no linear extension, so plain-RA-lin admits NO
    witness.  The absorber removes both rc edges (each add is absorbed by its
    own following rem), leaving the two vis chains a->ra, b->rb; every
    interleaving folds to the empty live set = the operational merge state.
    Expected: absorber RA-lin (op = {} in folds_absorber), plain CYCLIC."""
    sp = make_orset()
    a = (1, 0, ('add', 0)); ra = (2, 0, ('rem', 0))
    b = (3, 1, ('add', 0)); rb = (4, 1, ('rem', 0))
    moves = [('apply', 0, a), ('apply', 1, ra), ('apply', 0, b),
             ('apply', 3, rb), ('merge', 2, 4, 0)]
    C, vs = build_explicit_dag(sp, moves)
    return sp, C, vs, vs[-1]


def awsetf_defeater():
    """The defeater DAG (fig:defeater), on the add-wins skeleton AWSetF3.  A
    staging replica realizes {A_p,A_q} as version v_s so the final merge is
    LCA-legal.  The merged head v_top has flag = True (OR-flag merge) but every
    witness ends in a rem (flag False), so v_top is NON-RA-lin under BOTH
    orders (the #57 flag-deflation) -- the two orders AGREE here.  Returns
    (spec, C, versions, v_top)."""
    sp = make_vc8_awsetf()
    Ap = (1, 0, ('add',)); Aq = (2, 1, ('add',))
    Rp = (3, 0, ('rem',)); Rq = (4, 1, ('rem',))
    moves = [('apply', 0, Ap), ('apply', 0, Aq), ('merge', 1, 2, 0),
             ('apply', 1, Rp), ('apply', 2, Rq),
             ('merge', 4, 3, 1), ('merge', 5, 3, 2), ('merge', 6, 7, 3)]
    C, vs = build_explicit_dag(sp, moves)
    return sp, C, vs, vs[-1]

# ---------------------------------------------------------------------------
# PART 3.  CALIBRATION against the four anchors.  Both oracles must reproduce
# the known verdicts; any anchor whose two-order verdict DIFFERS is itself a
# separator (that difference is the whole point).  Expected:
#   ORSet        absorber RALIN / plain NONRA (cyclic)  -> SEPARATOR
#   MVR          absorber RALIN / plain RALIN           -> agree
#   change-wins  absorber NONRA / plain NONRA           -> agree (intrinsic)
#   AWSetF3      absorber NONRA / plain NONRA           -> agree (deflation)
# Companion fact: the absorber order is NEVER cyclic on any anchor version.
# ---------------------------------------------------------------------------

def run_calibration():
    print("== CALIBRATION: both oracles vs the four anchors ==")
    mm = 0

    # ORSet: deterministic minimal separator + random corroboration.
    sp, C, vs, sep = orset_minimal_separator()
    F = Folds(sp, C)
    fp = F.get(sep.events, False)
    fa = F.get(sep.events, True)
    ok_det = (not fp) and (sep.op in fa)          # plain cyclic, absorber ok
    print("  ORSet minimal DAG {a=add,ra=rem | b=add,rb=rem} merged:")
    print("     op=%s  folds_plain=%s (empty=CYCLIC)  folds_absorber=%s"
          % (sorted(sep.op), fp, fa))
    print("     -> plain has NO witness (cyclic), absorber has one : %s"
          % ("PASS" if ok_det else "*** FAIL ***"))
    mm += 0 if ok_det else 1
    aR, pR, cyc, fv, acyc, ex = scan_config_verdict(
        sp, [('add', 0), ('rem', 0)],
        [114, 7, 2026, 99, 5, 42], 30, nsteps=16)
    ok_rand = aR and (not pR) and cyc and (not fv) and (not acyc)
    print("     random 180 single-element DAGs: absorber=%s plain=%s "
          "cyclic-sep=%s foldval-sep=%s absorber-cyclic=%s"
          % ('RALIN' if aR else 'NONRA', 'RALIN' if pR else 'NONRA',
             cyc, fv, acyc))
    print("     EXPECT absorber RALIN, plain NONRA(cyclic), no foldval, "
          "absorber acyclic -> %s" % ("PASS" if ok_rand else "*** FAIL ***"))
    mm += 0 if ok_rand else 1

    # MVR: agree, both RALIN.
    sp = make_mvr()
    aR, pR, cyc, fv, acyc, ex = scan_config_verdict(
        sp, [('wr', 0), ('wr', 1)], [114, 7, 2026], 40)
    ok = aR and pR and (not acyc)
    print("  MVR: absorber=%s plain=%s (EXPECT both RALIN, agree) -> %s"
          % ('RALIN' if aR else 'NONRA', 'RALIN' if pR else 'NONRA',
             "PASS" if ok else "*** FAIL ***"))
    mm += 0 if ok else 1

    # change-wins: agree, both NONRA (its non-RA-ness is intrinsic).
    sp = make_changewins()
    aR, pR, cyc, fv, acyc, ex = scan_config_verdict(
        sp, sp.appchoices, [114, 7, 2026], 40)
    ok = (not aR) and (not pR)
    print("  change-wins flag: absorber=%s plain=%s (EXPECT both NONRA, "
          "agree) -> %s"
          % ('RALIN' if aR else 'NONRA', 'RALIN' if pR else 'NONRA',
             "PASS" if ok else "*** FAIL ***"))
    mm += 0 if ok else 1

    # AWSetF3: deterministic defeater DAG + agreement.
    sp, C, vs, vtop = awsetf_defeater()
    F = Folds(sp, C)
    sa = version_status(sp, F, vtop, True)
    spv = version_status(sp, F, vtop, False)
    ok = (sa is not True) and (spv is not True)   # both: op is no witness
    print("  AWSetF3 defeater v_top: op flag=True, every fold ends in rem "
          "(flag False)")
    print("     absorber=%s (op no fold: flag deflation), plain=%s "
          "(EXPECT both NONRA, agree) -> %s"
          % (sa, spv, "PASS" if ok else "*** FAIL ***"))
    mm += 0 if ok else 1
    print("  => ORSet is the anchor separator (absorber load-bearing); "
          "MVR/change-wins/AWSetF3 agree.\n")
    return mm


# ---------------------------------------------------------------------------
# PART 4.  SEPARATOR SEARCH.  Exhaustive S2x2 config-level classification:
# EVERY config-level separator is via the CYCLIC route; none via fold-value
# (fold-value separator VERSIONS occur only inside datatypes already NON-RA
# under the absorber order, i.e. VC-violators, so they never lift to a
# config-level dichotomy).  Directed LWW candidate: no separator (overwrite
# arbitration agrees with vis, so no plain cycle).
# ---------------------------------------------------------------------------

def run_search(full=False):
    print("== SEARCH: config-level separator classification ==")
    mm = 0

    # Directed candidate 1: LWW register (a concurrent write overwritten by a
    # later visible write -- the absorber's motivating shape).  rc = timestamp
    # order AGREES with vis direction, so plain never cycles and the last
    # writer dominates every fold: NO separator.  Hand-derived expectation.
    sp = make_vc2_lww()
    aR, pR, cyc, fv, acyc, ex = scan_config_verdict(
        sp, [('wr', 1), ('wr', 2), ('wr', 3)], [114, 7, 2026], 30, nsteps=12)
    ok = aR and pR and (not cyc) and (not fv)
    print("  [directed] LWW register: absorber=%s plain=%s cyclic-sep=%s "
          "foldval-sep=%s"
          % ('RALIN' if aR else 'NONRA', 'RALIN' if pR else 'NONRA', cyc, fv))
    print("     EXPECT no separator (rc agrees with vis) -> %s"
          % ("PASS" if ok else "*** FAIL ***"))
    mm += 0 if ok else 1

    # Exhaustive S2x2.
    nspec = 0
    sep_cyc = 0
    sep_fv = 0
    for spec in space_s2x2():
        nspec += 1
        aR, pR, cyc, fv, acyc, ex = scan_config_verdict(
            spec, spec.appchoices, [7, 114, 2026], 6)
        if aR and not pR:
            if cyc:
                sep_cyc += 1
            else:
                sep_fv += 1
    ok = (sep_fv == 0) and (sep_cyc > 0)
    print("  S2x2 exhaustive (%d specs, budget 18 DAGs/spec):" % nspec)
    print("     config-level separators: CYCLIC route = %d, FOLD-VALUE route "
          "= %d" % (sep_cyc, sep_fv))
    print("     EXPECT fold-value = 0 (every certified separator is cyclic) "
          "-> %s" % ("PASS" if ok else "*** FAIL ***"))
    mm += 0 if ok else 1

    if full:
        nspec = 0
        sep_cyc = 0
        sep_fv = 0
        for spec in space_s2x3():
            nspec += 1
            aR, pR, cyc, fv, acyc, ex = scan_config_verdict(
                spec, spec.appchoices, [7, 114], 4)
            if aR and not pR:
                if cyc:
                    sep_cyc += 1
                else:
                    sep_fv += 1
        print("  S2x3 exhaustive (%d specs): CYCLIC = %d, FOLD-VALUE = %d"
              % (nspec, sep_cyc, sep_fv))
    print()
    return mm


# ---------------------------------------------------------------------------
# PART 5.  THE ANTITONICITY STRIKE + observable/internal.  Exhibit E subset E'
# where loOn(E) has an edge loOn(E') LACKS (growing the set adds an absorber,
# removing the edge -- loOn_mono of def:lo).  Then the observable/internal
# reading of the two routes.
# ---------------------------------------------------------------------------

def run_antitonicity():
    print("== ANTITONICITY (loOn antitone in the event set) ==")
    mm = 0
    sp = make_orset()
    a = (1, 0, ('add', 0)); ra = (2, 0, ('rem', 0))
    b = (3, 1, ('add', 0)); rb = (4, 1, ('rem', 0))
    # Build a config carrying all four events with the honest vis
    # (a->ra same replica, b->rb same replica).
    moves = [('apply', 0, a), ('apply', 1, ra), ('apply', 0, b),
             ('apply', 3, rb), ('merge', 2, 4, 0)]
    C, vs = build_explicit_dag(sp, moves)
    E = frozenset({a, ra, b})
    Ep = frozenset({a, ra, b, rb})
    eE = loon_edges(sp, C, E, True)
    eEp = loon_edges(sp, C, Ep, True)
    # the rc edge ra -> b (rem before concurrent add, add-wins)
    edge = (ra, b)
    ok = (edge in eE) and (edge not in eEp)
    print("  E  = {a=add x, ra=rem x, b=add x}   loOn(E) edges:  %s"
          % sorted(eE))
    print("  E' = E + {rb=rem x}                  loOn(E') edges: %s"
          % sorted(eEp))
    print("  VANISHING EDGE  ra -> b : in loOn(E) = %s, in loOn(E') = %s"
          % (edge in eE, edge in eEp))
    print("     b is unabsorbed in E (no later non-comm successor there); in "
          "E' its own rem rb absorbs it, so the rc edge ra->b DISAPPEARS.")
    print("     -> a witness of the SMALLER version E (which must place ra "
          "before b) is not forced by, and can be VIOLATED under, E'.")
    print("     This is loOn_mono / the defeater: witnesses do not extend "
          "along store growth, which is exactly why def:ralin drops the "
          "witness-EXTENSION clause the published paper's binary spec carries.")
    print("     EXPECT ra->b present in loOn(E), absent in loOn(E') -> %s"
          % ("PASS" if ok else "*** FAIL ***"))
    mm += 0 if ok else 1

    # Observable vs internal reading, demonstrated on the two routes.
    print("\n  Observable / internal reading:")
    print("   - CYCLIC route (ORSet, the certified separator): plain-RA-lin "
          "is VACUOUS (a cyclic relation has NO extending witness list at "
          "all), so there is no plain fold to be eqObs-compared. Strictly "
          "stronger than observable; NOT eqObs-absorbable.")
    print("   - FOLD-VALUE route (only inside absorber-NON-RA / VC3-violating "
          "specs): op differs from every plain fold as a STATE, so for a flat "
          "datatype (query = identity) it is OBSERVABLE; coarsening eqObs to "
          "identify op with a plain fold turns it INTERNAL. Either way it "
          "never lifts to a certified config-level separator (search: 0).")
    print()
    return mm


# ---------------------------------------------------------------------------
# Driver.
# ---------------------------------------------------------------------------

def main():
    args = [x for x in sys.argv[1:] if not x.startswith("--")]
    full = "--full" in sys.argv
    seed = int(args[0]) if args else 114
    random.seed(seed)
    print("# absorber dichotomy check (task #114 phase 3)  seed=%d full=%s\n"
          % (seed, full))
    print("VERDICT: H-loadbearing. The absorber is load-bearing via "
          "ACYCLICITY: dropping it makes the linearization order CYCLIC on "
          "reachable ORSet histories, so plain-RA-lin admits no witness. The "
          "canonical ORSet (all 8 VCs green, mechanized RA-lin) is the "
          "separator.\n")
    mm = 0
    mm += run_calibration()
    mm += run_search(full)
    mm += run_antitonicity()
    print("# hand-derived expectation mismatches: %d" % mm)
    sys.exit(1 if mm else 0)


if __name__ == "__main__":
    main()
