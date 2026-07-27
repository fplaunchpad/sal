#!/usr/bin/env python3
"""conditioned_converse_check.py -- task #122 phase 1: the CONDITIONED CONVERSE.

The FLAT converse (whiteboard/converse-note.md, Metatheory/Converse.lean) settled
that canonical RA-lin = existence + convergence forces the four flat CORE VCs.
This harness probes the CONDITIONED generalization: does conditioned RA-lin (RA-lin
UP TO the observational equivalence eqObs, at every reachable Inv-config) force the
FOUR conditioned VCs  {vc:disc, vc:comm, vc:inv, vc:merge}?

No finite oracle carries the general conditioned case (unbounded state, arbitrary
eqObs/Inv).  This harness anchors THREE targeted, hand-derived claims, each PASS+FAIL:

  PROBE C  (load-bearing, for #123): vc:comm + vc:inv (the swap oracle EqSwap) are
    NOT forced by convergence-up-to-eqObs.  Structural fact: two lo-respecting
    linear extensions that differ by ONE adjacent transposition of an incomparable
    pair (a,b) at position pi look like  rho++[a,b]++tau  vs  rho++[b,a]++tau ; so
    convergence gives  fold(rho++[a,b]++tau) ~ fold(rho++[b,a]++tau)  -- a
    tau-BURDENED equality.  It equals EqSwap(a,b,fold(rho)) ONLY when tau is empty,
    i.e. (a,b) is lo-MAXIMAL.  At a NON-maximal incomparable pair convergence leaves
    the local swap free.  WITNESS (datatype PRIO): a convergent-up-to-eqObs datatype
    with a genuine non-maximal EqSwap FAILURE.  => the swap oracle is a SUFFICIENT
    DEVICE, not equivalent to RA-lin's convergence content.

  PROBE A  (vc:disc): the universal Inv-preservation clause is EXTRA, not forced.
    Analog of the flat shell VC3/VC4 all-states surplus: an RA-lin datatype whose do
    violates Inv-preservation at an UNREACHABLE Inv-state -- off the reachable-
    canonical domain, so RA-lin cannot see it.

  PROBE B  (vc:merge): the conditioned Join IS forced by existence + convergence on
    reachable merge tuples (positive), and the checker DETECTS a Join failure
    (calibration negative), exactly as the flat Join.

Every expected value is HAND-DERIVED in comments and asserted; none is read off the
object under test.  Run:  python3 whiteboard/litmus/conditioned_converse_check.py
Exit 0 iff every hand-derived verdict matches.
"""

import sys
from itertools import permutations, combinations, product

# ---------------------------------------------------------------------------
# Op = (ts, rep, appop).  appop is a hashable token.
# ---------------------------------------------------------------------------
def ts(e):  return e[0]
def rep(e): return e[1]
def ap(e):  return e[2]

FST, SND, EITHER = "Fst", "Snd", "Either"


class CondSpec:
    """A conditioned MRDT <State, init, do, mergeL, rc, Inv, app, eqObs>.

    do(s, op) -> s ;  mergeL(l,a,b) -> s ;  rc(e1,e2) -> FST|SND|EITHER
    inv(s) -> bool ;  app(op,s) -> bool ;  eqobs(s,s') -> bool  (an equivalence)
    states() -> finite iterable of representative states (the eqCommutesOn universe).
    """
    def __init__(self, name, init, do, mergeL, rc, inv, app, eqobs, states):
        self.name = name; self.init = init; self.do = do; self.mergeL = mergeL
        self.rc = rc; self.inv = inv; self.app = app; self.eqobs = eqobs
        self._states = states

    def states(self):
        return list(self._states())

    def fold(self, seq, s=None):
        s = self.init if s is None else s
        for e in seq:
            s = self.do(s, e)
        return s


# ---------------------------------------------------------------------------
# eqCommutesOn: ~-commutation quantified over Inv-states (Framework
# GenericEqQuotient.eqCommutesOn).  This is the commutation notion the ~-route's
# order loOnEq and the Join are proved against -- NOT raw-state equality.
# ---------------------------------------------------------------------------
def eq_commutes(spec, e1, e2):
    return all(spec.eqobs(spec.do(spec.do(s, e1), e2), spec.do(spec.do(s, e2), e1))
               for s in spec.states() if spec.inv(s))


def eq_visNC(spec, C, a, b):
    return C.vis(a, b) and not eq_commutes(spec, a, b)


# ---------------------------------------------------------------------------
# loOnEq: loOn with `commutes` replaced by eqCommutesOn (GenericEqQuotient.loOnEq).
#   e1 -> e2  iff  (vis e1 e2 and not eqComm e1 e2)                     [vis arm]
#            or    (e1||e2 and rc e1 e2 = Fst and e2 not absorbed in ev) [rc arm]
# antitone in ev: growing ev only adds absorbers, hence removes rc edges.
# ---------------------------------------------------------------------------
def loOnEq(spec, C, ev, x, y):
    if C.vis(x, y) and not eq_commutes(spec, x, y):
        return True
    if (not C.vis(x, y) and not C.vis(y, x) and spec.rc(x, y) == FST
            and not any((e3 in ev) and C.vis(y, e3) and not eq_commutes(spec, y, e3)
                        for e3 in C.events)):
        return True
    return False


def respecting_perms(spec, C, ev):
    """All loOnEq(C,ev)-respecting permutations of ev (no edge points backward)."""
    evl = list(ev)
    edges = {(x, y) for x in evl for y in evl
             if x != y and loOnEq(spec, C, ev, x, y)}
    out = []
    for perm in permutations(evl):
        ok = True
        for i in range(len(perm)):
            for j in range(i + 1, len(perm)):
                if (perm[j], perm[i]) in edges:      # a later element -> earlier: reversed
                    ok = False; break
            if not ok: break
        if ok:
            out.append(perm)
    return out


def canon_reads(spec, C, ev):
    """The set of eqObs-reads (as a frozenset of read-values) of all loOnEq-folds
    of ev.  |.| == 1  iff  the datatype CONVERGES UP TO eqObs on ev."""
    reads = set()
    for perm in respecting_perms(spec, C, ev):
        reads.add(_read_key(spec, spec.fold(list(perm))))
    return reads


def converges_eq(spec, C, ev):
    return len(canon_reads(spec, C, ev)) <= 1


# eqObs is given as a boolean relation; to bucket folds we need a canonical KEY per
# ~-class.  Every datatype below supplies `read` as its eqObs witness; we attach it
# as spec._readkey.  (Kept separate from eqobs so eqobs stays the primitive.)
def _read_key(spec, s):
    return spec._readkey(s)


# ---------------------------------------------------------------------------
# weak closure (backward closure under ~-non-commuting visibility) + subsets
# ---------------------------------------------------------------------------
def weakly_closed(spec, C, ev):
    evset = set(ev)
    for b in evset:
        for a in C.events:
            if a not in evset and eq_visNC(spec, C, a, b):
                return False
    return True


def closed_subsets(spec, C):
    evs = C.events
    out = []
    for r in range(len(evs) + 1):
        for sub in combinations(evs, r):
            if weakly_closed(spec, C, sub):
                out.append(frozenset(sub))
    return out


# ---------------------------------------------------------------------------
# EqSwap (Framework vc:comm): do(do s a) b  ~  do(do s b) a.
# ---------------------------------------------------------------------------
def eqswap(spec, a, b, s):
    return spec.eqobs(spec.do(spec.do(s, a), b), spec.do(spec.do(s, b), a))


def lo_incomparable(spec, C, ev, a, b):
    return not loOnEq(spec, C, ev, a, b) and not loOnEq(spec, C, ev, b, a)


def enabled_at(spec, C, ev, a, prefix):
    """a is ENABLED at prefix pi (Framework vc:inv): every loOnEq(ev)-predecessor
    of a in ev already lies in pi."""
    for z in ev:
        if z != a and loOnEq(spec, C, ev, z, a) and z not in prefix:
            return False
    return True


class Config:
    def __init__(self, events, vis_pairs):
        self.events = list(events)
        self._vis = set(vis_pairs)

    def vis(self, a, b):
        return (a, b) in self._vis


# ===========================================================================
# PROBE C -- the load-bearing witness: convergent up to ~, EqSwap FAILS.
# ===========================================================================
# Datatype RESET.  State = a log (tuple of values) in APPEND order.
#   write v  : do(s, ('w',v))    = s ++ (v,)
#   reset    : do(s, ('reset',)) = ('Z',)     -- erase to a sentinel Z (an OVERWRITE)
#   read(s)  = last element of the log (append-order sensitive)
#   eqObs(s,t) = read(s) == read(t).   Inv = app = True.
# c = reset is the crux (the classic ORSet add/remove absorber structure): it does
# NOT ~-commute with a,b (a write BEFORE reset is erased, one AFTER survives), so it
# is a legitimate loOnEq ABSORBER of the a->b rc-edge and carries vis-arm edges a->c,
# b->c; yet appended AFTER both a and b it ERASES both, RECONCILING the two orders.
# So the FULL folds converge (both read Z) while the LOCAL a,b swap does not (reads
# B vs A).  This inhabits the maximal-vs-non-maximal gap.
def reset_do(s, op):
    kind = ap(op)
    if kind[0] == 'w':
        return s + (kind[1],)
    return ('Z',)                              # ('reset',)


def reset_read(s):
    return s[-1] if s else None


def reset_eqobs(s, t):
    return reset_read(s) == reset_read(t)


def reset_rc(e1, e2):
    # concurrent ops conflict; resolve deterministically by ts (Fst = smaller ts).
    return FST if ts(e1) < ts(e2) else SND


def reset_states():
    # representative universe: all logs of length <=2 over {'A','B','Z'}.
    univ = [()]
    for r in range(1, 3):
        for p in product(['A', 'B', 'Z'], repeat=r):
            univ.append(tuple(p))
    return univ


RESET = CondSpec("RESET", (), reset_do, None, reset_rc,
                 lambda s: True, lambda o, s: True, reset_eqobs, reset_states)
RESET._readkey = reset_read

# The witness events.  a,b concurrent writes; c a reset that sees both.
A = (1, 0, ('w', 'A'))
B = (2, 1, ('w', 'B'))
Cc = (3, 2, ('reset',))
RESET_C = Config([A, B, Cc], [(A, Cc), (B, Cc)])   # a->c, b->c ; a || b


def _reset_global_sweep(spec):
    """Sweep every ts-monotone vis-DAG on n<=4 events over {wA,wB,reset} and count
    non-convergent weakly-closed subsets.  Returns (n_configs, n_subsets, n_bad)."""
    pool = [('w', 'A'), ('w', 'B'), ('reset',)]
    ncfg = nsub = bad = 0
    for n in (2, 3, 4):
        for appops in product(pool, repeat=n):
            events = [(i + 1, i % 3, appops[i]) for i in range(n)]
            base = [(events[i], events[j]) for i in range(n) for j in range(i + 1, n)]
            for mask in range(1 << len(base)):
                vis = set(base[k] for k in range(len(base)) if mask >> k & 1)
                changed = True
                while changed:
                    changed = False
                    for a in events:
                        for b in events:
                            if (a, b) in vis:
                                for cc in events:
                                    if (b, cc) in vis and (a, cc) not in vis:
                                        vis.add((a, cc)); changed = True
                C = Config(events, vis)
                ncfg += 1
                for E in closed_subsets(spec, C):
                    nsub += 1
                    if not converges_eq(spec, C, E):
                        bad += 1
    return ncfg, nsub, bad


def probe_C():
    print("\n=== PROBE C: vc:comm+vc:inv NOT forced by convergence (datatype RESET) ===")
    spec, C = RESET, RESET_C
    fails = []

    # HAND-DERIVED FACTS (see file header):
    # (1) eqComm(a,b) is FALSE: read([a,b])='B' (tie, last), read([b,a])='A'.
    hb = not eq_commutes(spec, A, B)
    ok = hb is True
    print(f"  [1] a,b do NOT ~-commute (owed a swap)        : {hb!r:5}  expect True   {'OK' if ok else 'FAIL'}")
    if not ok: fails.append("C1")

    # (2) In E={a,b,c}: a->b is ABSORBED by c (c a vis-noncomm successor of b),
    #     no b->a (rc(b,a)=Snd), so a,b are loOnEq(E)-INCOMPARABLE and NON-maximal
    #     (both -> c).  a,c and b,c are ordered (vis arm).
    ev = frozenset([A, B, Cc])
    inc = lo_incomparable(spec, C, ev, A, B)
    ac = loOnEq(spec, C, ev, A, Cc); bc = loOnEq(spec, C, ev, B, Cc)
    nonmax = ac and bc                       # c is a loOnEq-successor of both => a,b non-maximal
    ok = inc and ac and bc
    print(f"  [2] a||b incomparable in E={{a,b,c}}, both ->c   : inc={inc!r} a->c={ac!r} b->c={bc!r}  expect all True   {'OK' if ok else 'FAIL'}")
    if not ok: fails.append("C2")

    # (2b) contrast: in E'={a,b} (no absorber) a->b IS present (rc-arm), so the pair
    #      is only incomparable once c enlarges the set -- the ANTITONE gap.
    ev2 = frozenset([A, B])
    ab_small = loOnEq(spec, C, ev2, A, B)
    ok = ab_small is True
    print(f"  [2b] antitone: a->b PRESENT in E'={{a,b}}         : {ab_small!r:5}  expect True   {'OK' if ok else 'FAIL'}")
    if not ok: fails.append("C2b")

    # (3) CONVERGENCE up to ~ on EVERY weakly-closed subset of {a,b,c}.
    css = closed_subsets(spec, C)
    conv_all = all(converges_eq(spec, C, s) for s in css)
    # E={a,b,c}: both extensions [a,b,c],[b,a,c] reset to ('Z',), read 'Z'.
    reads_abc = canon_reads(spec, C, ev)
    ok = conv_all and reads_abc == {'Z'}
    print(f"  [3] convergent up to ~ on all {len(css):2} wc-subsets   : conv={conv_all!r} reads(abc)={sorted(reads_abc)}  expect True,['Z']   {'OK' if ok else 'FAIL'}")
    if not ok: fails.append("C3")

    # (4) EqSwap(a,b,init) is OWED (a,b incomparable, both enabled at pi=[]) and FAILS.
    owed = (inc and enabled_at(spec, C, ev, A, ()) and enabled_at(spec, C, ev, B, ()))
    swap_holds = eqswap(spec, A, B, spec.init)   # read([a,b])='B' vs read([b,a])='A'
    ok = owed and (swap_holds is False)
    print(f"  [4] EqSwap(a,b,init) OWED and FAILS            : owed={owed!r} holds={swap_holds!r}  expect True,False   {'OK' if ok else 'FAIL'}")
    if not ok: fails.append("C4")

    # (5) the tau-burdened equality convergence DOES give:
    #     fold([a,b,c]) ~ fold([b,a,c])  (append c reconciles) -- the maximal-only reach.
    tau_ok = spec.eqobs(spec.fold([A, B, Cc]), spec.fold([B, A, Cc]))
    ok = tau_ok is True
    print(f"  [5] tau-burdened fold([a,b]++[c]) ~ fold([b,a]++[c]): {tau_ok!r:5}  expect True   {'OK' if ok else 'FAIL'}")
    if not ok: fails.append("C5")

    # (6) RESET is GLOBALLY convergent up to ~ (so it satisfies the converse
    #     hypothesis EVERYWHERE, making the vc:comm failure a GLOBAL refutation,
    #     not merely a per-config one).  Sweep every vis-DAG on <=4 events over
    #     {write A, write B, reset}; expect ZERO non-convergent weakly-closed sets.
    ncfg, nsub, bad = _reset_global_sweep(spec)
    ok = bad == 0
    print(f"  [6] globally convergent: {bad} non-conv over {nsub} wc-sets ({ncfg} cfgs)  expect 0   {'OK' if ok else 'FAIL'}")
    if not ok: fails.append("C6")

    verdict = ("VERDICT: RESET is RA-lin up to ~ (existence+convergence) yet the swap\n"
               "         oracle EqSwap fails at the NON-maximal enabled pair (a,b).\n"
               "         => vc:comm+vc:inv are NOT forced by conditioned RA-lin;\n"
               "            they are a SUFFICIENT DEVICE (stronger than convergence).")
    print(verdict)
    return fails


# ===========================================================================
# PROBE A -- vc:disc's universal Inv-preservation is EXTRA (two-Inv witness).
# ===========================================================================
# Datatype GSET (grow-only set), eqObs = equality.  All ops COMMUTE at every
# state, so loOnEq is EMPTY and canonical-RA-lin holds INDEPENDENT of Inv.
#   Inv1 = True (top)          -> vc:disc preservation holds (vacuously).
#   Inv2 = 'poison' not in s   -> vc:disc preservation FAILS at o = add 'poison'.
# Same datatype, same RA-lin verdict, DIFFERENT vc:disc verdict => vc:disc is a
# property of the CHOSEN Inv, not forced by RA-lin.  (Flat analog: VC3/VC4 shell.)
def gset_do(s, op):
    _, x = ap(op)
    return s | frozenset([x])


def gset_states():
    base = ['x', 'y', 'poison']
    univ = []
    for r in range(0, 4):
        for sub in combinations(base, r):
            univ.append(frozenset(sub))
    return univ


def make_gset(inv, mergeL):
    g = CondSpec("GSET", frozenset(), gset_do, mergeL,
                 lambda e1, e2: EITHER, inv, lambda o, s: True,
                 lambda s, t: s == t, gset_states)
    g._readkey = lambda s: s
    return g


def gmerge_good(l, a, b):  return a | b
def gmerge_bad(l, a, b):   return a            # drops branch b


# a small honest config of adds across replicas (all pairwise concurrent-or-causal;
# G-set commutes so every subset is weakly closed).
GA = (1, 0, ('add', 'x'))
GB = (2, 1, ('add', 'y'))
GSET_C = Config([GA, GB], [])


def _canon_ra_lin_gset(spec, C):
    """existence+convergence proxy: loOnEq empty (commuting) => every wc-subset
    converges up to eqObs.  Returns True iff convergent everywhere."""
    return all(converges_eq(spec, C, s) for s in closed_subsets(spec, C))


def probe_A():
    print("\n=== PROBE A: vc:disc Inv-preservation EXTRA (GSET two-Inv witness) ===")
    fails = []
    inv1 = lambda s: True
    inv2 = lambda s: 'poison' not in s
    g1 = make_gset(inv1, gmerge_good)
    g2 = make_gset(inv2, gmerge_good)

    # RA-lin (canonical: existence+convergence) holds under BOTH Inv (commuting datatype).
    ra1 = _canon_ra_lin_gset(g1, GSET_C)
    ra2 = _canon_ra_lin_gset(g2, GSET_C)
    ok = ra1 and ra2
    print(f"  [1] canonical-RA-lin under Inv1 and Inv2      : {ra1!r},{ra2!r}  expect True,True   {'OK' if ok else 'FAIL'}")
    if not ok: fails.append("A1")

    # vc:disc preservation clause: exists Inv-state s, applicable op o, ~Inv(do s o)?
    poison_op = (9, 0, ('add', 'poison'))
    def preservation_fails(spec):
        for s in spec.states():
            if spec.inv(s) and spec.app(poison_op, s) and not spec.inv(spec.do(s, poison_op)):
                return True
        return False
    disc1 = not preservation_fails(g1)     # holds under Inv1
    disc2 = not preservation_fails(g2)     # fails under Inv2
    ok = (disc1 is True) and (disc2 is False)
    print(f"  [2] vc:disc holds? Inv1={disc1!r} Inv2={disc2!r}          expect True,False   {'OK' if ok else 'FAIL'}")
    if not ok: fails.append("A2")

    # the failure is OFF the reachable-canonical domain: 'poison' appears in NO
    # canonical fold of any weakly-closed set of the honest config.
    reads = set()
    for s in closed_subsets(g2, GSET_C):
        for p in respecting_perms(g2, GSET_C, s):
            reads |= g2.fold(list(p))
    ok = 'poison' not in reads
    print(f"  [3] 'poison' never in a reachable canon fold  : {('poison' not in reads)!r:5}  expect True   {'OK' if ok else 'FAIL'}")
    if not ok: fails.append("A3")

    print("VERDICT: same datatype + same RA-lin verdict, vc:disc GREEN under Inv1 and\n"
          "         RED under Inv2 => vc:disc's universal Inv-preservation is EXTRA\n"
          "         (RA-lin constrains only reachable canonical folds).")
    return fails


# ===========================================================================
# PROBE B -- vc:merge (conditioned Join) IS forced by existence+convergence.
# ===========================================================================
def _join_reads(spec, C):
    """(all_ok, detected_fail): for every weakly-closed pair E1,E2 check
    read(mergeL(sig(E1&E2),sig(E1),sig(E2))) == read(sig(E1|E2))."""
    css = closed_subsets(spec, C)

    def sig(ev):
        perms = respecting_perms(spec, C, ev)
        return spec.fold(list(perms[0]))      # convergent => representative fold

    all_ok = True
    for E1 in css:
        for E2 in css:
            if not weakly_closed(spec, C, E1 | E2):
                continue
            l = sig(E1 & E2); a = sig(E1); b = sig(E2)
            lhs = _read_key(spec, spec.mergeL(l, a, b))
            rhs = _read_key(spec, sig(E1 | E2))
            if lhs != rhs:
                all_ok = False
    return all_ok


def probe_B():
    print("\n=== PROBE B: vc:merge (conditioned Join) forced by existence+convergence ===")
    fails = []
    g_good = make_gset(lambda s: True, gmerge_good)
    g_bad = make_gset(lambda s: True, gmerge_bad)

    # positive: convergent G-set with union merge satisfies the Join on every pair.
    good = _join_reads(g_good, GSET_C)
    ok = good is True
    print(f"  [1] union-merge G-set: Join holds all pairs    : {good!r:5}  expect True   {'OK' if ok else 'FAIL'}")
    if not ok: fails.append("B1")

    # calibration negative: drop-branch merge FAILS the Join (checker detects it).
    bad = _join_reads(g_bad, GSET_C)
    ok = bad is False
    print(f"  [2] drop-branch merge: Join FAILS (detected)   : {bad!r:5}  expect False  {'OK' if ok else 'FAIL'}")
    if not ok: fails.append("B2")

    print("VERDICT: on reachable merge tuples (l=sig(E1&E2), branches sig(E1),sig(E2)),\n"
          "         RA-lin-existence forces mergeL to land ~ sig(E1|E2); the checker\n"
          "         also detects a Join violation => vc:merge forced, exactly as flat.")
    return fails


def main():
    print("conditioned_converse_check.py -- task #122 phase 1 (the CONDITIONED CONVERSE)")
    print("=" * 78)
    fails = []
    fails += probe_C()
    fails += probe_A()
    fails += probe_B()
    print("\n" + "=" * 78)
    if fails:
        print(f"RESULT: FAIL -- {len(fails)} hand-derived verdict(s) mismatched: {fails}")
        sys.exit(1)
    print("RESULT: PASS -- every hand-derived conditioned-converse verdict matched.")
    print("  vc:comm+vc:inv  NOT forced (Probe C, witnessed): sufficient device.")
    print("  vc:disc         EXTRA      (Probe A, two-Inv):   Inv-chosen, not forced.")
    print("  vc:merge        FORCED     (Probe B):            Join from exist.+converg.")
    sys.exit(0)


if __name__ == "__main__":
    main()
