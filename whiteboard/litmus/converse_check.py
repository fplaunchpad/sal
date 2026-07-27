#!/usr/bin/env python3
"""converse_check.py -- task #114 phase 2: the RESTRICTED CONVERSE of adequacy.

Adequacy is  VC1..VC8 => RA-lin.  The FULL converse (RA-lin => all 8 VCs) is
already REFUTED (phase 1: VC1/VC2/VC3/VC4 have RA-linearizable violators).  The
open completeness statement is the RESTRICTED converse:

  H-CONVERSE:  every CANONICAL flat MRDT that is RA-linearizable satisfies the
  FOUR CORE VCs {VC5-empty, VC6, VC7, VC8} on its REACHABLE states.

  REFUTED by a canonical-RA-lin datatype that reddens a core VC on a REACHABLE
  state (a genuine negative: an RA-lin datatype the VC set cannot certify).  A
  clean sweep VALIDATES it and pins the pen-and-paper derivation for Lean.

canonical RA-lin (per whiteboard/ra-lin-definition-note.md): for every reachable
weakly-closed event set E, EXACTLY ONE loOn(E)-respecting fold exists (EXISTENCE
+ CONVERGENCE => acyclic + convergent, so sig(E) is well-defined), AND the merge
is that fold -- the JOIN  mergeL(sig(E1&E2), sig(E1), sig(E2)) = sig(E1|E2) on
every mergeable pair of weakly-closed sets.

DOMAIN SUBTLETY (crucial).  A core-VC violation counts as a converse
counterexample ONLY on a reachable canonical input (a sig-fold of a reachable
weakly-closed set / a canonical LCA triple (sig(E1&E2), sig(E1), sig(E2))).  The
reused config-driven checkers vc5..8_on_config evaluate mergeL/do only on
sig-folds of weakly-closed subsets of honest DAGs, so their domain IS
reachable-canonical by construction.  (The VC6/VC7 nested-merge slots resolve to
canonical states exactly when the datatype is RA-lin, via the Join; for
non-RA-lin specs -- never converse candidates -- they may not.)

CALIBRATION (mandatory).  The four phase-1 separators each VIOLATE a core VC on
a reachable state, so the checkers CAN detect a violation; but each is
NON-RA-lin, so the oracle REJECTS it -- none is a converse counterexample.
ORSet and MVR are RA-lin with all four core VCs green (positive anchors).

VC8 DECOMPOSITION (the directed probe).  VC8 = [Join at (U-e, down(e)):
mergeL(B,A,e(B)) = sig(U)]  AND  [causal clause: sig(U) = e(sig(U-e)) for every
loOn(U)-maximal e].  The causal clause is forced by CONVERGENCE alone (loOn is
antitone in the event set, so a loOn(U-e)-respecting enum is loOn(U)-respecting;
appending the maximal e yields sig(U) = e(sig(U-e))).  So VC8 carries no content
beyond canonical-RA-lin: its extra-over-the-Join half IS convergence.  The
harness tests the causal clause on every convergent spec (predict: never fails)
to isolate the two halves.

Run:  python3 whiteboard/litmus/converse_check.py [--full] [seed]
      default S2x2 + S2x3 (>3000 specs); --full adds S3.  Exit 0 iff every
      hand-derived calibration verdict matches AND no converse counterexample /
      per-config implication violation / causal-clause violation is found.
"""
import os
import sys
import random

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from itertools import combinations

from vc_minimality_check import (
    gen_config, Sigma, closed_subsets, is_loOn_maximal, weakly_closed,
    vc6_on_config, vc7_on_config, vc8_on_config,
    make_orset, make_mvr, make_vc7_dcc, make_vc8_awsetf,
    ORSET_APPCHOICES, MVR_APPCHOICES, DCC_APPCHOICES, AWF_APPCHOICES,
)
from vc_synthesis_search import (
    space_s2x2, space_s2x3, space_s3,
    make_changewins, make_poisoned_empty, make_pure_or, make_delta_xor,
)


# ----------------------------------------------------------------------------
# The canonical-RA-lin oracle, on one honest DAG.
# ----------------------------------------------------------------------------

def canon_ra_lin_on_config(spec, C, sig):
    """(conv_ok, join_ok, witness) for THIS config.
      conv_ok : every weakly-closed subset has EXACTLY ONE loOn-fold
                (existence + convergence => sig(.) well-defined).
      join_ok : mergeL(sig(E1&E2), sig(E1), sig(E2)) = sig(E1|E2), all pairs."""
    cs = closed_subsets(spec, C, cap=6)
    for E in cs:
        if len(sig.folds(E)) != 1:
            return (False, False, ("nonconv/cyclic", len(E), len(sig.folds(E))))
    for E1 in cs:
        for E2 in cs:
            m = spec.mergeL(sig.canon(E1 & E2), sig.canon(E1), sig.canon(E2))
            u = sig.canon(E1 | E2)
            if m != u:
                return (True, False, ("join", len(E1), len(E2), m, u))
    return (True, True, None)


# ----------------------------------------------------------------------------
# Core-VC verdicts on reachable-canonical inputs (the reused config checkers
# already restrict their domain to sig-folds of weakly-closed subsets).
# ----------------------------------------------------------------------------

def vc5_reachable_on_config(spec, C, sig):
    """feasible_init on the REACHABLE-CANONICAL domain: mergeL(init,init,s) = s
    for s a fold of a WEAKLY-CLOSED (reachable) subset only.  This is the Join
    at (empty, ev).  NOTE: the phase-1 vc5_on_config over-quantifies to
    NON-closed ev on small configs; that surplus is the 'stated-stronger-than-
    consumed' part of feasible_init, OUTSIDE the reachable-canonical converse
    domain (see vc5_surplus_on_config), and is not a converse counterexample."""
    for ev in closed_subsets(spec, C, cap=6):
        for s in sig.folds(ev):
            if spec.mergeL(spec.init, spec.init, s) != s:
                return False, ("VC5", len(ev), s)
    return True, None


def vc5_surplus_on_config(spec, C, sig):
    """A VC5 (feasible_init) violation on a NON-weakly-closed ev: a fold of a
    non-causally-closed set, hence NOT a reachable state.  Diagnostic for the
    domain analysis; never a converse counterexample."""
    evs = C.events
    for r in range(len(evs) + 1):
        for c in combinations(evs, r):
            ev = frozenset(c)
            if weakly_closed(spec, C, ev):
                continue
            for s in sig.folds(ev):
                if spec.mergeL(spec.init, spec.init, s) != s:
                    return True
    return False


CORE_FNS = ((5, vc5_reachable_on_config), (6, vc6_on_config),
            (7, vc7_on_config), (8, vc8_on_config))


def core_reds_on_config(spec, C, sig):
    reds = {}
    for i, fn in CORE_FNS:
        ok, w = fn(spec, C, sig)
        if not ok:
            reds[i] = w
    return reds


def vc5empty_red(spec):
    """VC5-empty (VC5-degree-zero): mergeL(init,init,init) = init.  Config-free;
    it is the Join instance at E1 = E2 = empty (two fresh replicas merging)."""
    return spec.mergeL(spec.init, spec.init, spec.init) != spec.init


def vc8_causal_clause_on_config(spec, C, sig):
    """The convergence half of VC8, MERGE-FREE: for every weakly-closed U with a
    unique fold and every loOn(U)-maximal e,  sig(U) = e(sig(U-e))."""
    for U in closed_subsets(spec, C, cap=6):
        su = sig.canon(U)
        if su is None:
            continue
        for e in U:
            if not is_loOn_maximal(spec, C, U, e):
                continue
            sue = sig.canon(U - {e})
            if sue is None:
                continue
            if spec.do(sue, e) != su:
                return False, ("VC8-causal", len(U), spec.do(sue, e), su)
    return True, None


# ----------------------------------------------------------------------------
# Per-spec evaluation over sampled honest DAGs.
# ----------------------------------------------------------------------------

HUNT_BUDGET = ((8, 4), (4, 5))         # (count, n_events) per seed, the hunt
CALIB_BUDGET = ((20, 4), (10, 5))      # heavier: reliably hits each countermodel


def eval_spec(spec, appchoices, budgets=HUNT_BUDGET, seeds=(114, 7, 2026)):
    ra_lin = True                 # oracle passes on ALL sampled configs
    conv_all = True
    core_reds = {}                # union of core-VC reds (with a witness)
    impl_viol = []                # config where oracle PASSED yet a core VC red
    causal_viol = []              # convergent config where VC8-causal fails
    surplus = 0                   # RA-lin config with a VC5 surplus (non-closed ev)
    for seed in seeds:
        rng = random.Random(seed)
        for count, n in budgets:
            for _ in range(count):
                C = gen_config(spec, rng, n, appchoices)
                sig = Sigma(spec, C)
                conv_ok, join_ok, w = canon_ra_lin_on_config(spec, C, sig)
                oracle_ok = conv_ok and join_ok
                conv_all = conv_all and conv_ok
                ra_lin = ra_lin and oracle_ok
                reds = core_reds_on_config(spec, C, sig)
                for i, wi in reds.items():
                    core_reds.setdefault(i, wi)
                if oracle_ok and reds:
                    impl_viol.append((seed, n, sorted(reds)))
                if oracle_ok and vc5_surplus_on_config(spec, C, sig):
                    surplus += 1
                if conv_ok:
                    cok, cw = vc8_causal_clause_on_config(spec, C, sig)
                    if not cok:
                        causal_viol.append((seed, n, cw))
    if vc5empty_red(spec):
        core_reds.setdefault(5, ("VC5-empty", "mergeL(init,init,init)!=init"))
    return dict(ra_lin=ra_lin, conv_all=conv_all, core_reds=core_reds,
                impl_viol=impl_viol, causal_viol=causal_viol, surplus=surplus)


# ----------------------------------------------------------------------------
# CALIBRATION: hand-derived expected verdicts.  exp_reds = the core VC each
# separator reddens on a REACHABLE state; exp_ra = the oracle verdict (all four
# separators are NON-RA-lin, so NOT converse counterexamples; the two anchors
# are RA-lin with NO core red).
# ----------------------------------------------------------------------------

CALIB = [
    ("ORSet (add-wins set)",       make_orset,          ORSET_APPCHOICES, True,  set()),
    ("MVR (all-commuting)",        make_mvr,            MVR_APPCHOICES,   True,  set()),
    ("pure-or G-set (control)",    make_pure_or,        None,             True,  set()),
    ("delta counter mod2 a^b^l",   make_delta_xor,      None,             True,  set()),
    ("poisoned-empty G-set",       make_poisoned_empty, None,             False, {5}),
    ("change-wins flag",           make_changewins,     None,             False, {6}),
    ("double-counting counter",    make_vc7_dcc,        DCC_APPCHOICES,   False, {7}),
    ("AWSetF3 (#57 separator)",    make_vc8_awsetf,     AWF_APPCHOICES,   False, {8}),
]


def run_calibration():
    print("== CALIBRATION (oracle must REJECT separators; checkers must DETECT "
          "their reachable core-VC red; anchors RA-lin with no red) ==")
    fails = 0
    for name, make, appch, exp_ra, exp_reds in CALIB:
        spec = make()
        ac = appch if appch is not None else spec.appchoices
        r = eval_spec(spec, ac, budgets=CALIB_BUDGET)
        reds = set(r["core_reds"])
        if exp_ra:
            ok = r["ra_lin"] and reds == set()
        else:
            ok = (not r["ra_lin"]) and exp_reds <= reds
        conv_ce = r["ra_lin"] and bool(reds)     # a real converse counterexample
        print("  %-30s ra_lin=%-5s core_reds=%-9s causal_viol=%d  -> %s%s"
              % (name[:30], r["ra_lin"], sorted(reds), len(r["causal_viol"]),
                 "OK" if ok else "*** MISMATCH ***",
                 "  <<< CONVERSE COUNTEREXAMPLE" if conv_ce else ""))
        if not ok:
            fails += 1
    return fails


# ----------------------------------------------------------------------------
# THE HUNT.
# ----------------------------------------------------------------------------

def hunt(name, spec_iter, seeds=(114, 7, 2026), budgets=HUNT_BUDGET,
         progress=2000):
    visited = unique = ra_lin_n = conv_n = surplus_specs = 0
    counterexamples = []          # RA-lin spec that reddens a core VC (H-CONVERSE ce)
    impl_viols = []               # per-config: oracle passed yet core VC red
    causal_viols = []             # convergent spec: VC8-causal-clause fails
    ra_lin_examples = []          # sample RA-lin specs (all core VCs green)
    seen = set()
    for spec in spec_iter:
        visited += 1
        if progress and visited % progress == 0:
            print("  ... %s: %d visited, %d unique, %d ra-lin, %d ce"
                  % (name, visited, unique, ra_lin_n, len(counterexamples)),
                  flush=True)
        s = spec.signature()
        if s in seen:
            continue
        seen.add(s)
        unique += 1
        r = eval_spec(spec, spec.appchoices, budgets=budgets, seeds=seeds)
        if r["conv_all"]:
            conv_n += 1
        if r["surplus"]:
            surplus_specs += 1
        if r["ra_lin"]:
            ra_lin_n += 1
            if r["core_reds"]:
                counterexamples.append((spec.describe(), sorted(r["core_reds"])))
            elif len(ra_lin_examples) < 10 and any(
                    t not in ((0, 0), (0, 1)) for t in spec.do_tables):
                ra_lin_examples.append(spec.describe())    # skip trivial do
        for v in r["impl_viol"]:
            impl_viols.append((spec.describe(), v))
        for v in r["causal_viol"]:
            causal_viols.append((spec.describe(), v))
    return dict(name=name, visited=visited, unique=unique, ra_lin=ra_lin_n,
                conv=conv_n, surplus_specs=surplus_specs,
                counterexamples=counterexamples,
                impl_viols=impl_viols, causal_viols=causal_viols,
                ra_lin_examples=ra_lin_examples)


def report(res):
    print("\n== %s: %d visited (%d unique), %d canonical-RA-lin, %d convergent =="
          % (res["name"], res["visited"], res["unique"], res["ra_lin"],
             res["conv"]))
    print("  H-CONVERSE counterexamples (RA-lin spec reddening a core VC on a "
          "reachable state): %d" % len(res["counterexamples"]))
    for d, reds in res["counterexamples"][:12]:
        print("      *** %s   core_reds=%s" % (d, reds))
    print("  per-config implication violations (oracle PASSED, core VC red on "
          "the SAME config): %d" % len(res["impl_viols"]))
    for d, v in res["impl_viols"][:12]:
        print("      *** %s   %s" % (d, v))
    print("  VC8 causal-clause violations on convergent specs "
          "(sig(U) != e(sig(U-e))): %d" % len(res["causal_viols"]))
    for d, v in res["causal_viols"][:12]:
        print("      *** %s   %s" % (d, v))
    print("  DOMAIN DIAGNOSTIC: RA-lin specs with a VC5 SURPLUS violation on a "
          "NON-weakly-closed ev (feasible_init's stated surplus, OUTSIDE the "
          "reachable-canonical converse domain; not a counterexample): %d"
          % res["surplus_specs"])
    if res["ra_lin_examples"]:
        print("  sample RA-lin specs with ALL core VCs green:")
        for d in res["ra_lin_examples"]:
            print("      %s" % d)


def main():
    full = "--full" in sys.argv
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    seed = int(args[0]) if args else 114
    print("# converse check (task #114 phase 2)  seed=%d  full=%s\n" % (seed, full))

    fails = run_calibration()

    total_ce = total_impl = total_causal = total_visited = total_surplus = 0
    spaces = [("S2x2", space_s2x2()), ("S2x3", space_s2x3())]
    if full:
        spaces.append(("S3", space_s3(seed + 2, 4000)))
    for nm, it in spaces:
        res = hunt(nm, it)
        report(res)
        total_ce += len(res["counterexamples"])
        total_impl += len(res["impl_viols"])
        total_causal += len(res["causal_viols"])
        total_surplus += res["surplus_specs"]
        total_visited += res["visited"]

    print("\n# ============================================================")
    print("# SEARCH BOUND: %d specs visited across %d spaces"
          % (total_visited, len(spaces)))
    print("# H-CONVERSE counterexamples (RA-lin + core VC red on reachable "
          "state): %d" % total_ce)
    print("# per-config implication violations (reachable-canonical domain): %d"
          % total_impl)
    print("# VC8 causal-clause violations (convergent): %d" % total_causal)
    print("# VC5 surplus (RA-lin, viol on NON-closed ev; domain diagnostic, "
          "NOT counterexamples): %d specs" % total_surplus)
    print("# calibration mismatches: %d" % fails)
    verdict = (total_ce == 0 and total_impl == 0 and total_causal == 0
               and fails == 0)
    print("# VERDICT: %s" % ("H-CONVERSE VALIDATED (clean sweep)" if verdict
                             else "*** SEE COUNTEREXAMPLES / MISMATCHES ***"))
    sys.exit(0 if verdict else 1)


if __name__ == "__main__":
    main()
