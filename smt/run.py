#!/usr/bin/env python3
"""run.py -- reproduce the whole SMT VC-discharge campaign (task #99 / #49).

    python3 smt/run.py            # run everything, print the matrix, dump JSON

Emits smt/results/*.json and prints the instance x VC matrix with per-query
result (unsat = VC valid / sat = countermodel / timeout / unknown) and timing.
"""
import sys
import os
import json
import time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import z3
from vcgen import ALL_VCS, run_query, update_pointwise_ok
from instances.numeric import Counter, PN, Counter_BAD, PN_BAD
from instances.gset import GSet, GSet_BAD
from instances.orset import ORSet, ORSet_BAD
from instances.lww import LWW, LWW_BAD
from instances.rwset import RwSet, RwSet_EAGER, RwSet_ADDWINS
from instances.rwset_compact import RwSetC, RwSetC_MIN

TIMEOUT_MS = 10000

# The Lean ground truth: every listed flat instance discharged ALL eight VCs.
# So a faithful GOOD instance should return `unsat` (valid) for every VC.
# Documented exceptions: two ORSet VCs are configuration-conditioned in Lean
# (proved by hand via the canonical-state trichotomy), so their UNCONDITIONAL
# over-approximation is not valid -- the honest decidability-triage boundary.
LEAN_TRUE = {  # instances whose every VC Lean proved -> expect all `unsat`
    "Counter", "PN", "GSet", "ORSet", "LWW", "RwSetC(compacted)",
}
# (instance, vc) cells where the unconditional over-approx is EXPECTED not-unsat
CONFIG_CONDITIONED = {
    ("ORSet", "feasible_local_redistribute"),
    ("ORSet", "CDVC3"),
}

CALIB_GOOD = [Counter, PN, GSet, ORSet, LWW]
MUTATIONS = [Counter_BAD, PN_BAD, GSet_BAD, LWW_BAD, ORSet_BAD]
SUCCESS_49 = [RwSet, RwSetC]
KILLS_49 = [RwSet_EAGER, RwSet_ADDWINS, RwSetC_MIN]


def run_instance(m):
    rows = []
    for enc in ALL_VCS:
        for qy in enc(m):
            res, model, dt = run_query(qy, TIMEOUT_MS)
            rows.append(dict(vc=qy.vc, sub=qy.sub, result=res,
                             quantified=qy.quantified, time=round(dt, 3),
                             model=(model if res == "sat" else None)))
    up = update_pointwise_ok(m)
    if up is not None:
        res, model, dt = run_query(up, TIMEOUT_MS)
        rows.append(dict(vc=up.vc, sub=up.sub, result=res, quantified=False,
                         time=round(dt, 3), model=(model if res == "sat" else None)))
    return rows


def print_matrix(title, results, check_lean=False):
    print("\n" + "=" * 78)
    print(title)
    print("=" * 78)
    for name, rows in results:
        print("\n  %s" % name)
        for r in rows:
            q = "Q" if r["quantified"] else " "
            mark = ""
            if check_lean:
                cell = (name, r["vc"])
                if cell in CONFIG_CONDITIONED:
                    mark = "  <- config-conditioned (Lean hand-proof; over-approx)"
                elif name in LEAN_TRUE and r["result"] != "unsat":
                    mark = "  <- MISMATCH vs Lean!"
            tag = {"unsat": "unsat  (valid)", "sat": "SAT    (model)",
                   "timeout": "timeout", "unknown": "unknown"}[r["result"]]
            print("    [%s] %-28s %-24s %-14s %6.3fs%s"
                  % (q, r["vc"], r["sub"], tag, r["time"], mark))


def main():
    t0 = time.time()
    print("Solver: z3 (Python bindings) version %s" % z3.get_version_string())
    print("Per-query timeout: %d ms" % TIMEOUT_MS)
    allres = {}

    calib = [(m.name, run_instance(m)) for m in CALIB_GOOD]
    print_matrix("CALIBRATION -- true designs (expect unsat = matches Lean discharge)",
                 calib, check_lean=True)

    muts = [(m.name, run_instance(m)) for m in MUTATIONS]
    print_matrix("CALIBRATION -- mutations (expect >=1 SAT with countermodel)", muts)

    s49 = [(m.name, run_instance(m)) for m in SUCCESS_49]
    print_matrix("#49 -- remove-wins set (v1 literal, then compacted repair)", s49)

    kills = [(m.name, run_instance(m)) for m in KILLS_49]
    print_matrix("#49 -- kill tests (expect SAT countermodels)", kills)

    for label, group in [("calibration_good", calib), ("mutations", muts),
                         ("success_49", s49), ("kills_49", kills)]:
        allres[label] = {n: rows for n, rows in group}

    outdir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
    os.makedirs(outdir, exist_ok=True)
    meta = dict(solver="z3", version=z3.get_version_string(),
                timeout_ms=TIMEOUT_MS, wall_time_s=round(time.time() - t0, 2))
    with open(os.path.join(outdir, "results.json"), "w") as f:
        json.dump(dict(meta=meta, results=allres), f, indent=1)
    print("\nWrote %s  (wall %.1fs)" % (os.path.join(outdir, "results.json"),
                                        meta["wall_time_s"]))


if __name__ == "__main__":
    main()
