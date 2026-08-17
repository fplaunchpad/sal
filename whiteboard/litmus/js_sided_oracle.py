#!/usr/bin/env python3
"""Emit the canonical Fugue sided-model reads for the JS lockstep gate."""
import json
import litmus as L
from embed_sided import SidedChain, mkD, gauntlet

D = mkD(SidedChain, 'fugue')
bad = gauntlet(D, expect_l19_clean=True)
if bad:
    raise SystemExit('reference Fugue gauntlet failed: ' + repr(bad))

def run(state, ops):
    return L.run_replica(D, state, ops)[0]

cases = []
for name, _, ops in L.SEQ_TESTS:
    D.begin(); s = run(D.init(), ops)
    cases.append({'name': name, 'kind': 'seq', 'ops': ops, 'read': D.read(s)})
for name, lops, aops, bops, _ in L.MERGE_TESTS:
    D.begin(); l = run(D.init(), lops); a = run(D.copy(l), aops); b = run(D.copy(l), bops)
    cases.append({'name': name, 'kind': 'merge', 'lca': lops, 'a': aops, 'b': bops,
                  'read': D.read(D.merge(l, a, b))})

print(json.dumps(cases, separators=(',', ':')))
