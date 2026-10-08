#!/usr/bin/env python3
"""Positive/negative controls for full VC-contract comparison (build templates first)."""
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
preamble = 'import AutomatedORSet\nimport ExpandedVCs\n' + (HERE / 'Audit.lean').read_text()
positive = '''
audit_vc_contract NeemExpansion.AutomatedORSet.automated_vcs against NeemExpansion.Exact.expanded_vcs
'''
negative = '''
open Sal.MRDTs Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
-- A spurious extra execution premise must not count as the unchanged contract.
theorem restricted {α : Type} [DecidableEq α] (_extra : False) :
    Raw.MergeVCs (ORSet.conflict α) (ORSet.RawReplay.representation (α := α))
      (ORSet.RawReplay.scheme (α := α)) := NeemExpansion.AutomatedORSet.automated_vcs
audit_vc_contract restricted against NeemExpansion.Exact.expanded_vcs
'''
with tempfile.TemporaryDirectory(prefix='sal-contract-controls-') as tmp:
    for name, body, expected in [('positive', positive, 0), ('negative', negative, 1)]:
        path = Path(tmp) / (name + '.lean')
        path.write_text(preamble + body)
        run = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                             text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert (run.returncode == 0) == (expected == 0), run.stdout
        marker = 'VC_CONTRACT_MATCH' if expected == 0 else 'VC contract mismatch'
        assert marker in run.stdout, run.stdout
        print(name + ': ' + ('exact contract accepted' if expected == 0 else 'extra premise rejected'))
