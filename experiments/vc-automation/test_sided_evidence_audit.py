#!/usr/bin/env python3
"""PASS+FAIL controls for cached-proof exclusion in actual VC evidence closures."""
import copy
import importlib.util
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('verify', ROOT/'scripts/verify-paper1-automation.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
selected = [c for c in audit.CASES if c['id'] in
            {'sided-embed-rga', 'sided-peritext-core', 'sided-peritext-rich-core'}]
evidence = {r: {'dependencies': [audit.P+'Automation.OrderedRecords.ChainMapping.unique_keys']}
            for c in selected for r in c['vc_roots']}
report = audit.audit_sided_author_interface(evidence)
assert len(report) == 3 and all(r['status'] == 'pass' for r in report.values())
for case in selected:
    for helper in report[case['id']]['eliminated_compatibility_proofs']:
        bad = copy.deepcopy(evidence)
        bad[case['vc_roots'][0]]['dependencies'].append(helper)
        try:
            audit.audit_sided_author_interface(bad)
        except AssertionError as error:
            assert 'cached sided datatype law dependency' in str(error)
        else:
            raise AssertionError('cached law accepted: ' + helper)
    bad = copy.deepcopy(evidence)
    bad[case['vc_roots'][0]]['dependencies'] = []
    try:
        audit.audit_sided_author_interface(bad)
    except AssertionError as error:
        assert 'missing generic issuance derivation' in str(error)
    else:
        raise AssertionError('missing issuance evidence accepted')
print('Sided evidence controls: generic derivation accepted; all cached laws and missing issuance rejected.')

required = [audit.P + 'Automation.' + n for n in (
    'ArchivedOrderedRecords.Equations.kit', 'PrefixCodes.encode_injective',
    'CertifiedIssuance.creator_of_mint', 'append_delta_valid')]
case = next(c for c in audit.CASES if c['id'] == 'fugue-max')
root = case['vc_roots'][0]
evidence = {root: {'dependencies': required}}
report = audit.audit_fugue_author_interface(evidence)
assert report['status'] == 'pass'
for helper in report['eliminated_compatibility_proofs']:
    bad = {root: {'dependencies': required + [helper]}}
    try:
        audit.audit_fugue_author_interface(bad)
    except AssertionError as error:
        assert 'cached archived/code datatype law dependency' in str(error)
    else:
        raise AssertionError('cached Fugue law accepted: ' + helper)
for marker in required:
    bad = {root: {'dependencies': [d for d in required if d != marker]}}
    try:
        audit.audit_fugue_author_interface(bad)
    except AssertionError as error:
        assert 'missing generic archive/code/issuance derivation' in str(error)
    else:
        raise AssertionError('missing Fugue derivation accepted: ' + marker)
print('Fugue evidence controls: generic derivations accepted; cached laws and each absent derivation rejected.')
