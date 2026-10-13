#!/usr/bin/env python3
"""PASS+FAIL controls for the approved rename and narrow split-interface gate."""
import importlib.util
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('contracts', ROOT/'scripts/check-paper1-automation-contracts.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
checked = 0
# Check the immutable checkpoint against its own parent, not against an
# arbitrary recent snapshot: every semantic data body must survive the rename.
for path in audit.git('diff', '--no-renames', '--name-only', audit.RENAME_CHECKPOINT+'^',
                      audit.RENAME_CHECKPOINT, '--', 'Sal/**/*.lean').splitlines():
    if path in audit.RENAMED_PATHS.values():
        continue
    old = audit.declarations(audit.git('show', audit.RENAME_CHECKPOINT+'^:'+path))
    target = audit.RENAMED_PATHS.get(path,path)
    new = audit.declarations(audit.git('show', audit.RENAME_CHECKPOINT+':'+target))
    for name,before in old.items():
        after = new.get(name)
        assert after is not None, (path,name,'missing checkpoint declaration')
        assert before['header'] == after['header'], (path,name,'changed checkpoint header')
        assert before['variables'] == after['variables'], (path,name,'changed checkpoint context')
        if before['kind'] not in ('theorem','lemma'):
            assert before['body'] == after['body'], (path,name,'changed checkpoint semantic data')
        checked += 1
# Renaming does not normalize away weakened guards or altered resolver data.
old = audit.declarations('namespace N\ndef policy : ReplayPolicy D where\n  order a b := if guard a b then RcRes.Fst_then_snd else .Either\nend N\n')['N.policy']
new = audit.declarations('namespace N\ndef policy : EventOrder D where\n  order a b := if guard a b then OrderResult.Fst_then_snd else .Either\nend N\n')['N.policy']
assert old == new
poisoned = audit.declarations('namespace N\ndef policy : EventOrder D where\n  order a b := if True then OrderResult.Fst_then_snd else .Either\nend N\n')['N.policy']
assert poisoned['body'] != old['body']
# Whole scoped-law equivalence is checked by SplitPolicy.Certified and
# SplitPolicy.Invariant.restricted_iff_existing in the production ledger.
for name in audit.SPLIT_INTERFACE_CERTIFICATES:
    before = dict(header='def Correct : Prop', variables=(), kind='def',
                  body='def Correct : Prop := CertifiedReplay.RestrictedLaws scope policy ∧ accepted language')
    after = {**before,'body':before['body'].replace('CertifiedReplay.RestrictedLaws',
                                                  'SplitPolicy.Certified.RestrictedLaws')}
    assert audit.split_interface_certificate(name,before,after)
    for old,new in [('scope','otherScope'),('policy','emptyPolicy'),('language','otherLanguage'),
                    ('accepted language','True')]:
        mutation = {**after,'body':after['body'].replace(old,new)}
        assert not audit.split_interface_certificate(name,before,mutation), (name,old)
    assert not audit.split_interface_certificate(name,{**before,'variables':('variable α',)},after)
assert not audit.split_interface_certificate('N.other',before,after)
print(f'Approved event-order checkpoint: {checked} declaration contracts preserved; guard/data mutations rejected.')
print('Split-interface controls: exact carrier replacement accepted; scope/policy/language/premise/context mutations rejected.')
