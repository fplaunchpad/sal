#!/usr/bin/env python3
"""PASS+FAIL source controls for mixed Type-valued ordered/archive kits."""
import importlib.util
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('contracts', ROOT/'scripts/check-paper1-automation-contracts.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
for file, name, fields in (
    ('AutomatedRGA', audit.SIDED_KIT, audit.ORDERED_DATA_FIELDS),
    ('AutomatedFugue', audit.FUGUE_KIT, audit.ARCHIVED_DATA_FIELDS),
    ('AutomatedFugue', audit.ISSUANCE_MODEL, audit.ISSUANCE_DATA_FIELDS),
):
    source = audit.git('show', audit.SIDED_BASELINE + ':Sal/MRDTs/Paper1/Automation/' + file + '.lean')
    kit = audit.declarations(source)[name]
    body = kit['body'].split(' initial_archive :=', 1)[0] if name == audit.ISSUANCE_MODEL else kit['body']
    data = audit.kit_data(body, fields)
    assert data is not None and tuple(data) == fields
    # Accept a proof-only change while keeping every data field fixed.
    assert audit.kit_data(body.replace('init_carrier := rfl', 'init_carrier := by rfl'), fields) == data
    for field in fields:
        original = field + ' := ' + data[field]
        assert audit.kit_data(body.replace(original, field + ' := changedMap', 1), fields) != data, field
        assert audit.kit_data(body.replace(original, '', 1), fields) is None, field
        assert audit.kit_data(body + ' ' + original, fields) is None, field
print('Sided/archive source controls: unchanged data and proof-only edits accepted; every mutation, omission and duplicate rejected.')
# Exercise the new live-list adapter independently of current proof bodies.
body = 'def description where live := State.live archive := State.births archive_written := recordOf insertion := insertion id := Prod.fst Key := List Nat key := fun p=>sKey p.2.2 lt := fun p q=>keyLt (sKey p.2.2) (sKey q.2.2) written := written Γ target := target'
expected = audit.kit_data(audit.declarations(audit.git('show', audit.SIDED_BASELINE + ':Sal/MRDTs/Paper1/Automation/AutomatedFugue.lean'))[audit.FUGUE_KIT]['body'], audit.ARCHIVED_DATA_FIELDS)
assert audit.archived_description_data(body) == expected
for field in ('live', 'archive', 'archive_written', 'insertion', 'id', 'Key', 'key', 'lt', 'written', 'target'):
    import re
    mutated = re.sub(r'\b' + field + r' := .*?(?= \w+ :=|$)', field + ' := changedMap', body, count=1)
    assert audit.archived_description_data(mutated) != expected, field
print('Archived adapter controls: exact list-to-finset/SSorted adapter accepted; all ten description mutations rejected.')
