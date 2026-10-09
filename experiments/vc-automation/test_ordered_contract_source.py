#!/usr/bin/env python3
"""Adversarial controls for eight-map ordered kit source preservation."""
import importlib.util
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('contracts', ROOT/'scripts/check-paper1-automation-contracts.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
source = audit.git('show', 'ffec6e9:Sal/MRDTs/Paper1/Automation/AutomatedRGA.lean')
kit = audit.declarations(source)[audit.ORDERED_KIT]
data = audit.ordered_data(kit['body'])
assert data is not None and tuple(data) == audit.ORDERED_DATA_FIELDS
for field in audit.ORDERED_DATA_FIELDS:
    original = field + ' := ' + data[field]
    mutated = kit['body'].replace(original, field + ' := changedMap', 1)
    assert audit.ordered_data(mutated) != data, field
    missing = kit['body'].replace(original, '', 1)
    assert audit.ordered_data(missing) is None, field
assert audit.ordered_data(kit['body'].replace('init_carrier := rfl', 'init_carrier := by rfl')) == data
print('Ordered source controls: eight semantic-map mutations and omissions rejected; proof-only change accepted.')
