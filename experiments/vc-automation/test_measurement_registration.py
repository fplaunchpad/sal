#!/usr/bin/env python3
"""PASS+FAIL controls for source annotation symbol qualification."""
import ast
import re
from pathlib import Path
source = Path(__file__).with_name('measure_common_effort.py').read_text()
function = next(n for n in ast.parse(source).body if isinstance(n, ast.FunctionDef) and n.name == 'registration_mentions')
namespace = {'re': re}
exec(compile(ast.Module(body=[function], type_ignores=[]), '<measurement-function>', 'exec'), namespace)
mentions = namespace['registration_mentions']
e = 'Sal.MRDTs.Paper1.Automation.EmbeddedPrimitives.insertion'
s = 'Sal.MRDTs.Paper1.Automation.SidedPrimitives.insertion'
for text in (e, 'EmbeddedPrimitives.insertion', 'insertion'):
    assert mentions(e, text)
assert not mentions(e, s)
assert not mentions(s, e)
assert not mentions(e, 'SidedPrimitives.insertion')
assert not mentions(e, 'other_insertion')
assert not mentions(e, e + 'Suffix')
assert mentions(e, 'attribute [ordered_order] ' + e)
assert not mentions(s, 'attribute [ordered_order] ' + e)
print('Annotation symbol controls: exact/relative/unqualified matches accepted; sibling namespace and substring collisions rejected.')
