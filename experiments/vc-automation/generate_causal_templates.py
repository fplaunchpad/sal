"""Backend-neutral trials for the four actual causal-delta step kernels."""
from pathlib import Path
import re

root = Path(__file__).parent
out = root / 'causal-templates'
out.mkdir(exist_ok=True)
for filename, names in [
    ('InductiveSupplement.lean', {
        'causal_common_kernel', 'causal_commuting_kernel', 'causal_absorber_kernel'}),
    ('CausalExpansion.lean', {'causal_strict_kernel'}),
]:
    source = (root / filename).read_text()
    header = source.split('namespace NeemExpansion.Exact')[0]
    for ns in ['Exact', 'Efficient']:
        section = source.split('namespace NeemExpansion.' + ns + '\n')[1].split('end NeemExpansion.' + ns)[0]
        pre = section.split('theorem ')[0]
        for match in re.finditer(r'theorem (\w+) : (.*?) := by\n(.*?)(?=\ntheorem |\Z)', section, re.S):
            name, goal, proof = match.groups()
            if name not in names:
                continue
            proof, count = re.subn(r'\s*<;>\s*grind \(splits := 20\)\s*$', '', proof)
            assert count == 1, (filename, ns, name)
            trial = header + 'namespace NeemExpansion.' + ns + '\n' + pre
            trial += 'theorem trial : ' + goal + ' := by\n' + proof + '\n  -- SOLVER\n'
            trial += 'end NeemExpansion.' + ns + '\n'
            (out / (ns + '-' + name + '.lean')).write_text(trial)
