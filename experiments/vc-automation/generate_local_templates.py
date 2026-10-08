"""Generate identical-preparation backend trials for actual nested-local kernels."""
from pathlib import Path
import re
root = Path(__file__).parent
source = (root / 'LocalExpansion.lean').read_text()
header = source.split('namespace NeemExpansion.Exact')[0]
out = root / 'local-templates'
out.mkdir(exist_ok=True)
for ns in ['Exact', 'Efficient']:
    section = source.split('namespace NeemExpansion.' + ns + '\n')[1].split('end NeemExpansion.' + ns)[0]
    pre = section.split('theorem ')[0]
    for match in re.finditer(r'theorem (\w+) : (.*?) := by\n(.*?)(?=\ntheorem |\Z)', section, re.S):
        name, goal, proof = match.groups()
        proof = proof.rstrip().replace(' <;> grind (splits := 20)', '')
        proof += '\n  -- SOLVER\n'
        trial = header + 'namespace NeemExpansion.' + ns + '\n' + pre
        trial += 'theorem trial : ' + goal + ' := by\n' + proof
        trial += 'end NeemExpansion.' + ns + '\n'
        (out / (ns + '-' + name + '.lean')).write_text(trial)
