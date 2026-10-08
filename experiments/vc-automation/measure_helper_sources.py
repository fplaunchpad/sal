#!/usr/bin/env python3
"""Report transitive, source-written datatype helper theorems for every VC root.

Uses Lean's declaration ranges rather than guessing namespace scopes. Shared
helpers appear under each consumer; do not sum the per-root totals. Datatype
definitions and generated equations/deriving proofs are excluded.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]

def uncomment(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        pair = text[i:i+2]
        if pair == '/-': depth += 1; i += 2
        elif depth and pair == '-/': depth -= 1; i += 2
        elif not depth and pair == '--':
            while i < len(text) and text[i] != '\n': i += 1
        else:
            out.append(text[i] if not depth or text[i] == '\n' else ' ')
            i += 1
    return ''.join(out)

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--audit', type=Path, default=HERE / 'results/common-audit.json')
parser.add_argument('--output', type=Path, default=HERE / 'results/current-helper-effort.json')
args = parser.parse_args()
audit = json.loads(args.audit.read_text())
assert 'declaration_sources' in audit, 'Re-run the verifier with source-location auditing.'
report, hashes = {}, {}
for root, locations in audit['declaration_sources'].items():
    declarations = {}
    for loc in locations:
        module = loc['module']
        if loc['kind'] != 'theorem' or not (
            module.startswith('Sal.MRDTs.Instances.') or module.startswith('Sal.EmbedRGA.')
        ): continue
        path = ROOT / (module.replace('.', '/') + '.lean')
        source = path.read_text()
        start, end = int(loc['start_line']), int(loc['end_line'])
        text = '\n'.join(uncomment(source).splitlines()[start-1:end])
        # Generated tactic/deriving constants often share their parent's range.
        # Charge a source-written theorem once, but never charge an implementation
        # definition simply because Lean generated a proof about it.
        if not re.match(r'\s*(?:@\[[\s\S]*?\]\s*)?(?:private\s+|protected\s+)?theorem\b', text):
            continue
        key = f'{module}:{start}:{end}'
        if key not in declarations:
            declarations[key] = {'file': str(path.relative_to(ROOT)), 'start_line': start,
                'end_line': end, 'lines': sum(bool(line.strip()) for line in text.splitlines()),
                'constants': []}
        declarations[key]['constants'].append(loc['name'])
        hashes[str(path.relative_to(ROOT))] = hashlib.sha256(source.encode()).hexdigest()
    report[root] = {'helper_lines': sum(x['lines'] for x in declarations.values()),
                    'declarations': declarations}
args.output.write_text(json.dumps({'method': __doc__, 'cases': report,
    'source_sha256': hashes}, indent=2) + '\n')
for root, row in report.items(): print(f"{root}: {row['helper_lines']} datatype-helper lines")
