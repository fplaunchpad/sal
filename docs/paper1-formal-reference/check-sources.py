#!/usr/bin/env python3
"""Regenerate the appendix and emit a Lean declaration check to the given path."""
import argparse
import collections
import csv
import re
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('check_file', type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parent
rows = []
groups = collections.OrderedDict()
for section in ('execution', 'semantics', 'merge', 'bridge'):
    with (root / f'{section}-sources.tsv').open() as stream:
        for row in csv.DictReader(stream, delimiter='\t'):
            groups.setdefault(row['label'], []).append(row)
            rows.append(row)
order = []
for section in ('execution', 'semantics', 'merge', 'bridge'):
    order.extend(re.findall(r'\\label\{([^}]+)\}', (root / f'{section}.tex').read_text()))
groups = collections.OrderedDict(sorted(groups.items(), key=lambda pair: order.index(pair[0])))
lines = [r'\section{Mechanization Traceability}', r'\label{app:traceability}',
         'The main text can be read without Lean. This appendix maps each numbered',
         'statement to its checked declarations. Some statements group declarations',
         'or specialize a generic interface to concrete equality. Existing source',
         'links use the proof baseline; the new direct sequential lifting lemma',
         'links to the accompanying file on \\texttt{paper1}. The declaration-check',
         'script supplied with this reference checks that every name resolves.',
         'The theorem ledger separately audits final roots for permitted axioms.', '']
for label, entries in groups.items():
    lines.append(r'\medskip\noindent\textbf{Reference~\ref{' + label + r'}.}\par\nobreak')
    modules = collections.OrderedDict()
    for row in entries:
        modules.setdefault(row['module'], []).append(row['declaration'])
    for module, declarations in modules.items():
        revision = 'paper1' if module.endswith('.PaperPresentation') else '07fe525'
        url = f'https://github.com/fplaunchpad/sal/blob/{revision}/' + module.replace('.', '/') + '.lean'
        lines.append(r'\noindent\href{' + url + '}{' + module.split('.')[-1] + r'.lean}:\par')
        lines.extend(r'{\small\nolinkurl{' + declaration + r'}}\par' for declaration in declarations)
    lines.append('')
(root / 'traceability.tex').write_text('\n'.join(lines).rstrip() + '\n')
modules = sorted({row['module'] for row in rows})
declarations = sorted({row['declaration'] for row in rows})
args.check_file.write_text('\n'.join('import ' + m for m in modules) + '\n' +
                          '\n'.join('#check ' + d for d in declarations) + '\n')
print(f'{len(groups)} reference anchors; {len(declarations)} declarations')
