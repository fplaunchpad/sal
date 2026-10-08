#!/usr/bin/env python3
"""Measure author-facing declaration code, including annotations and helper proofs.
Run after verify_expansion.py --automated. Counts are physical nonblank code
lines, not a claim about necessary human effort. Generic library proofs are
separate; existing RDT-specific raw helper proofs are charged explicitly.
"""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def uncomment(source):
    out, depth, i = [], 0, 0
    while i < len(source):
        pair = source[i:i + 2]
        if pair == '/-':
            depth += 1
            i += 2
        elif depth and pair == '-/':
            depth -= 1
            i += 2
        elif not depth and pair == '--':
            while i < len(source) and source[i] != '\n':
                i += 1
        else:
            out.append(source[i] if not depth or source[i] == '\n' else ' ')
            i += 1
    return ''.join(out)


def count(code):
    return sum(bool(line.strip()) and not re.match(
        r'\s*(import |open |variable |namespace |end\b|#|set_option |noncomputable section)', line)
        for line in code.splitlines())


def region(file, start, stop):
    code = uncomment((HERE / file).read_text())
    code = code[code.index(start):]
    return count(code[:code.index(stop)])


def namespace_counts(file):
    counts, stack = {}, []
    for line in uncomment((HERE / file).read_text()).splitlines():
        text = line.strip()
        if text.startswith('namespace '):
            stack.append(text.split()[1])
        elif text.startswith('end '):
            stack.pop()
        else:
            name = '.'.join(stack)
            counts[name] = counts.get(name, 0) + count(line)
    return counts


def helper_declarations(file, dependencies):
    lines = uncomment((ROOT / file).read_text()).splitlines()
    namespace = next(line.split()[1] for line in lines if line.startswith('namespace '))
    result = {}
    boundary = r'^(?:private |noncomputable )?(?:theorem|def|abbrev|structure|instance|inductive|namespace|end|variable|open|attribute|notation|infix|#)\b'
    for i, line in enumerate(lines):
        match = re.match(r'^(?:private )?theorem\s+(\S+)', line)
        if not match:
            continue
        name = namespace + '.' + match[1]
        if name not in dependencies:
            continue
        j = i + 1
        while j < len(lines) and not re.match(boundary, lines[j]):
            j += 1
        result[name] = {'file': file, 'line': i + 1,
                        'lines': count('\n'.join(lines[i:j]))}
    return result


audit = json.loads((HERE / 'results/automated-audit.json').read_text())
deps = set(audit['dependencies'])
rga = namespace_counts('AutomatedRGA.lean')
helpers = {
    family: helper_declarations('Sal/MRDTs/Instances/' + module + '.lean', deps)
    for family, module in [('Embedded RGA', 'EmbedRGA'), ('Sided RGA', 'SidedEmbedRGA')]
}
rows = {
    'MVR': {
        'author_lines': region('AutomatedMVR.lean', 'def model', '#print'),
        'retained_datatype_helpers': {},
    },
    'Embedded RGA': {
        'author_lines': rga['NeemExpansion.AutomatedRGA.Embedded'],
        'retained_datatype_helpers': helpers['Embedded RGA'],
    },
    'Sided RGA': {
        'author_lines': rga['NeemExpansion.AutomatedRGA.Sided'],
        'retained_datatype_helpers': helpers['Sided RGA'],
    },
}
for row in rows.values():
    row['retained_helper_lines'] = sum(x['lines'] for x in row['retained_datatype_helpers'].values())
    row['author_plus_retained_helpers'] = row['author_lines'] + row['retained_helper_lines']
files = set(audit['source_sha256'])
report = {
    'method': 'Nonblank noncomment declaration lines, including theorem statements, proof bodies, definitions/annotations and helper lemmas; imports/namespace/open/variable/#print scaffolding excluded. Retained helper proofs are actual source-written theorems in the RDT modules reached by the audit; generated equations and general coordinate/collection library proofs are excluded.',
    'cases': rows,
    'raw_helper_registrations': {
        'Embedded RGA': ['mem_eInsert', 'mem_eMerge2', 'eInsert_sorted', 'eMerge_sorted', 'esorted_ext'],
        'Sided RGA': ['mem_sInsert', 'mem_sMerge2', 'sInsert_sorted', 'sMerge_sorted', 'ssorted_ext'],
    },
    'shared_helper_and_two_transfer_declarations': rga['NeemExpansion.AutomatedRGA'],
    'framework_lines': {f: count(uncomment((HERE / f).read_text())) for f in
                        ['GenericCertifiedRecords.lean', 'GenericOrderedRecords.lean', 'OrderedRecordRules.lean', 'OrderedRecordAutomation.lean']},
    'source_sha256': {f: hashlib.sha256((HERE / f).read_bytes()).hexdigest() for f in sorted(files)},
    'helper_source_sha256': {str(Path(x['file'])): hashlib.sha256((ROOT / x['file']).read_bytes()).hexdigest()
                             for h in helpers.values() for x in h.values()},
}
(HERE / 'results/template-effort.json').write_text(json.dumps(report, indent=2) + '\n')
for name, row in rows.items():
    print(f"{name}: {row['author_lines']} author lines; {row['retained_helper_lines']} retained raw-helper lines")
