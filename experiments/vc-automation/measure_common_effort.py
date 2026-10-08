#!/usr/bin/env python3
"""Measure source footprint of the current 23 common verification roots.

Counts complete source-written declarations (types, annotations and proofs),
not human time. Per-root closures overlap: only the unique campaign total is
summable. Generic framework proofs and existing implementation definitions are
excluded. Retained datatype theorem helpers are reported separately.
"""
from pathlib import Path
import argparse, hashlib, json, re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]

def uncomment(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        pair = text[i:i+2]
        if pair == '/-': depth += 1; out.extend('  '); i += 2
        elif depth and pair == '-/': depth -= 1; out.extend('  '); i += 2
        elif not depth and pair == '--':
            while i < len(text) and text[i] != '\n': out.append(' '); i += 1
        else:
            out.append(text[i] if not depth or text[i] == '\n' else ' '); i += 1
    return ''.join(out)

AUTHOR = {'CommonInstances', 'AutomatedORSet', 'AutomatedEfficientORSet',
          'AutomatedMVR', 'AutomatedRGA', 'AutomatedCore', 'AutomatedFugue',
          'TransferGuardedCommuting', 'TransferAegisSheet'}
MIXED = {'TransferSimple': ('NeemExpansion.TransferSimple.Add.',
    'NeemExpansion.TransferSimple.Finite.', 'NeemExpansion.TransferSimple.Delta.',
    'NeemExpansion.TransferSimple.Boolean.'),
    'TransferProductExpansion': ('NeemExpansion.TransferProduct.NativeRGA.',)}
DECL = re.compile(r'\s*(?:@\[[\s\S]*?\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*(?:def|abbrev|theorem|lemma|structure|inductive|instance)\b')
THEOREM = re.compile(r'\s*(?:@\[[\s\S]*?\]\s*)?(?:(?:private|protected)\s+)*theorem\b')

def category(loc):
    m, n = loc['module'], loc['name']
    if m in AUTHOR or (m in MIXED and any(p in n for p in MIXED[m])):
        return 'instance'
    if loc['kind'] == 'theorem' and (m.startswith('Sal.MRDTs.Instances.') or m.startswith('Sal.EmbedRGA.')):
        return 'retained_helper'
    return None

def source_path(module):
    return (ROOT / (module.replace('.', '/') + '.lean') if module.startswith('Sal.')
            else HERE / (module + '.lean'))

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--audit', type=Path, default=HERE/'results/common-audit.json')
parser.add_argument('--output', type=Path, default=HERE/'results/common-effort.json')
args = parser.parse_args()
audit = json.loads(args.audit.read_text())
for filename, expected in audit['source_sha256'].items():
    path = HERE / filename
    assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, f'Stale common audit: {path}'
locations = audit['declaration_sources']
assert len(locations) == 23, f'Expected all 23 common roots, got {len(locations)}'
sources, hashes, inventory, cases = {}, {}, {}, {}
def read(module):
    if module not in sources:
        path = source_path(module); raw = path.read_text()
        sources[module] = uncomment(raw).splitlines()
        hashes[str(path.relative_to(ROOT))] = hashlib.sha256(raw.encode()).hexdigest()
    return sources[module]

for root, locs in locations.items():
    entries = {}
    for loc in locs:
        cat = category(loc)
        if not cat: continue
        lines = read(loc['module']); start, end = int(loc['start_line']), int(loc['end_line'])
        text = '\n'.join(lines[start-1:end])
        if not (THEOREM if cat == 'retained_helper' else DECL).match(text): continue
        key = f"{loc['module']}:{start}:{end}"
        if key not in inventory:
            inventory[key] = {'category': cat, 'file': str(source_path(loc['module']).relative_to(ROOT)),
                'start_line': start, 'end_line': end,
                'code_lines': [i for i in range(start,end+1) if lines[i-1].strip()],
                'constants': [], 'consumers': [],
                'induction_syntax_lines': [start+i for i,line in enumerate(text.splitlines()) if re.search(r'\binduction\b',line)],
                'explicit_recursor_lines': [start+i for i,line in enumerate(text.splitlines()) if re.search(r'\.(?:rec|recOn|casesOn)\b',line)]}
        entry = inventory[key]
        if loc['name'] not in entry['constants']: entry['constants'].append(loc['name'])
        if root not in entry['consumers']: entry['consumers'].append(root)
        entries[key] = entry
    def count(cat):
        return len({(e['file'],i) for e in entries.values() if e['category']==cat for i in e['code_lines']})
    cases[root] = {'instance_lines': count('instance'), 'retained_helper_lines': count('retained_helper'),
        'declaration_keys': sorted(entries),
        'induction_syntax': {k:e['induction_syntax_lines'] for k,e in entries.items() if e['category']=='instance' and e['induction_syntax_lines']},
        'explicit_recursors': {k:e['explicit_recursor_lines'] for k,e in entries.items() if e['category']=='instance' and e['explicit_recursor_lines']}}

# Commands do not survive in proof terms. Record their source independently;
# scoped registration is associated with the selected input's namespace.
commands = []
for module in sorted({k.split(':')[0] for k,e in inventory.items() if e['category']=='instance'}):
    scopes=[]
    for i,line in enumerate(read(module),1):
        ns=re.match(r'\s*namespace\s+(\S+)',line)
        if ns: scopes.append(ns.group(1))
        if re.match(r'\s*end(?:\s|$)',line) and scopes: scopes.pop()
        if not re.match(r'\s*(?:register_mrdt_input|attribute)\b',line): continue
        scope='.'.join(scopes)
        registration=re.match(r'\s*register_mrdt_input\s+(\S+)',line)
        target=scope+'.'+registration.group(1) if registration else None
        consumers=sorted({r for e in inventory.values() if e['category']=='instance' and e['file']==str(source_path(module).relative_to(ROOT)) and any((n==target if target else n.startswith(scope+'.')) for n in e['constants']) for r in e['consumers']})
        commands.append({'file':str(source_path(module).relative_to(ROOT)), 'line':i, 'text':line.strip(), 'scope':scope, 'consumers':consumers})
for root,row in cases.items():
    row['registration_annotation_lines']=sum(root in c['consumers'] for c in commands)
    row['total_lines']=row['instance_lines']+row['retained_helper_lines']+row['registration_annotation_lines']
def unique(cat):
    return len({(e['file'],i) for e in inventory.values() if e['category']==cat for i in e['code_lines']})
registry=[]
for module in ['OrderedRecordAutomation','PolicyExpansionAutomation','CommonAlgebraAutomation']:
    lines=read(module)
    active=False
    for i,line in enumerate(lines,1):
        if re.match(r'\s*attribute\b',line): active=True
        elif active and line.strip() and not line.startswith(' '): active=False
        if active and line.strip(): registry.append({'file':str(source_path(module).relative_to(ROOT)), 'line':i, 'text':line.strip()})
report={'shared_registry_annotation_lines':len(registry), 'shared_registry_annotations':registry, 'method':__doc__, 'limitations':[
    'Source lines measure proof/annotation footprint, not human effort or proof difficulty.',
    'Per-root totals overlap and must not be summed; campaign totals deduplicate file/line pairs.',
    'Generic framework proofs are intentionally excluded; existing source-written datatype helper theorems are included separately.',
    'Induction/recursor scans are syntax diagnostics, not a proof that a helper hides no history reasoning.',
    'Registry framework macros are excluded; instance-side attribute/registration commands are recorded separately.'],
    'cases':cases, 'unique_campaign':{'instance_lines':unique('instance'), 'retained_helper_lines':unique('retained_helper'),
        'registration_annotation_lines':len(commands)}, 'declarations':inventory, 'commands':commands,
    'source_sha256':hashes, 'audit_sha256':hashlib.sha256(args.audit.read_bytes()).hexdigest()}
args.output.write_text(json.dumps(report,indent=2)+'\n')
for root,row in cases.items(): print(f"{root}: {row['instance_lines']} instance + {row['retained_helper_lines']} retained helper + {row['registration_annotation_lines']} annotation lines")
print('Unique campaign:',report['unique_campaign'])
