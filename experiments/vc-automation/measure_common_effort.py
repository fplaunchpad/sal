#!/usr/bin/env python3
"""Measure the current production five-VC source footprint for 23 named cases.

Counts source-written declarations and registrations, not human effort.
Per-case closures overlap; only deduplicated campaign totals are summable.
Instance declarations, retained datatype theorem helpers and shared generic
framework declarations are reported separately. Existing implementation and
contract definitions are excluded from author-side totals.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
AUTOMATION = 'Sal/MRDTs/Paper1/Automation/'
AUTHOR = {'AutomatedORSet', 'AutomatedEfficientORSet', 'AutomatedMVR',
          'AutomatedRGA', 'AutomatedCore', 'AutomatedRichCore', 'AutomatedFugue',
          'TransferGuardedCommuting', 'TransferAegisSheet', 'TransferLWW',
          'TransferNativeRGA', 'SimpleInputs', 'ORSetInputs', 'MVRInput',
          'CommutingInputs'}
MIXED = {'TransferSimple': ('TransferSimple.Add.', 'TransferSimple.Finite.',
                          'TransferSimple.Delta.', 'TransferSimple.Boolean.')}
DECL = re.compile(r'\s*(?:@\[[\s\S]*?\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*(?:def|abbrev|theorem|lemma|structure|inductive|instance)\b')
THEOREM = re.compile(r'\s*(?:@\[[\s\S]*?\]\s*)?(?:(?:private|protected)\s+)*(?:theorem|lemma)\b')


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


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--audit', type=Path, default=HERE/'results/production-audit.json')
parser.add_argument('--output', type=Path, default=HERE/'results/production-effort.json')
args = parser.parse_args()
audit = json.loads(args.audit.read_text())
for filename, expected in audit['source_sha256'].items():
    path = ROOT / filename
    assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, f'Stale production audit: {path}'
assert len(audit['cases']) == 23, f"Expected 23 production cases, got {len(audit['cases'])}"
locations, roots = audit['declaration_sources'], audit['roots']
vc_names = {root for case in audit['cases'] for root in case['vc_roots']}
evidence = audit['vc_evidence_closures']
sources, hashes, inventory, cases = {}, {}, {}, {}


def read(filename):
    if filename not in sources:
        raw = (ROOT / filename).read_text()
        sources[filename] = uncomment(raw).splitlines()
        hashes[filename] = hashlib.sha256(raw.encode()).hexdigest()
    return sources[filename]


def category(name, filename, text):
    stem = Path(filename).stem
    if filename.startswith(AUTOMATION):
        if stem in AUTHOR or (stem in MIXED and any(p in name for p in MIXED[stem])):
            return 'instance'
        return 'shared_framework'
    if (filename.startswith('Sal/MRDTs/Instances/') or filename.startswith('Sal/EmbedRGA/')) and THEOREM.match(text):
        return 'retained_helper'
    if filename.startswith('Sal/') and THEOREM.match(text):
        return 'existing_framework_helper'
    return None


for case in audit['cases']:
    case_id = case['id']
    dependencies = set()
    for root in case['vc_roots']:
        dependencies.update(evidence[root]['dependencies'])
        for name in evidence[root]['source_verification_declarations']:
            loc = locations.get(name)
            if loc and loc['file'].startswith(AUTOMATION) and Path(loc['file']).stem in AUTHOR:
                dependencies.add(name)
    entries = {}
    for name in sorted(dependencies):
        loc = locations.get(name)
        if not loc: continue
        filename = loc['file']
        lines = read(filename)
        start, end = int(loc['start_line']), int(loc['end_line'])
        text = '\n'.join(lines[start-1:end])
        if not DECL.match(text): continue
        cat = category(name, filename, text)
        if not cat: continue
        key = f'{filename}:{start}:{end}'
        if key not in inventory:
            inventory[key] = {'category': cat, 'file': filename,
                'start_line': start, 'end_line': end,
                'code_lines': [i for i in range(start,end+1) if lines[i-1].strip()],
                'constants': [], 'consumers': [],
                'induction_syntax_lines': [start+i for i,line in enumerate(text.splitlines()) if re.search(r'\binduction\b',line)],
                'explicit_recursor_lines': [start+i for i,line in enumerate(text.splitlines()) if re.search(r'\.(?:rec|recOn|casesOn)\b',line)]}
        entry = inventory[key]
        assert entry['category'] == cat, f'Ambiguous source category: {key}'
        if name not in entry['constants']: entry['constants'].append(name)
        if case_id not in entry['consumers']: entry['consumers'].append(case_id)
        entries[key] = entry
    def count(cat):
        return len({(e['file'],i) for e in entries.values() if e['category']==cat for i in e['code_lines']})
    cases[case_id] = {'vc_roots': case['vc_roots'],
        'instance_lines': count('instance'), 'retained_helper_lines': count('retained_helper'),
        'shared_framework_declaration_lines': count('shared_framework'),
        'existing_framework_helper_lines': count('existing_framework_helper'),
        'declaration_keys': sorted(entries),
        'induction_syntax': {k:e['induction_syntax_lines'] for k,e in entries.items() if e['category']=='instance' and e['induction_syntax_lines']},
        'explicit_recursors': {k:e['explicit_recursor_lines'] for k,e in entries.items() if e['category']=='instance' and e['explicit_recursor_lines']}}

# Registration commands do not survive in proof terms. Track Lean namespace
# and section nesting, then associate registrations with selected declarations.
commands = []
# Charge only production automation invocations inside existing certificates,
# rather than their unchanged sequential/history fields or whole declarations.
invocations = {}
for case in audit['cases']:
    for root in case['vc_roots']:
        for name in evidence[root]['source_verification_declarations']:
            loc = locations.get(name)
            if not loc: continue
            filename = loc['file']
            lines = read(filename)
            for i in range(int(loc['start_line']), int(loc['end_line'])+1):
                if 'mrdt_verify' not in lines[i-1]: continue
                if any(e['category']=='instance' and e['file']==filename and i in e['code_lines'] for e in inventory.values()):
                    continue
                key = (filename, i)
                if key not in invocations:
                    invocations[key] = {'file':filename, 'line':i, 'text':lines[i-1].strip(),
                        'kind':'production_vc_invocation', 'consumers':[]}
                if case['id'] not in invocations[key]['consumers']:
                    invocations[key]['consumers'].append(case['id'])
commands.extend(invocations.values())
for filename in sorted({e['file'] for e in inventory.values() if e['category']=='instance'}):
    frames = []
    scope = ''
    active_attribute = None
    for i,line in enumerate(read(filename),1):
        ns = re.match(r'\s*namespace\s+(\S+)',line)
        section = re.match(r'\s*(?:noncomputable\s+)?section(?:\s|$)',line)
        if ns:
            frames.append(scope)
            scope = scope+'.'+ns.group(1) if scope else ns.group(1)
        elif section: frames.append(scope)
        elif re.match(r'\s*end(?:\s|$)',line) and frames: scope = frames.pop()
        registration = re.match(r'\s*register_mrdt_input\s+(\S+)',line)
        attr = re.match(r'\s*attribute\b',line)
        if attr: active_attribute = i
        elif active_attribute and line.strip() and (not line.startswith(' ') or re.match(r'\s*(?:def|abbrev|theorem|lemma|namespace|end|open|set_option|register_mrdt_input)\b', line)): active_attribute = None
        if not registration and not active_attribute: continue
        if not line.strip(): continue
        target = scope+'.'+registration.group(1) if registration else None
        consumers = sorted({r for e in inventory.values() if e['category']=='instance' and e['file']==filename and any((n==target if target else n.startswith(scope+'.')) for n in e['constants']) for r in e['consumers']})
        if consumers:
            commands.append({'file':filename, 'line':i, 'text':line.strip(), 'scope':scope, 'kind':'instance_registration_or_annotation', 'consumers':consumers})
for case_id,row in cases.items():
    row['registration_annotation_lines'] = sum(case_id in c['consumers'] for c in commands)
    row['author_total_lines'] = row['instance_lines']+row['registration_annotation_lines']
    row['author_and_retained_helper_lines'] = row['author_total_lines']+row['retained_helper_lines']


def unique(cat):
    return len({(e['file'],i) for e in inventory.values() if e['category']==cat for i in e['code_lines']})


framework_files = sorted({e['file'] for e in inventory.values() if e['category']=='shared_framework'})
framework_code = sum(sum(bool(line.strip()) for line in read(filename)) for filename in framework_files)
# Whole reusable library size, independent of the selected proof closures.
# Mixed TransferSimple files contain finite instance declarations too; remove
# the charged instance lines from this additional module-level measurement.
library_files = sorted(str(p.relative_to(ROOT)) for p in (ROOT / AUTOMATION).glob('*.lean')
    if p.stem not in AUTHOR and p.stem != 'Controls')
instance_line_pairs = {(e['file'], i) for e in inventory.values() if e['category']=='instance' for i in e['code_lines']}
library_code = sum(sum(bool(line.strip()) and (filename, i) not in instance_line_pairs
    for i, line in enumerate(read(filename), 1)) for filename in library_files)
registry = []
for stem in ['OrderedRecordAutomation','PolicyExpansionAutomation','CommonAlgebraAutomation']:
    filename = AUTOMATION+stem+'.lean'
    active = False
    for i,line in enumerate(read(filename),1):
        if re.match(r'\s*attribute\b',line): active = True
        elif active and line.strip() and not line.startswith(' '): active = False
        if active and line.strip(): registry.append({'file':filename, 'line':i, 'text':line.strip()})
report = {'method':__doc__, 'limitations':[
    'Source lines measure proof/annotation footprint, not human effort or proof difficulty.',
    'Per-case totals overlap; campaign totals deduplicate file/line pairs.',
    'Author declarations are transitive production instance inputs and finite proofs from actual submitted CommonVerification.verify applications. Existing certificate wrappers contribute only mrdt_verify invocation lines; new author-side VC theorem declarations are counted in full.',
    'Existing implementation and contract definitions are excluded. Retained datatype theorem helpers and existing generic foundational theorem helpers are reported separately; structure projections are not charged as authored proofs.',
    'Shared generic declarations are a separate reusable-library cost; whole participating module code additionally includes macros, imports and annotations.',
    'Induction/recursor syntax scans do not establish absence of hidden history reasoning.'],
    'cases':cases, 'unique_campaign':{'instance_lines':unique('instance'), 'retained_helper_lines':unique('retained_helper'),
        'registration_annotation_lines':len(commands)},
    'shared_framework':{'dependency_declaration_lines':unique('shared_framework'), 'existing_framework_helper_lines':unique('existing_framework_helper'), 'participating_module_code_lines':framework_code,
        'participating_files':framework_files, 'library_code_lines_excluding_charged_instance_lines':library_code,
        'library_files':library_files, 'registry_annotation_lines':len(registry), 'registry_annotations':registry},
    'declarations':inventory, 'commands':commands, 'source_sha256':hashes,
    'audit_sha256':hashlib.sha256(args.audit.read_bytes()).hexdigest()}
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(report,indent=2)+'\n')
for case_id,row in cases.items():
    print(f"{case_id}: {row['instance_lines']} instance + {row['retained_helper_lines']} retained helper + {row['registration_annotation_lines']} annotation lines")
print('Unique campaign:',report['unique_campaign'])
print('Shared framework:',report['shared_framework']['dependency_declaration_lines'],'dependency declaration lines;',framework_code,'participating module code lines')
