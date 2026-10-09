#!/usr/bin/env python3
"""Audit source contracts against fixed production baselines; not kernel type equality.

Compares every existing declaration in modified production Lean files, retaining
namespace and variable contexts. Comments/whitespace and theorem proof bodies
are ignored. Only named proof certificates may change bodies. The OR-set derivation
baseline also checks the four mask data maps moved into a description. Newly
added declarations are checked by the build/axiom audit, not this scanner.
"""
import argparse
import json
import re
import subprocess
from pathlib import Path

BASELINE = 'e89cd6d'
ROOT = Path(__file__).resolve().parents[1]
CERTIFICATES = {
    'Sal.MRDTs.Paper1.ConcreteMRDT.SimplePorts.' + n + '.conditions'
    for n in ('Add', 'Finite', 'Boolean', 'Delta')
} | {
    'Sal.MRDTs.Paper1.ConcreteMRDT.GuardedPorts.' + n + '.conditions'
    for n in ('Bounded', 'Tree', 'Sheet')
} | {'Sal.MRDTs.Paper1.RGA.ConcretePort.conditions',
     'Sal.MRDTs.Paper1.LWW.GuardedPort.certificate'} | {
    'Sal.MRDTs.Paper1.ConcreteMRDT.Guarded.ScopedPorts.' + n + 'Certificate'
    for n in ('bounded', 'tree', 'sheet', 'rga')
}
MOVED = {
    'Sal.MRDTs.Paper1.CertifiedQueueMVR.MVR.RawVC.' + n:
    'Sal/MRDTs/Paper1/CertifiedMVRVCContract.lean'
    for n in ('policy', 'scheme', 'representation')
} | {
    'Sal.MRDTs.Paper1.CertifiedRGARichVC.' + n:
    'Sal/MRDTs/Paper1/CertifiedRGARichContract.lean'
    for n in ('policy', 'scheme', 'representation')
}
# These terms inhabit Prop; their exact headers and variable contexts still match.
ORSET_PROOFS = {
    'Sal.MRDTs.Paper1.Automation.AutomatedORSet.kit',
    'Sal.MRDTs.Paper1.Automation.AutomatedEfficientORSet.kit',
    'Sal.MRDTs.Paper1.Automation.CommonInstances.OrdinaryORSet.input',
    'Sal.MRDTs.Paper1.Automation.CommonInstances.EfficientORSet.input',
}
MASK_KIT = 'Sal.MRDTs.Paper1.Automation.AutomatedEfficientORSet.maskKit'
MASK_DESCRIPTION = 'Sal.MRDTs.Paper1.Automation.AutomatedEfficientORSet.maskDescription'
DECL = re.compile(r'^ ?(?:(?:private|protected|noncomputable|unsafe|opaque)\s+)*'
                  r'(theorem|lemma|def|abbrev|structure|inductive)\s+([^\s(:]+)')
COMMAND = re.compile(r'^(?:namespace|section|noncomputable section|end|open|variable|'
                     r'set_option|#\w+|attribute|import|instance|example|macro|elab)\b')


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)


def strip_comments(text):
    # Nested Lean block comments; retain newlines for command boundaries.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1
            i += 2
        elif depth:
            if text[i] == '\n':
                out.append('\n')
            i += 1
        elif text[i:i+2] == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def norm(text):
    return re.sub(r'\s+', ' ', text).strip()


def declarations(text):
    lines = strip_comments(text).splitlines()
    result, scopes, variables = {}, [], []
    i = 0
    while i < len(lines):
        line = lines[i]
        match = DECL.match(line)
        if match:
            j = i + 1
            while j < len(lines) and not DECL.match(lines[j]) and not COMMAND.match(lines[j]):
                j += 1
            body = '\n'.join(lines[i:j])
            namespace = '.'.join(name for kind, name, _ in scopes if kind == 'namespace')
            name = (namespace + '.' if namespace else '') + match[2]
            if name in result:
                raise ValueError('duplicate declaration: ' + name)
            result[name] = dict(kind=match[1], header=norm(re.split(r':=|\bwhere\b', body, maxsplit=1)[0]),
                                body=norm(body), variables=tuple(variables))
            i = j
            continue
        if line.startswith('namespace '):
            scopes.append(('namespace', line.split()[1], len(variables)))
        elif re.match(r'^(?:noncomputable )?section\b', line):
            scopes.append(('section', '', len(variables)))
        elif re.match(r'^end\b', line):
            if scopes:
                _, _, count = scopes.pop()
                variables = variables[:count]
        elif line.startswith('variable '):
            j = i + 1
            while j < len(lines) and lines[j][:1].isspace():
                j += 1
            variables.append(norm('\n'.join(lines[i:j])))
            i = j
            continue
        i += 1
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', choices=(BASELINE, '7880732'), default=BASELINE,
                        help='Fixed production migration or OR-set derivation baseline.')
    parser.add_argument('--output', type=Path,
                        default=ROOT / 'experiments/vc-automation/results/production-contracts.json')
    args = parser.parse_args()
    baseline = args.baseline
    changed = git('diff', '--no-renames', '--name-only', baseline, '--', 'Sal/**/*.lean').splitlines()
    baseline_files = set(git('ls-tree', '-r', '--name-only', baseline, '--', 'Sal').splitlines())
    files = [path for path in changed if path in baseline_files]
    report = dict(baseline=baseline, evidence='source-header/body preservation; not kernel type equality',
                  files=[], failures=[],
                  added_files=[path for path in changed if path not in baseline_files])
    for path in files:
        if not (ROOT / path).is_file():
            report['failures'].append(dict(path=path, reason='deleted baseline production file'))
            continue
        old = declarations(git('show', baseline + ':' + path))
        current = declarations((ROOT / path).read_text())
        record = dict(path=path, checked=len(old), moved=[], proof_changes=[], certificate_changes=[],
                      proof_definition_changes=[], preserved_data_descriptions=[])
        for name, before in old.items():
            after = current.get(name)
            if after is None and name in MOVED:
                target = MOVED[name]
                after = declarations((ROOT / target).read_text()).get(name)
                record['moved'].append(dict(declaration=name, target=target))
            reason = None
            if after is None:
                reason = 'missing declaration'
            elif before['header'] != after['header']:
                reason = 'changed declaration header'
            elif before['variables'] != after['variables']:
                reason = 'changed variable context'
            elif before['body'] != after['body']:
                if before['kind'] in ('theorem', 'lemma'):
                    record['proof_changes'].append(name)
                elif baseline == '7880732' and name in ORSET_PROOFS:
                    record['proof_definition_changes'].append(name)
                elif baseline == '7880732' and name == MASK_KIT:
                    description = current.get(MASK_DESCRIPTION)
                    old_data = before['body'].split(' where ', 1)[-1].split(' injective :=', 1)[0]
                    new_data = description['body'].split(' where ', 1)[-1] if description else None
                    if new_data != old_data:
                        reason = 'changed mask carrier/step/birth/kill data'
                    else:
                        record['preserved_data_descriptions'].append(name)
                elif name in CERTIFICATES:
                    record['certificate_changes'].append(name)
                else:
                    reason = 'changed semantic definition body'
            if reason:
                report['failures'].append(dict(path=path, declaration=name, reason=reason))
        report['files'].append(record)
    report['checked_declarations'] = sum(f['checked'] for f in report['files'])
    report['status'] = 'pass' if not report['failures'] else 'fail'
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('baseline', 'evidence', 'checked_declarations', 'status', 'failures')}))
    return bool(report['failures'])


if __name__ == '__main__':
    raise SystemExit(main())
