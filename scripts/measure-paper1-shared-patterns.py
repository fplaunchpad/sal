#!/usr/bin/env python3
"""Measure the HEAD-fa964790 shared representation/origin-prefix campaign.

Full concrete declarations, source annotations and generic module code are
charged separately. Prefix roots include the actual production conditions and
execution endpoint, not merely an isolated replacement lemma. Kernel closures
and unchanged contracts complement source footprint measurements.
"""
import hashlib
import importlib.util
import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = 'fa96479039ffee845eefc579915c7206434916be'
OUT = ROOT / 'experiments/vc-automation/results/shared-pattern-measurement.json'


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


B = module('bridges', 'scripts/measure-paper1-bridges.py')
C = B.C
P = 'Sal.MRDTs.Paper1.ConcreteMRDT.GuardedPorts.'
B.CASES = {fam.lower() + '-' + n: [P + fam + '.' + n]
           for fam in ('Tree', 'Sheet')
           for n in ('originLegal', 'conditions', 'executions')}
B.BASE = BASE
bridge_category = B.category
B.category = lambda n, d: ('concrete_proof_annotation'
    if n in {P + 'Tree.originLegal', P + 'Sheet.originLegal'}
    else bridge_category(n, d))


def cached_laws(dependencies):
    return {n for n in dependencies if n.startswith('Sal.MRDTs.Instances.') and
            n.rsplit('.', 1)[-1] in {'mergeLaws', 'deltaLaws', 'commutingPeelLaw', 'join',
                'BC_mergeLaws', 'BC_deltaLaws', 'BC_commutingPeelLaw',
                'RGAM_mergeLaws', 'RGAM_deltaLaws', 'RGAM_commutingPeelLaw'}}


def code_lines(text):
    return sum(bool(line.strip()) for line in C.strip_comments(text).splitlines())


def main():
    before_imports = B.import_hashes()
    baseline = json.loads((ROOT / 'experiments/vc-automation/shared-pattern-baseline/fa964790.json').read_text())
    roots = sorted(n for ns in B.CASES.values() for n in ns)
    kernels = [n for decls in baseline['selected_representation_declarations'].values()
               for n in decls if n.endswith('.kernels')]
    with tempfile.TemporaryDirectory(prefix='sal-shared-pattern-') as tmp:
        f = Path(tmp) / 'Audit.lean'
        f.write_text('import Sal.MRDTs.Paper1.Ledger\n' + B.V.LEAN_AUDIT + '\n' +
                     '\n'.join('audit_production ' + n for n in roots + kernels) + '\n')
        result = subprocess.run(['lake', 'env', 'lean', str(f)], cwd=ROOT,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    assert result.returncode == 0, result.stdout[-5000:]
    # The bridge parser expects exactly its configured roots; measure prefix
    # and representation evidence separately against the same kernel traversal.
    B.CASES.update({'representation-' + n: [n] for n in kernels})
    current = B.measure(result.stdout)
    assert before_imports == B.import_hashes(), 'Source changed during kernel audit'
    current['import_source_sha256'] = before_imports
    representation = {}
    preservation = []
    for filename, old in baseline['selected_representation_declarations'].items():
        raw = (ROOT / filename).read_text()
        new = C.declarations(raw)
        for name, before in old.items():
            if name.endswith('.or_idem'):
                assert name in new and before['header'] == new[name]['header']
                assert not any(n.endswith('.Boolean.or_idem') or 'Boolean.or_idem' in n
                               for r in current['roots'].values() for n in r['dependencies']), 'Old helper still used'
                continue
            assert name in new
            assert before['header'] == new[name]['header'], name
            assert tuple(before['variables']) == tuple(new[name]['variables']), name
            # Parser bodies are normalized strings; line costs come from
            # kernel declaration source ranges, not normalized proof text.
            loc = next(d for m in current['cases']['representation-' + name]['metrics'].values()
                       for d in m['declarations'] if d['name'] == name)
            before_lines = baseline['representation_source_ranges'][name]['lines']
            now_lines = raw.splitlines()[loc['start']-1:loc['end']]
            representation[name] = dict(file=filename, before_lines=before_lines,
                current_lines=code_lines('\n'.join(now_lines)), header_preserved=True,
                raw_definition_arguments=re.findall(r'mrdt_representation \[(.*?)\]', '\n'.join(now_lines)))
            preservation.append(name)
    libraries = {}
    for stem in ('RepresentationAutomation', 'OriginPrefixEvidence'):
        f = 'Sal/MRDTs/Paper1/Automation/' + stem + '.lean'
        raw = (ROOT / f).read_text()
        libraries[f] = dict(nonblank_noncomment_lines=code_lines(raw),
                            source_sha256=hashlib.sha256(raw.encode()).hexdigest())
        if stem == 'RepresentationAutomation':
            assert not re.search(r'Instances\.|TransferSimple|\.kernels\b|mergeLaws|deltaLaws|commutingPeelLaw', C.strip_comments(raw))
    kernel_controls = {}
    for name in kernels:
        deps = set(current['roots'][name]['dependencies'])
        bad = cached_laws(deps)
        assert not bad, (name, sorted(bad))
        forbidden = 'Sal.MRDTs.Instances.CACHED.mergeLaws'
        assert cached_laws(deps | {forbidden}) == {forbidden}
        kernel_controls[name] = dict(status='pass', cached_law_dependencies=[],
                                     contaminated_closure_rejected=True)
    contracts = []
    for filename in [*baseline['selected_representation_declarations'],
                     'Sal/MRDTs/Paper1/IssuedConcretePorts.lean']:
        old = C.declarations(C.git('show', BASE + ':' + filename))
        new = C.declarations((ROOT / filename).read_text())
        for name, before in old.items():
            assert name in new, ('deleted declaration', filename, name)
            after = new[name]
            assert before['header'] == after['header'], ('changed header', name)
            assert before['variables'] == after['variables'], ('changed context', name)
            if before['kind'] not in ('theorem', 'lemma'):
                assert before['body'] == after['body'], ('changed semantic body', name)
        contracts.append(dict(file=filename, declarations=len(old), status='pass'))
    validation_sources = {}
    for stem in ('RepresentationAutomationControls', 'OriginPrefixEvidenceControls'):
        f = 'Sal/MRDTs/Paper1/Automation/' + stem + '.lean'
        if (ROOT / f).is_file():
            raw = (ROOT / f).read_text()
            validation_sources[f] = dict(nonblank_noncomment_lines=code_lines(raw),
                source_sha256=hashlib.sha256(raw.encode()).hexdigest(),
                category='validation_only_not_production_author_savings')
    report = dict(method=__doc__, baseline=baseline, current=current,
                  representation_declarations=representation, shared_libraries=libraries,
                  kernel_controls=kernel_controls, preserved_headers=preservation,
                  head_contract_preservation=contracts, validation_sources=validation_sources)
    OUT.write_text(json.dumps(report, indent=2) + '\n')
    print('Shared pattern full-source/kernel closure report:', OUT.relative_to(ROOT))


if __name__ == '__main__':
    main()
