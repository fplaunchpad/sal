#!/usr/bin/env python3
"""Reproducible source-footprint census; not a proof-effort or completeness metric."""
import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
INST = ROOT / 'Sal/MRDTs/Instances'


def imports(path):
    return re.findall(r'^import\s+(\S+)', path.read_text(), re.M)


def closure(module):
    seen = set()
    pending = [module]
    while pending:
        name = pending.pop()
        path = ROOT / (name.replace('.', '/') + '.lean')
        if name in seen or not path.exists():
            continue
        seen.add(name)
        pending.extend(imports(path))
    return seen


def count(path):
    source = path.read_text()
    lines = source.splitlines()
    return {'path': str(path.relative_to(ROOT)), 'lines': len(lines),
            'nonblank_lines': sum(bool(line.strip()) for line in lines),
            'theorem_declarations': len(re.findall(
                r'^\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s', source, re.M))}


def group(paths):
    files = [count(p) for p in sorted(paths)]
    return {'totals': {key: sum(f[key] for f in files)
                       for key in ('lines', 'nonblank_lines', 'theorem_declarations')},
            'file_count': len(files), 'files': files}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    ref = closure('Sal.MRDTs.Instances.NotionCoreProtocol')
    direct = list(INST.glob('NotionCoreStructural*.lean'))
    intermediate = list(INST.glob('NotionCoreIncremental*.lean'))
    final_closure = closure('Sal.MRDTs.Instances.NotionCoreStructuralMRDT')
    direct_dependencies = set()
    for path in direct:
        direct_dependencies |= closure('.'.join(path.relative_to(ROOT).with_suffix('').parts))
    direct_names = {'.'.join(p.relative_to(ROOT).with_suffix('').parts) for p in direct}
    intermediate_names = {'.'.join(p.relative_to(ROOT).with_suffix('').parts) for p in intermediate}
    def paths(names):
        return [ROOT / (name.replace('.', '/') + '.lean') for name in names]
    notion = lambda name: name.startswith('Sal.MRDTs.Instances.Notion')
    report = {
        'scope': 'Current source snapshot, including unfinished modules. No build or completion claim.',
        'limits': ['Physical and nonblank lines include definitions, comments and controls.',
                   'Declaration counts use line-oriented syntax, not elaborated theorem objects.',
                   'Import closure measures available dependencies, not which lemmas are used.',
                   'Source size does not measure author time, difficulty, or proof reduction.',
                   'Reference provides shared semantics and honest protocol; direct modules reuse it.'],
        'reference_protocol_notion_closure': group(paths(n for n in ref if notion(n))),
        'new_direct_modules': group(direct),
        'new_direct_required_by_final_endpoint': group(paths(direct_names & final_closure)),
        'new_direct_optional_investigations': group(paths(direct_names - final_closure)),
        'intermediate_cache_and_counterexample_modules': group(intermediate),
        'new_support_required_by_final_endpoint': group(paths(intermediate_names & final_closure)),
        'direct_existing_notion_dependencies': group(paths(n for n in direct_dependencies
                                                         if notion(n) and n not in direct_names and n not in intermediate_names)),
    }
    output = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(output)
    else:
        print(output, end='')


if __name__ == '__main__':
    main()
