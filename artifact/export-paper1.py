#!/usr/bin/env python3
"""Export only the paper's measured Lean dependency closure and support files."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
TEMPLATE = ROOT / 'artifact' / 'paper1'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True, help='new directory; existing paths are refused')
    parser.add_argument('--archive', action='store_true', help='also create a .tar.gz beside the directory')
    args = parser.parse_args()
    out = args.out.resolve()
    if out.exists():
        parser.error('output directory already exists')
    counts = json.loads((ROOT / 'experiments/paper-implementation/current-counts.json').read_text())
    meta = json.loads((ROOT / 'experiments/paper-implementation/metatheory-counts.json').read_text())
    for filename, digest in counts['source_sha256'].items():
        if sha(ROOT / filename) != digest:
            raise SystemExit('Measured source changed; refresh the paper measurement first: ' + filename)
    seeds = set(counts['source_sha256'])
    seeds |= {d['file'] for d in meta['declarations'].values() if d['file'].startswith('Sal/')}
    seeds |= {'Sal/MRDTs/Paper1/OperationLabelsInvariant.lean',
              'Sal/MRDTs/Instances/NotionSplitSpec.lean',
              'Sal/MRDTs/Instances/NotionFormattingCounterexample.lean'}
    files, pending = set(), list(seeds)
    tracked = set(subprocess.check_output(['git', 'ls-files'], cwd=ROOT, text=True).splitlines())
    while pending:
        filename = pending.pop()
        if filename in files:
            continue
        if filename not in tracked or not (ROOT / filename).is_file():
            raise SystemExit('Missing or untracked source dependency: ' + filename)
        files.add(filename)
        for line in (ROOT / filename).read_text().splitlines():
            if line.startswith('import '):
                pending.extend(mod.replace('.', '/') + '.lean' for mod in line[7:].split()
                               if mod.startswith('Sal.'))
    shutil.copytree(TEMPLATE, out, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
    for filename in sorted(files | {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json'}):
        destination = out / filename
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / filename, destination)
    measurements = out / 'measurements'
    measurements.mkdir(exist_ok=True)
    for name in ['current-counts.json', 'metatheory-counts.json', 'table.md', 'implementation_table.tex']:
        shutil.copyfile(ROOT / 'experiments/paper-implementation' / name, measurements / name)
    # Preserve the original counting code, changing only its imports and revision
    # lookup so it works without the larger repository ledger or .git directory.
    adaptations = []
    for name in ['measure.py', 'measure_metatheory.py']:
        text = (ROOT / 'experiments/paper-implementation' / name).read_text()
        text = text.replace('Sal.MRDTs.Metatheory.RefactorLedger', 'Sal.Artifact.Paper')
        text = text.replace('Sal.MRDTs.Paper1.Ledger', 'Sal.Artifact.Paper')
        for variable in ['ROOT', 'root']:
            expression = "subprocess.check_output(['git','rev-parse','HEAD'],cwd=" + variable + ",text=True).strip()"
            text = text.replace(expression, "json.loads((" + variable + "/'provenance.json').read_text())['source_revision']")
        write(out / 'measurements' / name, text)
        adaptations.append('measurements/' + name + ': artifact ledger import and provenance.json revision lookup')
    verifier = (ROOT / 'scripts/verify-paper1-automation.py').read_text()
    audit_node = next(n for n in ast.parse(verifier).body if isinstance(n, ast.Assign)
                      and any(isinstance(t, ast.Name) and t.id == 'LEAN_AUDIT' for t in n.targets))
    # Extract only the pure case descriptions and audit command used by counting;
    # the full development auditor reads a repository-only ledger at import time.
    support = verifier.split('# Existing Ledger already rejects', 1)[0]
    support += '\n' + ast.get_source_segment(verifier, audit_node) + '\n'
    write(out / 'scripts/verify-paper1-automation.py', support)
    contracts = (ROOT / 'scripts/check-paper1-automation-contracts.py').read_text()
    stripper = next(n for n in ast.parse(contracts).body
                    if isinstance(n, ast.FunctionDef) and n.name == 'strip_comments')
    write(out / 'scripts/check-paper1-automation-contracts.py',
          ast.get_source_segment(contracts, stripper) + '\n')
    adaptations.append('scripts: extract unchanged case descriptions, Lean audit command and comment stripper; omit repository-only audit runners')
    roots = {n for row in counts['paper_rows'].values() for names in row['roots'].values() for n in names}
    roots |= set(meta['roots'])
    roots |= {
        'Sal.MRDTs.Paper1.OperationLabels.specificationRA',
        'Sal.MRDTs.Paper1.OperationLabels.eventVersionsRA',
        'Sal.MRDTs.Paper1.OperationLabelsInvariant.projectedVersionsRA',
        'Sal.MRDTs.Paper1.OperationLabels.issuance_issue',
        'Sal.MRDTs.Paper1.OperationLabels.issuance_rejects_mismatch',
        'Sal.MRDTs.Paper1.OperationLabels.identified_labels_control',
        'Sal.MRDTs.Instances.NotionSplitSpec.minimized_split_zero_rejects_ordinary_contract',
        'Sal.MRDTs.Instances.NotionFormattingCounterexample.two_character_reversal',
        'Sal.MRDTs.Instances.NotionFormattingCounterexample.noncontiguous_selection_overformats',
        'Sal.MRDTs.Instances.NotionFormattingCounterexample.contiguous_selection_control',
    }
    imports = '\n'.join('import ' + f[:-5].replace('/', '.') for f in sorted(seeds))
    audit = r'''
/-!
# Paper artifact entry point

Build with `lake build Sal.Artifact.Paper`. Imports retain the exact source
files measured for the paper; no repository-wide ledger or Git checkout is
required. See docs/claims-and-theorems.md for the research claims and hypotheses,
and measurements/current-counts.json for each datatype's selected roots.
The checks below fail if any advertised root is absent or depends on an axiom
outside Lean's standard logical axioms (including any unfinished proof).
-/
open Lean Elab Command in
elab "audit_paper " n:ident : command => do
  let root ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← liftCoreM <| Lean.collectAxioms root
  for ax in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "{root} depends on unapproved axiom {ax}"
  logInfo m!"PAPER_CHECKED {root} {axioms}"
'''
    write(out / 'Sal/Artifact/Paper.lean', imports + '\n' + audit + '\n' +
          '\n'.join('audit_paper ' + root for root in sorted(roots)) + '\n')
    shutil.copyfile(ROOT / 'experiments/notion-oracle/regression-observations.jsonl',
                    out / 'notion/recorded-observations.jsonl')
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    provenance = {'source_revision': revision, 'lean_source_count': len(files),
                  'selected_roots': sorted(roots), 'paper_rows': counts['paper_row_count'],
                  'configurations': counts['configuration_count'],
                  'source_sha256': {f: sha(ROOT / f) for f in sorted(files)},
                  'packaging_adaptations': adaptations,
                  'dependency_only_gc_modules': sorted(f for f in files if 'GC' in f),
                  'scope': 'Paper proofs and supporting reproductions; no GC result is an artifact claim.'}
    write(out / 'provenance.json', json.dumps(provenance, indent=2) + '\n')
    hashes = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob('*')) if p.is_file()}
    write(out / 'manifest.json', json.dumps({'sha256': hashes}, indent=2) + '\n')
    if args.archive:
        archive = out.with_suffix('.tar.gz')
        if archive.exists():
            raise SystemExit('Refusing to overwrite archive: ' + str(archive))
        with tarfile.open(archive, 'w:gz') as tar:
            tar.add(out, arcname=out.name)
        print(archive)
    print(f'Exported {len(files)} Lean sources, {len(roots)} checked roots, {len(hashes)} files to {out}')


if __name__ == '__main__':
    main()
