#!/usr/bin/env python3
"""Export only the paper's measured Lean dependency closure and support files."""
import argparse
import ast
import hashlib
import gzip
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


def anonymous_text(text):
    # Token-boundary replacements preserve words such as “causal” and all lines.
    text = text.replace('Types* (Soundarapandian,\nKamath, Nagar, Sivaramakrishnan; PLDI 2022)', 'Types* (PLDI\n2022)')
    text = re.sub(r'\bVimala\b', 'CertifiedMRDTs2022', text)
    return re.sub(r'\bsal\b', 'artifact', re.sub(r'\bSal\b', 'Artifact', text))


def anonymise(out):
    """Rename the project without changing proof structure or source line counts."""
    # The paper closure never invokes this legacy tactic macro. Remove it and
    # its import, retaining blank lines so paper/source references remain exact.
    interface = out / 'Sal/Interfaces/Set_Extended.lean'
    original = interface.read_text()
    unused = 'macro "neem" : tactic =>\n  `(tactic| first | grind | blaster)'
    assert original.count('import Blaster\n') == original.count(unused) == 1
    for path in (out / 'Sal').rglob('*.lean'):
        if path != interface and re.search(r'\b(neem|blaster|Blaster)\b', path.read_text()):
            raise SystemExit('Unexpected dependency on the removed tactic: ' + str(path))
    stripped = original.replace('import Blaster\n', '\n').replace(unused, '\n')
    assert stripped.count('\n') == original.count('\n')
    write(interface, stripped)
    config = (out / 'lakefile.toml').read_text()
    config, removed = re.subn(r'\[\[require\]\]\nname = "Blaster"\n.*?(?=\[\[)', '', config, flags=re.S)
    assert removed == 1
    write(out / 'lakefile.toml', config)
    lock = json.loads((out / 'lake-manifest.json').read_text())
    lock['packages'] = [p for p in lock['packages'] if p['name'] != 'Blaster']
    write(out / 'lake-manifest.json', json.dumps(lock, indent=2) + '\n')
    # Transform text and paths in one pass. Third-party notices remain untouched.
    for path in sorted(out.rglob('*')):
        if not path.is_file() or 'vendor' in path.relative_to(out).parts:
            continue
        data = anonymous_text(path.read_text())
        if path.suffix == '.json':
            obj = json.loads(data)
            for key in ('source_revision', 'repo_head', 'git_head'):
                if key in obj:
                    obj[key] = 'anonymous-source-snapshot'
            data = json.dumps(obj, indent=2) + '\n'
        write(path, data)
    (out / 'Sal').rename(out / 'Artifact')
    for path in sorted(out.rglob('*'), key=lambda p: len(p.parts), reverse=True):
        if 'vendor' in path.relative_to(out).parts:
            continue
        new_name = anonymous_text(path.name)
        if new_name != path.name:
            path.rename(path.with_name(new_name))
    # The published digests describe the renamed sources; line counts are invariant.
    for name in ('provenance.json', 'measurements/current-counts.json'):
        path = out / name
        obj = json.loads(path.read_text())
        obj['source_sha256'] = {f: sha(out / f) for f in obj['source_sha256']}
        if name == 'provenance.json':
            obj['packaging_adaptations'] += [
                'Neutral project/module names; no change to proof structure or source line counts.',
                'Repository revision metadata removed; source hashes recomputed after renaming.',
                'Unused legacy tactic macro and its package dependency removed; source line numbers preserved.']
        write(path, json.dumps(obj, indent=2) + '\n')
    forbidden = re.compile(r'\bSal\b|\bsal\b|kayceesrk|kcsrk|fplaunchpad|Sivaramakrishnan|Soundarapandian|Vimala|Kartik|/Users/kc|olp_[A-Za-z0-9]+', re.I)
    for path in out.rglob('*'):
        if path.is_file() and (forbidden.search(str(path.relative_to(out))) or forbidden.search(path.read_text())):
            raise SystemExit('Anonymity check failed in generated file: ' + str(path.relative_to(out)))


def anonymous_tar_info(info):
    info.uid = info.gid = 0
    info.uname = info.gname = ''
    info.mtime = 0
    info.pax_headers = {}
    return info


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
              'Sal/MRDTs/Instances/NotionFormattingCounterexample.lean',
              'Sal/MRDTs/Instances/NotionMergeLossCounterexample.lean'}
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
        'Sal.MRDTs.Instances.NotionMergeLossCounterexample.merge_into_removed_block_hides_document',
        'Sal.MRDTs.Instances.NotionMergeLossCounterexample.document_loss_unexplained',
        'Sal.MRDTs.Instances.NotionMergeLossCounterexample.live_target_control',
        'Sal.MRDTs.Instances.NotionMergeLossCounterexample.cyclic_merge_removal_hides_character',
        'Sal.MRDTs.Instances.NotionMergeLossCounterexample.character_loss_unexplained',
        'Sal.MRDTs.Instances.NotionMergeLossCounterexample.acyclic_target_control',
        'Sal.MRDTs.Instances.NotionCoreProtocol.specification_ra',
        'Sal.MRDTs.Instances.NotionCoreMRDTClient.merge_effect',
        'Sal.MRDTs.Instances.NotionCoreSpecMerge.merge_text_conserved',
        'Sal.MRDTs.Instances.NotionCoreStructuralRender.SPOT.merge_outside_scope',
    }
    imports = '\n'.join('import ' + f[:-5].replace('/', '.') for f in sorted(seeds))
    audit = r'''
/-!
# Paper artifact entry point

Build with `lake build Sal.Artifact.Paper`. Imports retain the proofs measured
for the paper, with neutral module names; no repository-wide ledger or Git checkout is
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
    anonymise(out)
    hashes = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob('*')) if p.is_file()}
    write(out / 'manifest.json', json.dumps({'sha256': hashes}, indent=2) + '\n')
    if args.archive:
        archive = out.with_suffix('.tar.gz')
        if archive.exists():
            raise SystemExit('Refusing to overwrite archive: ' + str(archive))
        with archive.open('wb') as raw:
            with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as zipped:
                with tarfile.open(fileobj=zipped, mode='w') as tar:
                    tar.add(out, arcname=out.name, filter=anonymous_tar_info)
        write(Path(str(archive) + '.sha256'), sha(archive) + '  ' + archive.name + '\n')
        print(archive)
    print(f'Exported {len(files)} Lean sources, {len(roots)} checked roots, {len(hashes)} files to {out}')


if __name__ == '__main__':
    main()
