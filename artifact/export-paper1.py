#!/usr/bin/env python3
"""Export only the paper's measured Lean dependency closure and support files."""
import argparse
import ast
import hashlib
import gzip
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
TEMPLATE = ROOT / 'artifact' / 'paper1'

# Executable support is selected explicitly; the Lean import closure below
# continues to require tracked sources. These trees contain only first-party
# harnesses and lockfiles, not the libraries they execute.
PBT_EXPERIMENTS = ('yjs-oracle', 'automerge-oracle', 'loro-oracle', 'notion-ra-pbt',
                   'notion-production-text', 'notion-production-blocks')
RUNTIME_TESTS = ('ingest', 'hash', 'dag', 'rga', 'virtual-lca', 'commitbatch', 'applybatch', 'mint')
PRODUCTION_CLIENT = 'experiments/notion-production-client'
PRODUCTION_EXPORT_INPUTS = {f'{PRODUCTION_CLIENT}/{name}' for name in
                            ('client.mjs', 'index.mjs', 'runtime.mjs', 'requests.mjs', 'sources.json')}


def copy_pbt_support(out):
    selected = set()
    for directory in ('ra-pbt', 'runtime/src',
                      *(f'experiments/{n}' for n in PBT_EXPERIMENTS)):
        for here, dirs, names in os.walk(ROOT / directory, followlinks=False):
            dirs[:] = sorted(d for d in dirs if d not in {
                'node_modules', '.git', '.lake', '__pycache__', 'results',
                'cache', 'extracted', 'extracted-replay'})
            for name in sorted(names):
                path = Path(here) / name
                if path.is_symlink():
                    raise SystemExit('Refusing symlink in executable support: ' + str(path))
                if path.suffix not in {'.js', '.mjs', '.py', '.json', '.md'} or name.startswith('upstream-drafts'):
                    continue
                selected.add(str(path.relative_to(ROOT)))
    selected |= {'runtime/package.json', 'experiments/notion-oracle/sources.json',
                 'experiments/notion-merge-design/design-patch/patch.py'}
    selected |= {f'runtime/test/{name}.test.js' for name in RUNTIME_TESTS}
    # An explicit allow-list keeps all downloaded assets and generated module
    # bodies out, regardless of the names used for local cache/export folders.
    selected |= {f'{PRODUCTION_CLIENT}/{name}' for name in (
        'client.mjs', 'index.mjs', 'runtime.mjs', 'requests.mjs', 'sources.json',
        'extract.mjs', 'download.py', 'replay.mjs', 'run-replays.mjs', 'package.json',
        'package-lock.json', 'README.md', 'test/extraction.test.mjs', 'test/replays.test.mjs')}
    pins = json.loads((ROOT / 'ra-pbt/instances/notion-production-text/sources.json').read_text())['exportFiles']
    for filename in PRODUCTION_EXPORT_INPUTS:
        if sha(ROOT / filename) != pins[Path(filename).name]:
            raise SystemExit('Pinned production export input changed: ' + filename)
    # Include the first-party sequential specifications imported by adapters;
    # these are outside the experiment-driver trees selected above.
    pending = list(selected)
    while pending:
        filename = pending.pop()
        if Path(filename).suffix not in {'.js', '.mjs'}:
            continue
        text = (ROOT / filename).read_text()
        for ref in re.findall(r'''(?:from\s*|import\s*)['"](\.[^'"]+)['"]''', text):
            dependency = (ROOT / filename).parent.joinpath(ref).resolve()
            if not dependency.is_relative_to(ROOT) or 'node_modules' in dependency.parts:
                raise SystemExit('Unexpected executable support import: ' + ref + ' in ' + filename)
            if not dependency.is_file():
                raise SystemExit('Missing executable support import: ' + ref + ' in ' + filename)
            relative = str(dependency.relative_to(ROOT))
            if relative not in selected:
                selected.add(relative)
                pending.append(relative)
    for filename in sorted(selected):
        destination = out / filename
        destination.parent.mkdir(parents=True, exist_ok=True)
        text = (ROOT / filename).read_text()
        if filename.startswith('experiments/notion-production-') and Path(filename).suffix == '.md':
            link = os.path.relpath(out / 'docs/production-client.md', destination.parent)
            text = '# Extracted client experiment support\n\n' \
                   f'See the [reviewed reproduction guide]({link}) for commands, source pins, ' \
                   'specification choices and protocol limits. The supplied executable histories ' \
                   'are offline fixture experiments, not observations of the live service.\n'
        elif filename not in PRODUCTION_EXPORT_INPUTS:
            text = text.replace('docs/notion-production-blocks.md', 'docs/production-client.md')
            text = text.replace('docs/notion-production-text.md', 'docs/production-client.md')
        if filename.endswith('/repro/README.md'):
            # Posted reports link back to identifying user accounts. Keep the
            # executable reproductions and version table, omit report history.
            text = re.sub(r'\nPosted upstream\b.*\Z', '\n', text, flags=re.S)
        write(destination, text)

    recorded = out / 'recorded/pbt'
    record_inputs = {}
    for name in PBT_EXPERIMENTS:
        for path in sorted((ROOT / 'experiments' / name / 'results').glob('*.json')):
            # Large raw failing-trial dumps and logs are intentionally omitted.
            # Keep aggregate counters and every already-shrunk representative.
            if path.name.startswith('left-search-'):
                continue
            data = json.loads(path.read_text())
            if name.startswith('notion-production-'):
                # Host paths identify only the review machine, not the source.
                def neutral_paths(value):
                    if isinstance(value, dict):
                        return {k: neutral_paths(v) for k, v in value.items()}
                    if isinstance(value, list):
                        return [neutral_paths(v) for v in value]
                    if isinstance(value, str) and value.startswith(('/Users/', '/private/tmp/', '/tmp/')):
                        return 'external-source-path'
                    return value
                data = neutral_paths(data)
                if path.name == 'out-of-order.json':
                    for run in data.values():
                        if isinstance(run, dict):
                            run.pop('failing', None)
            if path.name == 'campaign.json' and name != 'notion-ra-pbt':
                for run in data.get('runs', []):
                    run.pop('trials', None)
                    if 'source' in run:
                        run['omitted_raw_source'] = run.pop('source')
                data['artifact_selection'] = 'Aggregate counters and all stored representatives; per-trial records, raw search dumps and logs omitted.'
            write(recorded / name / path.name, json.dumps(data, indent=2) + '\n')
            record_inputs[str(path.relative_to(ROOT))] = sha(path)
    write(recorded / 'selection.json', json.dumps({
        'input_sha256': record_inputs,
        'selection': 'Top-level JSON evidence, with per-trial lists removed from external campaign summaries; all stored representative schedules retained.',
        'omitted': ['node_modules and downloaded third-party sources', 'upstream-drafts and posted-report history',
                    'raw campaign subdirectories and logs', 'redundant Loro left-search no-failure dumps'],
        'interpretation': 'Historical bounded experiments, not library proofs. Notion law snapshots predate inconclusive-status reporting; rerun current code for honest statuses. Production-client campaign verdicts predate review: pending or rejected records are not same-record-set divergence, and causal witness failures are not automatically failures of the paper criterion. See docs/production-client.md.',
    }, indent=2) + '\n')
    return selected


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(data)


def anonymous_text(text):
    # Token-boundary replacements preserve words such as “causal” and all lines.
    text = text.replace('// "SAL", binary-wire version 1', '// Binary-wire version 1; original magic bytes retained.')
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
        if str(path.relative_to(out)) in PRODUCTION_EXPORT_INPUTS:
            # extract.mjs copies these files verbatim into the separately
            # acquired library. Renaming/reformatting would invalidate its pins.
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
            obj['support_source_sha256'] = {f: sha(out / f) for f in obj['support_source_sha256']}
            obj['packaging_adaptations'] += [
                'Neutral project/module names; no change to proof structure or source line counts.',
                'Repository revision metadata removed; source hashes recomputed after renaming.',
                'Unused legacy tactic macro and its package dependency removed; source line numbers preserved.',
                'Original binary-wire magic bytes retained for format compatibility; identifying comment neutralized.']
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
              'Sal/MRDTs/Instances/NotionMergeLossCounterexample.lean',
              'Sal/MRDTs/Instances/YjsMarkerCounterexample.lean',
              'Sal/MRDTs/Instances/YjsDeleteSetCounterexample.lean'}
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
    support_files = copy_pbt_support(out)
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
    adaptations += [
        'Executable PBT harnesses, exact npm lockfiles, external-library verifiers and standalone reproductions included; third-party installations excluded.',
        'Runtime source plus eight portable test files included, including the binary overlapping-delta ingest regression; no runtime extraction or GC result claimed.',
        'Recorded campaign summaries retain aggregate counters and all stored representatives, omitting per-trial lists, raw search dumps and logs; recorded/pbt/selection.json identifies inputs.',
        'Posted-report drafts and identifying upstream-report history omitted from reproduction READMEs.',
        'Notion PBT includes its original seven-module source manifest and exact design patcher; anchor-absorb is an older experiment, separate from the current rich Lean model.',
        'Production-client support includes only first-party acquisition/extraction/harness code; downloaded assets and generated module bodies are acquired outside the bundle.',
        'The five production export inputs are preserved byte-for-byte to reproduce the same six pinned library files. Production experiment READMEs point to a curated reviewed guide; source note paths in harness diagnostics are adapted.',
        'Production recorded machine paths are neutralized; raw failing lists in the out-of-order probe are omitted, preserving summaries and shrunk representatives. Historical pre-review verdicts are not promoted to deployment claims.',
    ]
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
        'Sal.MRDTs.Instances.YjsMarkerCounterexample.merged_not_sequential',
        'Sal.MRDTs.Instances.YjsMarkerCounterexample.closer_control',
        'Sal.MRDTs.Instances.YjsMarkerCounterexample.live_closer_control',
        'Sal.MRDTs.Instances.YjsDeleteSetCounterexample.gap_render',
        'Sal.MRDTs.Instances.YjsDeleteSetCounterexample.delivery',
        'Sal.MRDTs.Instances.YjsDeleteSetCounterexample.integrated_not_closed',
        'Sal.MRDTs.Instances.YjsDeleteSetCounterexample.no_admitted_view',
        'Sal.MRDTs.Instances.YjsDeleteSetCounterexample.arrival_control',
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
                  'support_source_sha256': {f: sha(ROOT / f) for f in sorted(support_files)},
                  'packaging_adaptations': adaptations,
                  'dependency_only_gc_modules': sorted(f for f in files if 'GC' in f),
                  'scope': 'Paper proofs and supporting reproductions; no GC result is an artifact claim.'}
    write(out / 'provenance.json', json.dumps(provenance, indent=2) + '\n')
    anonymise(out)
    export_pins = json.loads((out / 'ra-pbt/instances/notion-production-text/sources.json').read_text())['exportFiles']
    for filename in PRODUCTION_EXPORT_INPUTS:
        if sha(out / filename) != export_pins[Path(filename).name]:
            raise SystemExit('Packaging changed a pinned production export input: ' + filename)
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
