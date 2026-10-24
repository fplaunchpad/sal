#!/usr/bin/env python3
"""Validate shared-priority formatting using offline temporary pinned copies."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


merge = load('atomic_priority_merge', HERE.parent / 'notion-merge-design' / 'run.py')
priority = load('atomic_priority_patch', HERE / 'atomic-priority-patch.py')


def hashes(directory, manifest):
    return {module['file']: hashlib.sha256((directory / module['file']).read_bytes()).hexdigest()
            for module in manifest['modules']}


def toggle_source(text):
    return text[text.index('\ttoggleBold('):text.index('\tcreateBlock(')]


def run(cache, output, variants):
    manifest_path = HERE.parent / 'notion-oracle' / 'sources.json'
    manifest, sources = merge.patch.load_pinned(cache, manifest_path)
    before = hashes(cache, manifest)
    planner_hash = hashlib.sha256((HERE / 'candidate-planner.mjs').read_bytes()).hexdigest()
    reports = {}
    with tempfile.TemporaryDirectory(prefix='notion-atomic-priority-') as temporary:
        controls = Path(temporary) / 'per-segment-control'
        controls.mkdir()
        for variant in variants:
            # A broken arbitration rule must still fail on the established
            # whole-transaction witness. Run its unchanged harness before
            # applying the repair in a separate temporary source directory.
            old_work = merge.workdir(controls, variant, sources)
            for filename in ['candidate-planner.mjs', 'atomic-fracture.mjs']:
                shutil.copyfile(HERE / filename, old_work / filename)
            old_result = subprocess.run(['node', 'atomic-fracture.mjs'], cwd=old_work,
                                        text=True, capture_output=True, check=True)
            old_report = json.loads(old_result.stdout)
            assert old_report['summary']['flags'] == '10011'
            assert old_report['summary']['passFailControlsHold']
            work = merge.workdir(Path(temporary), variant, sources)
            current = {name: (work / name).read_text() for name in sources}
            repaired = priority.apply(current)
            for name, text in repaired.items():
                (work / name).write_text(text)
            assert toggle_source((work / 'replica.js').read_text()) == toggle_source(sources['replica.js'])
            for filename in ['candidate-planner.mjs', 'atomic-priority-adapter.mjs', 'atomic-priority-probes.mjs',
                             'atomic-priority-generated.mjs']:
                shutil.copyfile(HERE / filename, work / filename)
            working = hashes(work, manifest)
            result = subprocess.run(['node', 'atomic-priority-probes.mjs'], cwd=work,
                                    text=True, capture_output=True, check=True)
            assert working == hashes(work, manifest), 'Working modules changed during execution'
            assert planner_hash == hashlib.sha256((work / 'candidate-planner.mjs').read_bytes()).hexdigest()
            reports[variant] = json.loads(result.stdout)
            generated = subprocess.run(['node', 'atomic-priority-generated.mjs'], cwd=work,
                                       text=True, capture_output=True, check=True)
            reports[variant]['generated'] = json.loads(generated.stdout)
            assert working == hashes(work, manifest), 'Generated gate changed working source modules'
            reports[variant]['knownBrokenPerSegmentControl'] = old_report['summary']
            reports[variant]['workingModuleHashes'] = working
            reports[variant]['originalToggleBoldUnchanged'] = True
            reports[variant]['candidatePlannerUnchanged'] = True
    assert before == hashes(cache, manifest), 'Pinned cached sources changed'
    report = {'schema': 'notion-formatting-atomic-priority-run-v1',
              'sourceManifest': str(manifest_path.relative_to(HERE.parent.parent)),
              'sourceHashes': before, 'cachedSourcesUnchanged': True,
              'candidatePlannerHash': planner_hash,
              'node': subprocess.check_output(['node', '--version'], text=True).strip(),
              'variants': reports}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'output': str(output), 'cachedSourcesUnchanged': True,
                      'variants': {variant: {'targeted': result['summary'],
                                            'generated': result['generated']['summary']}
                                   for variant, result in reports.items()}}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache', required=True, type=Path)
    parser.add_argument('--output', type=Path, default=HERE / 'results' / 'atomic-priority.json')
    parser.add_argument('--variants', nargs='+', choices=['design', 'slice-following'],
                        default=['slice-following', 'design'])
    arguments = parser.parse_args()
    try:
        run(arguments.cache, arguments.output, arguments.variants)
    except subprocess.CalledProcessError as error:
        if error.stderr:
            print(error.stderr, file=sys.stderr, end='')
        raise
