#!/usr/bin/env python3
"""Reproduce the candidate's atomicity obstruction using offline pinned JS.

No source fetch or cache mutation occurs. Corrected merge patches apply only
inside a temporary work directory. The interval planner is copied unchanged.
"""
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
MERGE = HERE.parent / 'notion-merge-design'
spec = importlib.util.spec_from_file_location('atomic_merge_runner', MERGE / 'run.py')
merge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(merge)


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
    with tempfile.TemporaryDirectory(prefix='notion-atomic-fracture-') as temporary:
        for variant in variants:
            work = merge.workdir(Path(temporary), variant, sources)
            for filename in ['candidate-planner.mjs', 'atomic-fracture.mjs']:
                shutil.copyfile(HERE / filename, work / filename)
            working_before = hashes(work, manifest)
            assert toggle_source((work / 'replica.js').read_text()) == toggle_source(sources['replica.js']), \
                'Corrected merge patch changed original toggleBold'
            result = subprocess.run(['node', 'atomic-fracture.mjs'], cwd=work,
                                    text=True, capture_output=True, check=True)
            assert working_before == hashes(work, manifest), 'Working source modules changed during execution'
            assert planner_hash == hashlib.sha256((work / 'candidate-planner.mjs').read_bytes()).hexdigest(), \
                'Copied candidate planner changed during execution'
            reports[variant] = json.loads(result.stdout)
            reports[variant]['workingModuleHashes'] = working_before
            reports[variant]['workingModulesUnchangedDuringExecution'] = True
            reports[variant]['originalToggleBoldUnchanged'] = True
            reports[variant]['candidatePlannerUnchangedDuringExecution'] = True
    assert before == hashes(cache, manifest), 'Pinned cached source modules changed'
    report = {'schema': 'notion-formatting-atomic-fracture-run-v1',
              'sourceManifest': str(manifest_path.relative_to(HERE.parent.parent)),
              'sourceHashes': before, 'cachedSourcesUnchanged': True,
              'candidatePlannerHash': planner_hash,
              'node': subprocess.check_output(['node', '--version'], text=True).strip(),
              'variants': reports}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'output': str(output), 'cachedSourcesUnchanged': True,
                      'variants': {variant: result['summary'] for variant, result in reports.items()}}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache', required=True, type=Path)
    parser.add_argument('--output', type=Path, default=HERE / 'results' / 'atomic-fracture.json')
    parser.add_argument('--variants', nargs='+', choices=['design', 'slice-following'],
                        default=['slice-following', 'design'])
    arguments = parser.parse_args()
    try:
        run(arguments.cache, arguments.output, arguments.variants)
    except subprocess.CalledProcessError as error:
        if error.stderr:
            print(error.stderr, file=sys.stderr, end='')
        raise
