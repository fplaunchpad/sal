#!/usr/bin/env python3
"""Check cached source hashes, run offline probes on demo and corrected merge.

No fetch path exists. Module edits live only in temporary directories.
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
spec = importlib.util.spec_from_file_location('merge_runner', MERGE / 'run.py')
merge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(merge)


def run(cache, output):
    manifest_path = HERE.parent / 'notion-oracle' / 'sources.json'
    manifest, sources = merge.patch.load_pinned(cache, manifest_path)
    before = {m['file']: hashlib.sha256((cache / m['file']).read_bytes()).hexdigest()
              for m in manifest['modules']}
    reports = {}
    with tempfile.TemporaryDirectory(prefix='notion-formatting-') as temporary:
        for variant in ['demo', 'design']:
            work = merge.workdir(Path(temporary), variant, sources)
            shutil.copyfile(HERE / 'probes.mjs', work / 'formatting-probes.mjs')
            for name in ['candidate-planner.mjs', 'candidate-probes.mjs']:
                shutil.copyfile(HERE / name, work / name)
            probes = subprocess.run(['node', 'formatting-probes.mjs'], cwd=work,
                                    text=True, capture_output=True, check=True)
            candidate = subprocess.run(['node', 'candidate-probes.mjs'], cwd=work,
                                       text=True, capture_output=True, check=True)
            gate = subprocess.run(['node', 'gate.mjs'], cwd=work,
                                  text=True, capture_output=True, check=True)
            reports[variant] = json.loads(probes.stdout)
            reports[variant]['candidate'] = json.loads(candidate.stdout)
            reports[variant]['recordedRegressions'] = [c for c in json.loads(gate.stdout)['cases']
                                                      if c['name'].startswith(('N-002', 'N-003'))]
    after = {m['file']: hashlib.sha256((cache / m['file']).read_bytes()).hexdigest()
             for m in manifest['modules']}
    assert before == after, 'Cached source changed during probe run'
    output.mkdir(parents=True, exist_ok=True)
    for variant, report in reports.items():
        (output / f'{variant}.json').write_text(json.dumps(report, indent=2) + '\n')
    summary = {'sourceManifest': str(manifest_path.relative_to(HERE.parent.parent)),
               'sourceHashes': before, 'cachedSourcesUnchanged': True,
               'node': subprocess.check_output(['node', '--version'], text=True).strip(),
               'variants': {v: {**r['summary'], 'candidate': r['candidate']['summary'],
                                'recordedRegressions': r['recordedRegressions']}
                            for v, r in reports.items()}}
    (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache', required=True, type=Path)
    parser.add_argument('--results', type=Path, default=HERE / 'results')
    args = parser.parse_args()
    try:
        run(args.cache, args.results)
    except subprocess.CalledProcessError as error:
        if error.stderr:
            print(error.stderr, file=sys.stderr, end='')
        raise
