#!/usr/bin/env python3
"""Run bounded testing support; downloads occur only with --install or the separate Notion downloader."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / 'results/pbt'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--external', action='store_true', help='also verify and test the pinned Yjs, Automerge and Loro installations')
    parser.add_argument('--install', action='store_true', help='npm ci --ignore-scripts for the three pinned instance packages; implies --external')
    parser.add_argument('--notion-cache', type=Path, help='also test the demo and older anchor-absorb model using these seven previously downloaded, hash-pinned modules')
    parser.add_argument('--production-cache', type=Path, help='also extract and test the 63 pinned public production assets from this complete existing cache; generated external code stays outside the package')
    args = parser.parse_args()
    RESULTS.mkdir(parents=True, exist_ok=True)
    report = {'scope': 'Bounded executable tests, not verification of external libraries or a GC result.', 'commands': []}
    env = os.environ.copy()

    def run(name, argv, cwd=ROOT):
        print(name + ': running', flush=True)
        result = subprocess.run(argv, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (RESULTS / (name + '.log')).write_text(result.stdout)
        report['commands'].append({'name': name, 'argv': argv, 'cwd': str(cwd.relative_to(ROOT)), 'exit_code': result.returncode})
        (RESULTS / 'summary.json').write_text(json.dumps(report, indent=2) + '\n')
        print(name + ': ' + ('PASS' if result.returncode == 0 else 'FAIL'), flush=True)
        if result.returncode:
            print(result.stdout[-8000:], file=sys.stderr)
            raise SystemExit(result.returncode)

    run('manifest', ['python3', 'scripts/check-manifest.py'])
    run('harness', ['node', '--test', *[str(p.relative_to(ROOT)) for p in sorted((ROOT / 'ra-pbt/test').glob('*.test.js'))]])
    run('runtime', ['npm', 'test'], ROOT / 'runtime')
    # The independent specification assertions need no third-party installation.
    for name in ('yjs', 'automerge', 'loro'):
        run(name + '-spec', ['node', f'experiments/{name}-oracle/spec-tests.mjs'])
    if args.external or args.install:
        for name in ('yjs', 'automerge', 'loro'):
            directory = ROOT / 'ra-pbt/instances' / name
            if args.install:
                run(name + '-install', ['npm', 'ci', '--ignore-scripts', '--no-audit', '--no-fund'], directory)
            run(name + '-pins', ['node', f'ra-pbt/instances/{name}/verify-sources.js'])
            run(name + '-regressions', ['node', f'experiments/{name}-oracle/run.mjs', '--mode', 'regressions'])
            run(name + '-pins-after', ['node', f'ra-pbt/instances/{name}/verify-sources.js'])
    if args.notion_cache:
        directory = ROOT / 'results/notion-pbt-sources'
        cache = directory / 'cache'
        cache.mkdir(parents=True, exist_ok=True)
        manifest = json.loads((ROOT / 'experiments/notion-oracle/sources.json').read_text())
        for module in manifest['modules']:
            shutil.copyfile(args.notion_cache.resolve() / module['file'], cache / module['file'])
        env['NOTION_RA_PBT_SOURCES'] = str(directory)
        run('notion-prepare', ['node', 'ra-pbt/instances/notion/prepare.js', '--offline'])
        run('notion-regressions', ['node', 'experiments/notion-ra-pbt/run.mjs', '--mode', 'regressions'])
    if args.production_cache:
        directory = ROOT / 'experiments/notion-production-client'
        if args.install:
            run('production-parser-install', ['npm', 'ci', '--ignore-scripts', '--no-audit', '--no-fund'], directory)
        cache = args.production_cache.resolve()
        asset_manifest = json.loads((directory / 'sources.json').read_text())
        if any(not (cache / asset['file']).is_file() for asset in asset_manifest['assets']):
            parser.error('production cache is incomplete; acquire the pinned public assets first with experiments/notion-production-client/download.py')
        env['NOTION_PRODUCTION_CACHE'] = str(cache)
        run('production-assets', ['python3', 'experiments/notion-production-client/download.py', '--cache', str(cache)])
        library = Path(tempfile.mkdtemp(prefix='editor-production-review-')) / 'library'
        env['NOTION_PRODUCTION_LIBRARY'] = str(library)
        run('production-extract', ['node', 'experiments/notion-production-client/extract.mjs', str(cache), str(library)])
        run('production-extraction-controls', ['npm', 'test'], directory)
        for name in ('text', 'blocks'):
            run('production-' + name + '-pins', ['node', f'ra-pbt/instances/notion-production-{name}/verify-sources.js'])
        run('production-text-spec', ['node', 'experiments/notion-production-text/spec-tests.mjs'])
        run('production-blocks-spec', ['node', '--test', 'ra-pbt/instances/notion-production-blocks/spec.test.js'])
        run('production-text-regressions', ['node', 'experiments/notion-production-text/run.mjs', '--mode', 'regressions'])
        run('production-blocks-regressions', ['node', 'experiments/notion-production-blocks/regressions.mjs'])
        run('production-review-controls', ['node', 'experiments/notion-production-blocks/review-controls.mjs'])
        for name in ('text', 'blocks'):
            run('production-' + name + '-pins-after', ['node', f'ra-pbt/instances/notion-production-{name}/verify-sources.js'])
    run('manifest-after', ['python3', 'scripts/check-manifest.py'])
    print('Results: results/pbt/summary.json (individual command logs alongside it).')


if __name__ == '__main__':
    main()
