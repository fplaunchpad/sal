#!/usr/bin/env python3
"""Run discovery probes against the pinned public Notion demo modules."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import argparse

root = Path(__file__).resolve().parent
manifest = json.loads((root / 'sources.json').read_text())
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--systematic', action='store_true', help='run the extended distinguishing suite')
parser.add_argument('--reachable', action='store_true', help='check local request effects after reachable concurrent merges')
parser.add_argument('--minimize', action='store_true', help='minimize the saved reachable failure by reissuing requests')
parser.add_argument('--core', action='store_true', help='restrict reachable generation to split/insert/delete')
parser.add_argument('--trace', help='run a named first-party .mjs experiment')
args = parser.parse_args()
if args.trace and (Path(args.trace).name != args.trace or not args.trace.endswith('.mjs') or not (root / args.trace).is_file()):
    parser.error('--trace must name an existing experiment .mjs file')
with tempfile.TemporaryDirectory(prefix='sal-notion-oracle-') as directory:
    work = Path(directory)
    (work / 'package.json').write_text('{"type":"module"}\n')
    for source in root.glob('*.mjs'):
        shutil.copy(source, work / source.name)
    if args.systematic or args.reachable or args.minimize:
        for name in ['systematic.mjs', 'reachable.mjs', 'minimize.mjs', 'transaction-set.mjs', 'positional-spec.mjs']:
            shutil.copy(root / name, work / name)
        if args.minimize:
            shutil.copy(root / 'reachable-observations.jsonl', work / 'reachable-observations.jsonl')
    for module in manifest['modules']:
        target = work / module['file']
        subprocess.run(['curl', '-fsSL', module['url'], '-o', str(target)], check=True)
        if hashlib.sha256(target.read_bytes()).hexdigest() != module['sha256']:
            raise SystemExit(f"Source changed: {module['file']}; review before updating the snapshot")
    command = ['node', str(work / (args.trace if args.trace else 'minimize.mjs' if args.minimize else 'reachable.mjs' if args.reachable else 'systematic.mjs' if args.systematic else 'traces.mjs'))]
    if args.core:
        command.append('--core')
    subprocess.run(command, check=True)
