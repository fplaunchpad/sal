#!/usr/bin/env python3
"""Check every shipped file, source measurement and local Lean import."""
import hashlib
import json
import os
from pathlib import Path

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / 'manifest.json').read_text())['sha256']
# Build products and locally downloaded demo modules are not shipped sources.
ignored_dirs = {'.lake', 'results', 'vendor/notion'}
for name in ('yjs', 'automerge', 'loro'):
    ignored_dirs.add(f'ra-pbt/instances/{name}/node_modules')
for name in ('yjs-oracle', 'automerge-oracle', 'loro-oracle', 'notion-ra-pbt'):
    ignored_dirs.add(f'experiments/{name}/results')
    ignored_dirs.add(f'experiments/{name}/repro/node_modules')
ignored_dirs.add('experiments/yjs-oracle/repro/v14/node_modules')
actual = set()
for directory, dirs, names in os.walk(root):
    relative = Path(directory).relative_to(root)
    dirs[:] = [name for name in dirs
               if name != '__pycache__' and str(relative / name) not in ignored_dirs]
    for name in names:
        if not name.endswith('.pyc'):
            actual.add(str(relative / name))
extra = actual - set(manifest) - {'manifest.json'}
if extra:
    raise SystemExit('Unexpected artifact file(s): ' + ', '.join(sorted(extra)))
for filename, expected in manifest.items():
    path = root / filename
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise SystemExit('Missing or changed artifact file: ' + filename)
counts = json.loads((root / 'measurements/current-counts.json').read_text())
for filename, expected in counts['source_sha256'].items():
    if hashlib.sha256((root / filename).read_bytes()).hexdigest() != expected:
        raise SystemExit('Source differs from the paper measurement: ' + filename)
for path in (root / 'Sal').rglob('*.lean'):
    for line in path.read_text().splitlines():
        if line.startswith('import '):
            for module in line[7:].split():
                if module.startswith('Sal.') and not (root / (module.replace('.', '/') + '.lean')).is_file():
                    raise SystemExit(f'Unresolved local import in {path}: {module}')
print(f'Verified {len(manifest)} artifact files, {len(counts["source_sha256"])} measured source hashes, and local imports.')
