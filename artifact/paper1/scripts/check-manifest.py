#!/usr/bin/env python3
"""Check every shipped file, source measurement and local Lean import."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / 'manifest.json').read_text())['sha256']
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
