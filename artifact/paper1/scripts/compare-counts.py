#!/usr/bin/env python3
"""Compare freshly generated measurements with the paper's recorded counts."""
import argparse
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--instances', type=Path, required=True, help='directory containing measurement.json')
p.add_argument('--metatheory', type=Path, required=True, help='directory containing sal-metatheory-count.json')
a = p.parse_args()
old = json.loads((root / 'measurements/current-counts.json').read_text())
new = json.loads((a.instances / 'measurement.json').read_text())
expected = {k: v['loc'] for k, v in old['paper_rows'].items()}
observed = {k: v['loc'] for k, v in new['paper_rows'].items()}
if expected != observed:
    raise SystemExit('Datatype table counts differ from the recorded paper measurement.')
if old['source_sha256'] != new['source_sha256']:
    raise SystemExit('Measured source set or hashes differ from the recorded paper measurement.')
old_meta = json.loads((root / 'measurements/metatheory-counts.json').read_text())
new_meta = json.loads((a.metatheory / 'sal-metatheory-count.json').read_text())
metrics = lambda x: {k: v['nonblank_noncomment_lines'] for k, v in x['metrics'].items()}
if metrics(old_meta) != metrics(new_meta):
    raise SystemExit('Metatheory counts differ from the recorded paper measurement.')
print(f'Matched all {len(expected)} datatype rows, {len(old["source_sha256"])} source hashes, and metatheory counts.')
