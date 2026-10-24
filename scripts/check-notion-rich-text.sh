#!/usr/bin/env sh
set -eu

if [ "$#" -ne 1 ] || [ ! -d "$1" ]; then
  echo "Usage: sh scripts/check-notion-rich-text.sh PINNED_SOURCE_CACHE" >&2
  echo 'See experiments/notion-formatting/README.md for the pinned download command.' >&2
  exit 2
fi
source_cache=$1
check_dir=$(mktemp -d "${TMPDIR:-/tmp}/sal-rich-text-check.XXXXXX")
printf 'Rich-text check logs: %s\n' "$check_dir"

lake build Sal.MRDTs.Metatheory.NotionFormattingLedger > "$check_dir/lean.log" 2>&1
python3 experiments/notion-formatting/run.py --cache "$source_cache" \
  --results "$check_dir/original" > "$check_dir/original.log" 2>&1
python3 experiments/notion-formatting/run-atomic-fracture.py --cache "$source_cache" \
  --output "$check_dir/per-segment.json" > "$check_dir/per-segment.log" 2>&1
python3 experiments/notion-formatting/run-atomic-priority.py --cache "$source_cache" \
  --output "$check_dir/repaired.json" > "$check_dir/repaired.log" 2>&1

python3 - "$check_dir" <<'PY'
import json
from pathlib import Path
import sys

root = Path(sys.argv[1])
original = json.loads((root / 'original' / 'summary.json').read_text())
old = json.loads((root / 'per-segment.json').read_text())
repaired = json.loads((root / 'repaired.json').read_text())
assert original['cachedSourcesUnchanged'] and old['cachedSourcesUnchanged'] and repaired['cachedSourcesUnchanged']
assert original['sourceHashes'] == old['sourceHashes'] == repaired['sourceHashes']
for variant, result in original['variants'].items():
    regressions = result['recordedRegressions']
    failures = [r for r in regressions if 'control' not in r['name']]
    controls = [r for r in regressions if 'control' in r['name']]
    assert len(failures) == 2 and all(r['preconditionReached'] and not r['contractHolds'] for r in failures)
    assert controls and all(r['contractHolds'] for r in controls)
    print(f'{variant}: original N-002/N-003 reproduced; passing control preserved')
for variant, result in old['variants'].items():
    assert result['summary']['flags'] == '10011'
    print(f'{variant}: original per-segment obstruction reproduced')
for variant, result in repaired['variants'].items():
    targeted, generated = result['summary'], result['generated']['summary']
    assert targeted['fractureRepaired'] and generated['allPassed'] and generated['discarded'] == 0
    print(f"{variant}: {targeted['positiveAndNegativeControls']} directed and "
          f"{generated['pairedControls']} generated paired controls passed")
print('Lean ledger and all source gates passed; pinned caches unchanged.')
PY
