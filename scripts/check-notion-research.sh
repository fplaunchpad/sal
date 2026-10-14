#!/usr/bin/env sh
set -eu

# Separate research gate: the production ledger intentionally does not register
# an unfinished Notion document certificate.
lake build \
  Sal.MRDTs.Instances.NotionSplitSpec \
  Sal.MRDTs.Instances.NotionFormattingCounterexample \
  Sal.MRDTs.Instances.NotionTransactionSet \
  Sal.MRDTs.Instances.NotionRunAllocation \
  Sal.MRDTs.Instances.NotionCoreSpec \
  Sal.MRDTs.Instances.NotionCoreInvariant \
  Sal.MRDTs.Instances.NotionCoreRGA \
  Sal.MRDTs.Instances.NotionCoreSource \
  Sal.MRDTs.Instances.NotionCoreSourceDocument \
  Sal.MRDTs.Instances.NotionCoreHistory \
  Sal.MRDTs.Instances.NotionCoreSourceHistory \
  Sal.MRDTs.Instances.NotionCoreSourceInvariant \
  Sal.MRDTs.Instances.NotionCoreSourceGuards

check_dir=$(mktemp -d "${TMPDIR:-/tmp}/sal-notion-check.XXXXXX")
printf 'Notion check logs: %s\n' "$check_dir"
python3 experiments/notion-oracle/run.py --systematic > "$check_dir/systematic.jsonl"
python3 experiments/notion-oracle/run.py --trace regressions.mjs > "$check_dir/regressions.jsonl"
python3 experiments/notion-oracle/run.py --trace identity-check.mjs > "$check_dir/identity.jsonl"
python3 experiments/notion-oracle/run.py --trace core-adversarial.mjs > "$check_dir/core-adversarial.jsonl"
python3 experiments/notion-oracle/run.py --trace allocation-controls.mjs > "$check_dir/allocation-controls.jsonl"
node experiments/notion-oracle/identity-controls.mjs > "$check_dir/identity-controls.jsonl"
python3 - "$check_dir" <<'PY'
import json
from pathlib import Path
import sys
root = Path(sys.argv[1])
for name in ['systematic', 'regressions', 'identity', 'identity-controls', 'core-adversarial', 'allocation-controls']:
    rows = [json.loads(line) for line in (root / (name + '.jsonl')).read_text().splitlines()]
    print(f'{name}: {len(rows)} result records; executable assertions passed')
print('Known-failure regression success means the counterexamples reproduce.')
PY
