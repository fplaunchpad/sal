#!/usr/bin/env sh
set -eu

# Separate research gate: the production ledger intentionally does not register
# an unfinished Notion document certificate.
lake build \
  Sal.MRDTs.Instances.NotionSplitSpec \
  Sal.MRDTs.Instances.NotionFormattingCounterexample \
  Sal.MRDTs.Instances.NotionTransactionSet

check_dir=$(mktemp -d "${TMPDIR:-/tmp}/sal-notion-check.XXXXXX")
printf 'Notion check logs: %s\n' "$check_dir"
python3 experiments/notion-oracle/run.py --systematic > "$check_dir/systematic.jsonl"
python3 experiments/notion-oracle/run.py --trace regressions.mjs > "$check_dir/regressions.jsonl"
python3 experiments/notion-oracle/run.py --trace identity-check.mjs > "$check_dir/identity.jsonl"
node experiments/notion-oracle/identity-controls.mjs > "$check_dir/identity-controls.jsonl"
python3 - "$check_dir" <<'PY'
import json
from pathlib import Path
import sys
root = Path(sys.argv[1])
for name in ['systematic', 'regressions', 'identity', 'identity-controls']:
    rows = [json.loads(line) for line in (root / (name + '.jsonl')).read_text().splitlines()]
    print(f'{name}: {len(rows)} result records; executable assertions passed')
print('Known-failure regression success means the counterexamples reproduce.')
PY
