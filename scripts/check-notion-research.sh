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
  Sal.MRDTs.Instances.NotionCoreSourceGuards \
  Sal.MRDTs.Instances.NotionCoreOriginTree \
  Sal.MRDTs.Instances.NotionCorePartition \
  Sal.MRDTs.Instances.NotionCorePreparation \
  Sal.MRDTs.Instances.NotionCorePhysicalReplay \
  Sal.MRDTs.Instances.NotionCoreIssuance \
  Sal.MRDTs.Instances.NotionCoreParentMap \
  Sal.MRDTs.Instances.NotionCoreParentCoupling \
  Sal.MRDTs.Instances.NotionCorePayload \
  Sal.MRDTs.Instances.NotionCorePayloadNetwork \
  Sal.MRDTs.Instances.NotionCorePayloadParents \
  Sal.MRDTs.Instances.NotionCoreReplayGraph \
  Sal.MRDTs.Instances.NotionCoreExtractionEdges \
  Sal.MRDTs.Instances.NotionCoreParentErase \
  Sal.MRDTs.Instances.NotionCoreDisplayOrder \
  Sal.MRDTs.Instances.NotionCoreMachine \
  Sal.MRDTs.Instances.NotionCoreMachineRows \
  Sal.MRDTs.Instances.NotionCoreMachinePrefix \
  Sal.MRDTs.Instances.NotionCoreMachineSlices \
  Sal.MRDTs.Instances.NotionCoreCreatorNetwork \
  Sal.MRDTs.Instances.NotionCoreMachineCreators \
  Sal.MRDTs.Instances.NotionCoreMachineClient \
  Sal.MRDTs.Instances.NotionCoreMachineBirths \
  Sal.MRDTs.Instances.NotionCoreRanges \
  Sal.MRDTs.Instances.NotionCoreMachineDelete \
  Sal.MRDTs.Instances.NotionCoreReconstruction \
  Sal.MRDTs.Instances.NotionCoreMachineNetwork \
  Sal.MRDTs.Instances.NotionCoreTableView \
  Sal.MRDTs.Instances.NotionCoreArchiveOrder \
  Sal.MRDTs.Instances.NotionCoreMachineTables \
  Sal.MRDTs.Instances.NotionCoreMachineTableGraph \
  Sal.MRDTs.Instances.NotionCoreForestRefs \
  Sal.MRDTs.Instances.NotionCoreMachineRouting \
  Sal.MRDTs.Instances.NotionCoreMachinePartition \
  Sal.MRDTs.Instances.NotionCoreMachinePartitionCreate \
  Sal.MRDTs.Instances.NotionCoreMachineSplice \
  Sal.MRDTs.Instances.NotionCoreMachineErase \
  Sal.MRDTs.Instances.NotionCoreMachineCanonicalForest \
  Sal.MRDTs.Instances.NotionCoreMachineCreatorPresence \
  Sal.MRDTs.Instances.NotionCoreMachinePartitionUpdates \
  Sal.MRDTs.Instances.NotionCoreMachineCanonicalCreate \
  Sal.MRDTs.Instances.NotionCoreMachineMarkerProgress \
  Sal.MRDTs.Instances.NotionCoreMachineInactiveTitleBoundary \
  Sal.MRDTs.Instances.NotionCoreMachineBootstrap \
  Sal.MRDTs.Instances.NotionCoreMachinePartitionSplit \
  Sal.MRDTs.Instances.NotionCoreMachineCanonicalSplit \
  Sal.MRDTs.Instances.NotionCoreRootCreators \
  Sal.MRDTs.Instances.NotionCoreMachineRootReplay \
  Sal.MRDTs.Instances.NotionCoreMachineHonestReplay \
  Sal.MRDTs.Instances.NotionCoreBootstrapProvenance \
  Sal.MRDTs.Instances.NotionCoreMachineShape \
  Sal.MRDTs.Instances.NotionCoreMachineClientShape \
  Sal.MRDTs.Instances.NotionCoreMachineDisplay \
  Sal.MRDTs.Instances.NotionCoreMachineBlockPresence \
  Sal.MRDTs.Instances.NotionCoreMachineFreshText \
  Sal.MRDTs.Instances.NotionCoreMachineDeleteTotal \
  Sal.MRDTs.Instances.NotionCoreMachineClientTotal \
  Sal.MRDTs.Instances.NotionCoreMachineDocument \
  Sal.MRDTs.Instances.NotionCoreMachineDocumentCreate \
  Sal.MRDTs.Instances.NotionCoreMachineDocumentErase \
  Sal.MRDTs.Instances.NotionCoreMachineCommands \
  Sal.MRDTs.Instances.NotionCoreMachineDocumentClient \
  Sal.MRDTs.Instances.NotionCoreMachineDocumentInvariant \
  Sal.MRDTs.Instances.NotionCoreMachineDocumentInsert \
  Sal.MRDTs.Instances.NotionCoreMachineDocumentBootstrap \
  Sal.MRDTs.Instances.NotionCoreMachineDocumentSplit \
  Sal.MRDTs.Instances.NotionCoreMachineClientEffects \
  Sal.MRDTs.Instances.NotionCoreMachineInsertEffects \
  Sal.MRDTs.Instances.NotionCoreMachineHistory \
  Sal.MRDTs.Instances.NotionCoreMachineEraseIssueEffects \
  Sal.MRDTs.Instances.NotionCoreMachineSplitEffects \
  Sal.MRDTs.Instances.NotionCoreMachineVersionTables \
  Sal.MRDTs.Instances.NotionCoreSliceForest

check_dir=$(mktemp -d "${TMPDIR:-/tmp}/sal-notion-check.XXXXXX")
printf 'Notion check logs: %s\n' "$check_dir"
python3 experiments/notion-oracle/run.py --systematic > "$check_dir/systematic.jsonl"
python3 experiments/notion-oracle/run.py --trace regressions.mjs > "$check_dir/regressions.jsonl"
python3 experiments/notion-oracle/run.py --trace identity-check.mjs > "$check_dir/identity.jsonl"
python3 experiments/notion-oracle/run.py --trace core-adversarial.mjs > "$check_dir/core-adversarial.jsonl"
python3 experiments/notion-oracle/run.py --trace allocation-controls.mjs > "$check_dir/allocation-controls.jsonl"
python3 experiments/notion-oracle/run.py --trace preparation-boundary.mjs > "$check_dir/preparation-boundary.jsonl"
python3 experiments/notion-oracle/run.py --trace physical-replay-controls.mjs > "$check_dir/physical-replay-controls.jsonl"
python3 experiments/notion-oracle/run.py --trace replay-prefix-instrumentation.mjs > "$check_dir/replay-prefix-instrumentation.jsonl"
python3 experiments/notion-oracle/run.py --trace payload-provenance-controls.mjs > "$check_dir/payload-provenance-controls.jsonl"
python3 experiments/notion-oracle/run.py --trace search-label-controls.mjs > "$check_dir/search-label-controls.jsonl"
python3 experiments/notion-oracle/run.py --trace endpoint-adjacency-controls.mjs > "$check_dir/endpoint-adjacency-controls.jsonl"
python3 experiments/notion-oracle/run.py --trace client-provenance-controls.mjs > "$check_dir/client-provenance-controls.jsonl"
python3 experiments/notion-oracle/run.py --trace delete-group-controls.mjs > "$check_dir/delete-group-controls.jsonl"
python3 experiments/notion-oracle/run.py --trace split-phase-controls.mjs > "$check_dir/split-phase-controls.jsonl"
python3 experiments/notion-oracle/run.py --trace inactive-title-controls.mjs > "$check_dir/inactive-title-controls.jsonl"
python3 experiments/notion-oracle/run.py --trace active-instance-controls.mjs > "$check_dir/active-instance-controls.jsonl"
node experiments/notion-oracle/identity-controls.mjs > "$check_dir/identity-controls.jsonl"
python3 - "$check_dir" <<'PY'
import json
from pathlib import Path
import sys
root = Path(sys.argv[1])
for name in ['systematic', 'regressions', 'identity', 'identity-controls', 'core-adversarial', 'allocation-controls', 'preparation-boundary', 'physical-replay-controls', 'replay-prefix-instrumentation', 'payload-provenance-controls', 'search-label-controls', 'endpoint-adjacency-controls', 'client-provenance-controls', 'delete-group-controls', 'split-phase-controls', 'inactive-title-controls', 'active-instance-controls']:
    rows = [json.loads(line) for line in (root / (name + '.jsonl')).read_text().splitlines()]
    print(f'{name}: {len(rows)} result records; executable assertions passed')
print('Known-failure regression success means the counterexamples reproduce.')
PY
