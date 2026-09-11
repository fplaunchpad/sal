// Measure the steady-state cost of a Peritext document after all visible
// content is deleted, state GC fires, a quiet peer acknowledges the epoch, and
// commit history is pruned. This is a measurement harness, not a proof.

import { performance } from 'node:perf_hooks';
import { DistributedReplica, syncReplicas } from '../src/replica.js';
import { compactiblePeritext } from '../src/compact-peritext.js';

function run(n) {
  const a = new DistributedReplica(compactiblePeritext, 'A');
  const b = new DistributedReplica(compactiblePeritext, 'B');
  a.register('B'); b.register('A');
  const start = performance.now();

  for (let id = 1; id <= n; id++)
    a.commit({ type: 'ins', id, el: 'x', anchorId: id === 1 ? null : id - 1 });
  syncReplicas(a, b);
  for (let id = 1; id <= n; id++) a.commit({ type: 'del', id });
  syncReplicas(a, b);
  b.commit({ type: 'del', id: n }); // quiet-state evidence; state stays empty
  syncReplicas(a, b);

  const commitsBefore = a.dag.size;
  const compacted = a.compactStable();
  if (!compacted.compacted) throw new Error(`compaction refused: ${compacted.reason}`);
  syncReplicas(a, b); // fetch-aligned receipt, no post-compaction datatype op
  const pruned = a.pruneToEpochBase();
  if (pruned.pruned === 0) throw new Error(`pruning refused: ${pruned.reason}`);

  return {
    operations: 2 * n + 1,
    commitsBefore,
    commitsAfter: a.dag.size,
    stateBytes: a.saveBytes(),
    symbols: a.symbolCount(),
    visibleChars: a.read().length,
    elapsedMs: Number((performance.now() - start).toFixed(2)),
  };
}

const rows = [10, 100, 1000].map(run);
console.table(rows);
if (!rows.every((r) => r.commitsAfter === 1 && r.symbols === 0 && r.visibleChars === 0))
  throw new Error('empty-document steady-state bound failed');
if (!rows.every((r) => r.stateBytes === rows[0].stateBytes))
  throw new Error('empty datatype state grew with deleted history');
