// Representation canary: prefix-sharing coordinate nodes against real traces.
// This is not a paper benchmark or the production default. It gates semantic
// equality with the trace and records whether the proposed hot representation
// avoids full-path copying before integration with GC/epochs/serialization.

import { performance } from 'node:perf_hooks';
import { loadTrace, flattenOps } from '../lib/traces.mjs';
import { sharedEmbedRGA, encodeSharedState, decodeSharedState,
  encodeSharedRuns, decodeSharedRuns } from '../../runtime/src/datatypes/sharedEmbedRGA.js';
import { compactSharedDirect } from '../../runtime/src/shared-compact.js';

const traces = process.argv.slice(2);
if (traces.length === 0) traces.push('friendsforever_flat');

for (const name of traces) {
  const doc = loadTrace(name), ops = flattenOps(doc);
  let state = sharedEmbedRGA.init(), view = [], clock = 0;
  const t0 = performance.now();
  for (const op of ops) {
    clock++;
    if (op.t === 'i') {
      const anchorId = op.pos ? view[op.pos - 1] : null;
      state = sharedEmbedRGA.apply(state,
        { type: 'ins', id: clock, anchorId, el: op.ch });
      view.splice(op.pos, 0, clock);
    } else {
      state = sharedEmbedRGA.apply(state, { type: 'del', id: view[op.pos] });
      view.splice(op.pos, 1);
    }
  }
  const applyMs = performance.now() - t0;
  const r0 = performance.now();
  const text = sharedEmbedRGA.read(state).join('');
  const readMs = performance.now() - r0;
  if (text !== doc.endContent) throw new Error(`${name}: shared representation text mismatch`);
  const s0 = performance.now(), snapshot = encodeSharedState(state), encodeMs = performance.now() - s0;
  const d0 = performance.now(), restored = decodeSharedState(snapshot), decodeMs = performance.now() - d0;
  if (sharedEmbedRGA.read(restored).join('') !== text)
    throw new Error(`${name}: shared snapshot mismatch`);
  const rs0 = performance.now(), runSnapshot = encodeSharedRuns(state), runEncodeMs = performance.now() - rs0;
  const rd0 = performance.now(), runRestored = decodeSharedRuns(runSnapshot), runDecodeMs = performance.now() - rd0;
  if (sharedEmbedRGA.read(runRestored).join('') !== text)
    throw new Error(`${name}: shared run snapshot mismatch`);
  const settledIds = new Set(Array.from({ length: clock }, (_, i) => i + 1));
  const gc0 = performance.now();
  const compacted = compactSharedDirect(state, { settledIds }, { fuseSpines: true }).state;
  const gcMs = performance.now() - gc0, compactedSnapshot = encodeSharedRuns(compacted);
  if (sharedEmbedRGA.read(compacted).join('') !== text)
    throw new Error(`${name}: shared compaction mismatch`);
  console.log(JSON.stringify({ trace: name, operations: ops.length,
    finalChars: text.length, applyMs, readMs,
    retainedPathNodes: sharedEmbedRGA.nodeCount(state), snapshotBytes: snapshot.length,
    encodeMs, decodeMs, runSnapshotBytes: runSnapshot.length,
    runEncodeMs, runDecodeMs, compactedNodes: sharedEmbedRGA.nodeCount(compacted),
    compactedSnapshotBytes: compactedSnapshot.length, gcMs, gate: 'pass' }));
}
