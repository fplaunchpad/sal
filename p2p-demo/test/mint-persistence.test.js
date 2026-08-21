import test from 'node:test';
import assert from 'node:assert/strict';
import { Node } from '../src/node.js';
import { nodeRecords, rebuildNode } from '../src/records.js';
import { compactiblePeritext } from '../../runtime/src/compact-peritext.js';

test('Lamport mint survives durable reload independently of GC state', () => {
  const original = new Node(compactiblePeritext, 'A', { mint: { slot: 31 } });
  const first = original.commitGenerated({ type: 'ins', el: 'x', anchorId: null }).payload;
  const deleted = original.commitGenerated({ type: 'del', id: first.id }).payload;
  assert.equal(original.compactStable().compacted, true, 'entered a state-GC epoch');
  original.pruneToEpochBase();
  const saved = nodeRecords(original);
  const restored = rebuildNode(saved.records, saved.heads, compactiblePeritext);
  const second = restored.generate({ type: 'ins', el: 'y', anchorId: first.id });
  assert.equal(restored.exportMintState().slot, 31);
  assert.ok(second.id > deleted.time, 'clock survives after its causal commits were pruned');
});

test('opening as a new replica never inherits the old replica slot', () => {
  const original = new Node(compactiblePeritext, 'A', { mint: { slot: 31 } });
  original.commitGenerated({ type: 'ins', el: 'x', anchorId: null });
  const saved = nodeRecords(original);
  assert.throws(() => rebuildNode(saved.records, saved.heads, compactiblePeritext, { name: 'B' }).mintTime(),
    /unique persistent mint slot/);
  const b = rebuildNode(saved.records, saved.heads, compactiblePeritext, { name: 'B', mint: { slot: 32 } });
  assert.equal(b.exportMintState().slot, 32);
});
