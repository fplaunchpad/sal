// CROSS-EPOCH LIFT (Case 1, #97 lazy translation), distributed. A straggler
// that authored on its old-epoch head merges ACROSS a peer's compaction by
// LIFTING its edits into the new epoch, record by record, through the epoch's
// translate -- which it recomputes from the compact commit's parent state + the
// shipped cut (verified by fingerprint). This is the deployed editor's
// datatype (peritext), whose cut carries settled MARK mids as well as char ids,
// so it exercises the Set-valued cut serialization both ways. PASS+FAIL shaped:
// Case 1 converges (and matches a never-compacted control); Case 2 (two peers,
// incomparable cuts) stays refused.

import test from 'node:test';
import assert from 'node:assert/strict';
import { compactiblePeritext } from '../src/compact-peritext.js';
import { DistributedReplica, syncReplicas } from '../src/replica.js';

const mint = (k) => k * 1000 + 7;
const textOf = (r) => r.read().map((e) => e.char).join('');
const boldOf = (r) => r.read().map((e) => (e.marks.some((m) => m.mtype === 'bold') ? '1' : '0')).join('');

// build "abcdefghij", delete a few, bold a settled span -- enough for the
// marks-layer GC to actually compact (settled tombstones + a settled span)
function seed(r) {
  const ops = [];
  for (let i = 1; i <= 10; i++) {
    ops.push({ type: 'ins', id: mint(i), el: 'abcdefghij'[i - 1], anchorId: i === 1 ? null : mint(i - 1) });
  }
  ops.push({ type: 'del', id: mint(3) });
  ops.push({ type: 'del', id: mint(7) });
  ops.push({ type: 'addMark', mid: mint(100), mtype: 'bold', startId: mint(1), endId: mint(4),
    startSide: 'before', endSide: 'after', ts: mint(100) });
  r.commitBatch(ops);
}

test('CASE 1 (peritext): a straggler with a local edit lifts across a compaction', () => {
  const a = new DistributedReplica(compactiblePeritext, 'A');
  const b = new DistributedReplica(compactiblePeritext, 'B');
  a.register('B'); b.register('A');
  seed(a);
  syncReplicas(a, b);
  // B contributes so its evidence covers the cut, then both converge at epoch 0
  b.commit({ type: 'ins', id: mint(11), el: 'k', anchorId: mint(10) });
  syncReplicas(a, b);
  const text0 = textOf(a), bold0 = boldOf(a);
  assert.equal(a.epoch, 0);

  // A compacts alone (drops the settled tombstones / collapses the settled span)
  const g = a.compactStable();
  assert.equal(g.compacted, true, 'A compacted');
  assert.equal(a.epoch, 1); assert.equal(b.epoch, 0);
  assert.equal(textOf(a), text0, 'A reads unchanged by its own GC');

  // B authors a LOCAL edit on its epoch-0 head, then merges across A's epoch
  b.commit({ type: 'ins', id: mint(12), el: 'Z', anchorId: mint(11) });
  b.ingest(a.delta(b.ancestryGids())); // carries A's compaction WITH its cut
  b.mergeWithGid(a.headGid);           // Case 1: lift B's 'Z' into epoch 1
  assert.equal(b.epoch, 1, 'B lifted to epoch 1');
  assert.equal(textOf(b), text0 + 'Z', 'B kept its edit and absorbed the compaction');
  assert.equal(boldOf(b), bold0 + '0', 'the settled bold span survived the lift');

  // symmetric convergence
  a.ingest(b.delta(a.ancestryGids()));
  a.mergeWithGid(b.headGid);
  assert.equal(a.headGid, b.headGid, 'same head SHA across the epoch');
  assert.equal(textOf(a), textOf(b));

  // twin: a never-compacted control that took the identical op stream
  const ctl = new DistributedReplica(compactiblePeritext, 'C');
  seed(ctl);
  ctl.commit({ type: 'ins', id: mint(11), el: 'k', anchorId: mint(10) });
  ctl.commit({ type: 'ins', id: mint(12), el: 'Z', anchorId: mint(11) });
  assert.equal(textOf(a), textOf(ctl), 'lifted reads == never-compacted control (text)');
  assert.equal(boldOf(a), boldOf(ctl), 'lifted reads == never-compacted control (marks)');
});

test('CASE 2 (peritext): two peers compacting incomparable cuts stay refused', () => {
  const a = new DistributedReplica(compactiblePeritext, 'A');
  const b = new DistributedReplica(compactiblePeritext, 'B');
  a.register('B'); b.register('A');
  seed(a);
  syncReplicas(a, b);
  b.commit({ type: 'ins', id: mint(11), el: 'k', anchorId: mint(10) });
  syncReplicas(a, b);
  assert.equal(a.compactStable().compacted, true);
  assert.equal(b.compactStable().compacted, true); // rival epoch-1 re-coding
  assert.notEqual(a.headGid, b.headGid);
  a.ingest(b.delta(a.ancestryGids()));
  assert.throws(() => a.mergeWithGid(b.headGid), /cross-epoch merge/,
    'incomparable-cut compaction stays the deferred half');
});

test('CASE 1 survives persistence: a reloaded compaction still lets a straggler lift', async () => {
  const { nodeRecords, rebuildNode } = await import('../../p2p-demo/src/records.js');
  const a = new DistributedReplica(compactiblePeritext, 'A');
  const b = new DistributedReplica(compactiblePeritext, 'B');
  a.register('B'); b.register('A');
  seed(a);
  syncReplicas(a, b);
  b.commit({ type: 'ins', id: mint(11), el: 'k', anchorId: mint(10) });
  syncReplicas(a, b);
  const text0 = textOf(a);
  assert.equal(a.compactStable().compacted, true); // A at epoch 1

  // PERSIST + REBUILD A (a hub or tab restart): the stored cut must let the
  // reloaded node recover the epoch's translate
  const { records, heads } = nodeRecords(a, { datatypeLabel: 'peritext' });
  assert.ok(records.some((r) => r.kind === 'compact' && r.cut), 'the cut is persisted with the compaction');
  const a2 = rebuildNode(records, heads, compactiblePeritext);

  // B (still epoch 0) authors locally, then lifts across the RELOADED epoch
  b.commit({ type: 'ins', id: mint(12), el: 'Z', anchorId: mint(11) });
  b.ingest(a2.delta(b.ancestryGids())); // a2 re-ships the cut it recovered
  b.mergeWithGid(a2.headGid);
  assert.equal(b.epoch, 1, 'B lifted across the reloaded compaction');
  assert.equal(textOf(b), text0 + 'Z', 'lift works after a restart');
});

test('CASE 1: a tampered cut is caught -- the lift stays refused, never mislifted', () => {
  const a = new DistributedReplica(compactiblePeritext, 'A');
  const b = new DistributedReplica(compactiblePeritext, 'B');
  a.register('B'); b.register('A');
  seed(a);
  syncReplicas(a, b);
  b.commit({ type: 'ins', id: mint(11), el: 'k', anchorId: mint(10) });
  syncReplicas(a, b);
  assert.equal(a.compactStable().compacted, true);
  b.commit({ type: 'ins', id: mint(12), el: 'Z', anchorId: mint(11) });
  const wire = a.delta(b.ancestryGids());
  const compact = wire.find((w) => w.kind === 'compact');
  assert.ok(compact && compact.cut, 'the compaction ships its cut');
  compact.cut.settledIds = { $set: [] }; // forge: claim NOTHING settled -> a
                                         // different re-coding than A shipped
  b.ingest(wire); // ingest still succeeds (the STATE is content-gated), but the
                  // translate recomputed from the forged cut does not reproduce
                  // that state, so it is rejected and the epoch stays un-lifted
  assert.throws(() => b.mergeWithGid(a.headGid), /cross-epoch merge/,
    'a cut whose recomputation disagrees is not trusted for lifting');
});
