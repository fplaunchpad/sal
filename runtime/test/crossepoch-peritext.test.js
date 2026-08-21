// CROSS-EPOCH MERGE for PERITEXT. The epoch join lifts a state DOWN to a
// common frame through the epoch's INVERSE translate map, which is built by
// buildInverseTranslate over the COORDINATE-bearing sub-state. For embedRGA
// that is the whole state; for PERITEXT it is the text SHADOW. The datatype
// exposes it via `coordState`, and the replica routes the inverse builder
// through it. Without this routing, buildInverseTranslate throws on peritext's
// nested { text, marks } object, translateInv is null, and every peritext
// cross-epoch merge defers (silent divergence between peers). This pins it.

import test from 'node:test';
import assert from 'node:assert/strict';
import { DistributedReplica, syncReplicas } from '../src/replica.js';
import { compactiblePeritext } from '../src/compact-peritext.js';

const mint = (k) => k * 1000 + 7;
const txt = (r) => r.read().map((e) => e.char).join('');

test('a peritext straggler merges a compaction ACROSS an epoch and converges', () => {
  const a = new DistributedReplica(compactiblePeritext, 'A');
  const b = new DistributedReplica(compactiblePeritext, 'B');
  a.register('B'); b.register('A');
  const ops = [];
  for (let i = 1; i <= 12; i++) ops.push({ type: 'ins', id: mint(i), el: 'abcdefghijkl'[i - 1], anchorId: i === 1 ? null : mint(i - 1) });
  for (const d of [3, 7, 10]) ops.push({ type: 'del', id: mint(d) }); // tombstones for the GC
  a.commitBatch(ops);
  syncReplicas(a, b);
  b.commit({ type: 'ins', id: mint(50), el: '!', anchorId: mint(12) }); // B contributes -> cut complete
  syncReplicas(a, b);
  const readConverged = txt(a);

  // A compacts alone -> epoch 1; B stays at epoch 0
  assert.equal(a.compactStable().compacted, true, 'A compacted');
  assert.equal(a.epoch, 1); assert.equal(b.epoch, 0);

  // B authors a LOCAL edit on its epoch-0 head, then merges A's epoch-1 head.
  b.commit({ type: 'ins', id: mint(60), el: 'Z', anchorId: mint(50) });
  b.ingest(a.delta(b.ancestryGids()));
  b.mergeWithGid(a.headGid); // must NOT throw
  assert.equal(txt(b), readConverged + 'Z', 'B kept its edit AND absorbed the compaction');

  // symmetric convergence, same head SHA
  a.ingest(b.delta(a.ancestryGids()));
  a.mergeWithGid(b.headGid);
  assert.equal(txt(a), txt(b), 'A and B converge across the epoch');
  assert.equal(a.headGid, b.headGid, 'same head SHA');

  // twin: a never-compacted control that took the identical op stream reads the same
  const ctl = new DistributedReplica(compactiblePeritext, 'C');
  ctl.commitBatch(ops);
  ctl.commit({ type: 'ins', id: mint(50), el: '!', anchorId: mint(12) });
  ctl.commit({ type: 'ins', id: mint(60), el: 'Z', anchorId: mint(50) });
  assert.equal(txt(a), txt(ctl), 'lifted reads == never-compacted control');
});

test('the peritext datatype exposes coordState (the text shadow)', () => {
  const a = new DistributedReplica(compactiblePeritext, 'A');
  a.commit({ type: 'ins', id: mint(1), el: 'x', anchorId: null });
  const cs = compactiblePeritext.coordState(a.head.state);
  assert.equal(cs, a.head.state.text.shadow, 'coordState is the text shadow (the coord-bearing sub-state)');
});

test('a concurrent mark restores its collected endpoint across epochs', () => {
  const a = new DistributedReplica(compactiblePeritext, 'A');
  const b = new DistributedReplica(compactiblePeritext, 'B');
  a.register('B'); b.register('A');
  a.commit({ type: 'ins', id: mint(1), el: 'x', anchorId: null });
  a.commit({ type: 'ins', id: mint(2), el: 'y', anchorId: mint(1) });
  syncReplicas(a, b);
  a.commit({ type: 'del', id: mint(2) });
  syncReplicas(a, b);
  // B's authored acknowledgement makes the delete stable, but B remains on
  // the old epoch when A subsequently compacts the unmarked dead endpoint.
  b.commit({ type: 'del', id: mint(2) });
  syncReplicas(a, b);
  assert.equal(a.compactStable().compacted, true);
  assert.equal(a.head.state.text.shadow.has(mint(2)), false, 'A collected endpoint y');

  b.commit({ type: 'addMark', mid: mint(9), mtype: 'bold', value: true,
    startId: mint(1), endId: mint(2), startSide: 'before', endSide: 'after' });
  syncReplicas(a, b); // invokes the physical merge-coverage audit
  assert.equal(a.head.state.text.shadow.has(mint(2)), true,
    'the old-epoch branch restores the endpoint required for continuation');
  assert.deepEqual(a.read(), b.read());

  const control = new DistributedReplica(compactiblePeritext, 'C');
  control.commit({ type: 'ins', id: mint(1), el: 'x', anchorId: null });
  control.commit({ type: 'ins', id: mint(2), el: 'y', anchorId: mint(1) });
  control.commit({ type: 'del', id: mint(2) });
  control.commit({ type: 'addMark', mid: mint(9), mtype: 'bold', value: true,
    startId: mint(1), endId: mint(2), startSide: 'before', endSide: 'after' });
  assert.deepEqual(a.read(), control.read(), 'compacted run equals never-compacted control');
});
