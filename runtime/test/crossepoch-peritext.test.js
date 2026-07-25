// CROSS-EPOCH MERGE for PERITEXT (regression). The #112 epoch join lifts a
// state DOWN to a common frame through the epoch's INVERSE translate map, which
// is built by buildInverseTranslate over the COORDINATE-bearing sub-state. For
// embedRGA that is the whole state; for PERITEXT it is the text SHADOW. The
// datatype exposes it via `coordState`, and the replica routes the inverse
// builder through it -- WITHOUT this, buildInverseTranslate threw on peritext's
// nested { text, marks } object, translateInv was null, and every peritext
// cross-epoch merge DEFERRED (silent divergence between peers). The #112 tests
// only exercised embedRGA, so this gap slipped through; this pins it.

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
  // Pre-fix this THREW ('inverse epoch map unavailable') and was deferred.
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
