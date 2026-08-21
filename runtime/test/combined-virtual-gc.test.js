// End-to-end executable cell: distributed fetch + commit GC + Peritext state
// GC + a genuine virtual-LCA merge, checked against a never-collected twin.

import test from 'node:test';
import assert from 'node:assert/strict';
import { DistributedReplica } from '../src/replica.js';
import { compactiblePeritext } from '../src/compact-peritext.js';

const text = (r) => r.read().map((e) => e.char).join('');

function exchange(a, b) {
  b.ingest(a.delta(b.ancestryGids()));
  a.ingest(b.delta(a.ancestryGids()));
}

function sync(a, b) {
  const ah = a.headGid;
  const bh = b.headGid;
  exchange(a, b);
  a.mergeWithGid(bh);
  b.mergeWithGid(ah);
  a.acknowledgeFetch(b.name, b.headGid, b.epochKey);
  b.acknowledgeFetch(a.name, a.headGid, a.epochKey);
}

function pair(prefix) {
  const A = new DistributedReplica(compactiblePeritext, `${prefix}A`);
  const B = new DistributedReplica(compactiblePeritext, `${prefix}B`);
  A.register(B.name);
  B.register(A.name);
  return { A, B };
}

function prepareStableGarbage(W) {
  W.A.commit({ type: 'ins', id: 10, el: 'q', anchorId: null });
  sync(W.A, W.B);
  W.B.commit({ type: 'ins', id: 11, el: 'r', anchorId: 10 });
  sync(W.A, W.B);
  W.A.commit({ type: 'del', id: 10 });
  W.B.commit({ type: 'del', id: 11 });
  sync(W.A, W.B);
}

function buildCross(W) {
  W.A.commit({ type: 'ins', id: 101, el: 'x', anchorId: null });
  W.B.commit({ type: 'ins', id: 202, el: 'y', anchorId: null });
  const a1 = W.A.headGid;
  exchange(W.A, W.B);
  W.A.mergeWithGid(W.B.headGid);
  W.A.commit({ type: 'del', id: 101 });
  W.B.commit({ type: 'del', id: 202 });
  W.B.mergeWithGid(a1);
  exchange(W.A, W.B);
}

test('virtual Peritext merge composes with both GCs and matches a no-GC twin', () => {
  const control = pair('c');
  const collected = pair('g');
  prepareStableGarbage(control);
  prepareStableGarbage(collected);

  const compactA = collected.A.compactStable();
  assert.equal(compactA.compacted, true, compactA.reason);
  sync(collected.A, collected.B);
  const compactB = collected.B.compactStable();
  if (compactB.compacted) sync(collected.A, collected.B);

  buildCross(control);
  buildCross(collected);
  assert.equal(text(collected.A), text(control.A));
  assert.equal(text(collected.B), text(control.B));

  // Ingest has supplied authenticated frontier evidence for both current
  // heads. Collection must keep the recursive MCA closure needed below.
  const ga = collected.A.gc();
  const gb = collected.B.gc();
  assert.equal(ga.refused, false, ga.reason);
  assert.equal(gb.refused, false, gb.reason);
  assert.ok(ga.dropped + gb.dropped > 0, 'commit GC must genuinely collect');

  const controlRemote = control.B.headGid;
  const collectedRemote = collected.B.headGid;
  control.A.mergeWithGid(controlRemote);
  collected.A.mergeWithGid(collectedRemote);
  assert.equal(text(control.A), '', 'virtual base makes both deletes stick');
  assert.equal(text(collected.A), text(control.A), 'both-GC execution matches control');

  control.B.ingest(control.A.delta(control.B.ancestryGids()));
  collected.B.ingest(collected.A.delta(collected.B.ancestryGids()));
  control.B.mergeWithGid(control.A.headGid);
  collected.B.mergeWithGid(collected.A.headGid);
  assert.equal(text(collected.B), text(control.B));
  assert.equal(text(collected.B), '');
});
