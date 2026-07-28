// VIRTUAL LCAs: DistributedReplica resolves criss-cross merges by the
// mechanized recursive rule instead of throwing. The directed store is a
// criss-cross shape; expected reads are HAND-DERIVED from the OR-set survival
// rule (live iff in all three, or born in exactly one branch), and the FAIL
// companions pin the machine-refuted single-MCA shortcuts: picking either
// single MCA as the base resurrects a delete.

import test from 'node:test';
import assert from 'node:assert/strict';
import { compactibleEmbedRGA } from '../src/compact.js';
import { DistributedReplica } from '../src/replica.js';

const read = (r) => r.read().join('');
const exchange = (p, q) => {
  q.ingest(p.delta(q.ancestryGids()));
  p.ingest(q.delta(p.ancestryGids()));
};

/** Build the criss-cross: heads whose maximal common ancestors are the
 *  ANTICHAIN {a1, b1}. Returns the replicas at the crossing point. */
function buildCrissCross() {
  const A = new DistributedReplica(compactibleEmbedRGA, 'A');
  const B = new DistributedReplica(compactibleEmbedRGA, 'B');
  A.commit({ type: 'ins', id: 1, el: 'x', anchorId: null });  // a1
  B.commit({ type: 'ins', id: 2, el: 'y', anchorId: null });  // b1
  const a1gid = A.headGid;
  exchange(A, B);
  A.mergeWithGid(B.headGid);                    // mA: {x,y}
  A.commit({ type: 'del', id: 1 });             // a2: head A reads "y"
  B.commit({ type: 'del', id: 2 });             // b2: head B reads ""
  B.mergeWithGid(a1gid);                        // mB = merge(b2, a1): reads "x"
  exchange(A, B);
  return { A, B };
}

test('criss-cross merges through the virtual base; deletes both stick', () => {
  const { A, B } = buildCrissCross();
  assert.equal(read(A), 'y', 'A head before the crossing merge');
  assert.equal(read(B), 'x', 'B head before the crossing merge');

  // heads (a2, mB) have MCAs {a1, b1}: the
  // virtual fold: base = merge3(root, {x}, {y}) = {x,y}; final
  // merge3({x,y}, {y}, {x}) kills both (each deleted on one side).
  const g = A.mergeWithGid(B.headGid);
  assert.equal(read(A), '', 'both deletes stick: the meet fold');

  // FAIL companions (the refuted single-MCA picks, hand-derived): base a1
  // ({x}) would resurrect y; base b1 ({y}) would resurrect x.
  assert.notEqual(read(A), 'y', 'not the pick-a1 resurrection');
  assert.notEqual(read(A), 'x', 'not the pick-b1 resurrection');

  // the other replica gets the merge commit over the wire (its ingest
  // re-resolves the same criss-cross) and lands on the identical head
  B.ingest(A.delta(B.ancestryGids()));
  B.mergeWithGid(g);
  assert.equal(B.headGid, g, 'same head SHA on both replicas');
  assert.equal(read(B), '', 'same read');
});

test('a wire merge commit resolved virtually re-ingests under the content gate', () => {
  const { A, B } = buildCrissCross();
  A.mergeWithGid(B.headGid); // the virtual-resolved merge commit
  const C = new DistributedReplica(compactibleEmbedRGA, 'C');
  const n = C.ingest(A.delta(C.ancestryGids())); // replays ALL commits incl. the criss-cross merge
  assert.ok(n >= 7, `full history ingested (${n} commits)`);
  C.mergeWithGid(A.headGid);
  assert.equal(C.headGid, A.headGid, 'content addresses agree');
  assert.equal(read(C), '', 'recomputed state agrees');
});

test('randomized: mesh syncs never throw and converge (criss-crosses included)', () => {
  let seed = 0x5eed;
  const rng = () => { seed = (seed * 1664525 + 1013904223) >>> 0; return seed / 2 ** 32; };
  const names = ['P', 'Q', 'R'];
  const reps = names.map((n) => new DistributedReplica(compactibleEmbedRGA, n));
  let id = 0;
  for (let round = 0; round < 40; round++) {
    for (const r of reps) {
      if (rng() < 0.7) {
        const view = compactibleEmbedRGA.readIds(r.head.state);
        if (view.length > 2 && rng() < 0.3) r.commit({ type: 'del', id: view[Math.floor(rng() * view.length)] });
        else {
          const nid = ++id * 100 + names.indexOf(r.name);
          const anchor = view.length && rng() < 0.6 ? view[Math.floor(rng() * view.length)] : null;
          r.commit({ type: 'ins', id: nid, el: 'abcdefgh'[nid % 8], anchorId: anchor });
        }
      }
    }
    // random pairwise sync: exchange, then BOTH merge the pre-exchange head
    // pair (the rival-merge genesis that mints criss-crosses)
    const i = Math.floor(rng() * 3); let j = Math.floor(rng() * 3);
    if (j === i) j = (j + 1) % 3;
    const gi = reps[i].headGid, gj = reps[j].headGid;
    exchange(reps[i], reps[j]);
    reps[i].mergeWithGid(gj);
    reps[j].mergeWithGid(gi);
  }
  // full closure: everyone syncs with everyone until stable
  for (let k = 0; k < 3; k++) {
    for (const p of reps) for (const q of reps) {
      if (p !== q) { exchange(p, q); p.mergeWithGid(q.headGid); }
    }
  }
  const r0 = read(reps[0]);
  assert.ok(r0.length > 0, 'non-trivial document');
  for (const r of reps) {
    assert.equal(read(r), r0, `${r.name} converged`);
    assert.equal(r.headGid, reps[0].headGid, `${r.name} same head SHA`);
  }
});
