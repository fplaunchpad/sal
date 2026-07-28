// THE FIRST-CLASS DISTRIBUTED REPLICA (src/replica.js): one store
// with BOTH wire sync and certified compaction, exercised DIRECTLY (the p2p
// demo's Node is a thin re-export of this). Datatype-PARAMETRIC: every test
// that can run over orset as well as embedRGA does, proving the object is not
// embed-specific.
//
//   (a) convergence via delta gossip                    -- embed AND orset
//   (b) SHA content addressing: round-trip, dedup, gate  -- embed AND orset
//   (c) certified state GC: refuse-then-fire, reads kept -- embed (orset refuses)
//   (d) commit GC: prune below the horizon, reads kept   -- embed AND orset
//   (e) cross-epoch merge: the certificate-determined join (a coordinate
//       translation, reads == twin)

import test from 'node:test';
import assert from 'node:assert/strict';
import { DistributedReplica, syncReplicas } from '../src/replica.js';
import { compactibleEmbedRGA } from '../src/compact.js';
import { embedRGA } from '../src/datatypes/embedRGA.js';
import { orset } from '../src/datatypes/orset.js';

function mulberry32(seed) {
  let a = seed >>> 0;
  return () => { a = (a + 0x6d2b79f5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
}
const pick = (rng, xs) => xs[Math.floor(rng() * xs.length)];
const eq = (x) => JSON.stringify(x);

// ------------------------------------------------------------ (a) convergence
test('embedRGA: N replicas gossip over the wire and converge to equal reads', () => {
  const rng = mulberry32(0xD15);
  const N = 4;
  const reps = Array.from({ length: N }, (_, i) => new DistributedReplica(compactibleEmbedRGA, 'p' + i));
  let mint = 0;
  for (let round = 0; round < 20; round++) {
    for (let i = 0; i < N; i++) {
      const view = embedRGA.readIds(reps[i].head.state);
      if (view.length > 3 && rng() < 0.25) { reps[i].commit({ type: 'del', id: pick(rng, view) }); continue; }
      const id = ++mint;
      const anchorId = view.length && rng() < 0.7 ? pick(rng, view) : null;
      reps[i].commit({ type: 'ins', id, el: String.fromCharCode(97 + (id % 26)), anchorId });
    }
    // criss-cross-free linear fold into replica 0, then broadcast back
    for (let pass = 0; pass < 2; pass++) for (let k = 1; k < N; k++) syncReplicas(reps[0], reps[k]);
    const reads = reps.map((r) => r.read().join(''));
    for (let i = 1; i < N; i++) assert.equal(reads[i], reads[0], `round ${round}: p${i} diverged`);
  }
  assert.ok(reps[0].read().length > 5, 'a non-trivial document was built');
});

test('orset: N replicas gossip over the wire and converge (add-wins), PARAMETRIC', () => {
  const rng = mulberry32(0x0257E7);
  const N = 4;
  const reps = Array.from({ length: N }, (_, i) => new DistributedReplica(orset, 'p' + i));
  let tag = 0;
  for (let round = 0; round < 20; round++) {
    for (let i = 0; i < N; i++) {
      const live = orset.read(reps[i].head.state);
      if (live.length > 2 && rng() < 0.3) {
        reps[i].commit({ type: 'rm', tags: orset.observe(reps[i].head.state, pick(rng, live)) });
      } else {
        reps[i].commit({ type: 'add', tag: 'p' + i + '#' + (tag++), el: 'e' + Math.floor(rng() * 6) });
      }
    }
    for (let pass = 0; pass < 2; pass++) for (let k = 1; k < N; k++) syncReplicas(reps[0], reps[k]);
    const reads = reps.map((r) => eq(r.read()));
    for (let i = 1; i < N; i++) assert.equal(reads[i], reads[0], `round ${round}: orset p${i} diverged`);
  }
  assert.ok(reps[0].registered.size === N, 'heard of every replica over the wire');
});

// ------------------------------------------------------- (b) SHA addressing
test('SHA content addressing: round-trip, dedup, and the tamper gate (embed + orset)', () => {
  for (const dt of [compactibleEmbedRGA, orset]) {
    const a = new DistributedReplica(dt, 'A'), b = new DistributedReplica(dt, 'B');
    const op1 = dt === orset ? { type: 'add', tag: 'A#0', el: 'h' } : { type: 'ins', id: 1, el: 'h', anchorId: null };
    const op2 = dt === orset ? { type: 'add', tag: 'A#1', el: 'i' } : { type: 'ins', id: 2, el: 'i', anchorId: 1 };
    a.commit(op1); a.commit(op2);
    assert.equal(a.headGid.length, 40, 'commit ids are 40-hex SHA content ids');
    const d = a.delta(b.ancestryGids());
    assert.equal(b.ingest(d), 2, 'B ingests two commits');
    assert.equal(b.ingest(d), 0, 'idempotent: re-ingest adds nothing (SHA dedup)');
    b.mergeWithGid(a.headGid); // fast-forward B onto A's advertised head
    assert.equal(eq(a.read()), eq(b.read()), 'reads round-trip over the wire');
    // tamper: a wire commit whose payload does not match its claimed gid is rejected
    const bad = a.delta(new DistributedReplica(dt, 'C').ancestryGids());
    bad[0].payload = dt === orset ? { type: 'add', tag: 'A#0', el: 'X' } : { type: 'ins', id: 1, el: 'X', anchorId: null };
    assert.throws(() => new DistributedReplica(dt, 'C').ingest(bad), /content-address mismatch/);
  }
});

// ------------------------------------------------ (c) certified state GC
test('embedRGA certified GC: refuses without the certificate, fires with it, reads unchanged', () => {
  const a = new DistributedReplica(compactibleEmbedRGA, 'A'), b = new DistributedReplica(compactibleEmbedRGA, 'B');
  a.register('B'); b.register('A'); // roster: A knows B is a room member
  a.commit({ type: 'ins', id: 50, el: 'a', anchorId: null });
  a.commit({ type: 'ins', id: 80, el: 'b', anchorId: null });
  const r0 = a.compactStable();
  assert.equal(r0.compacted, false, 'A refuses: not heard from B');
  assert.deepEqual(r0.missing, ['B']);
  syncReplicas(a, b); // B learns A's ops; A still has heard no B-authored op
  assert.equal(a.compactStable().compacted, false, 'still refuses: B has authored nothing A absorbed');
  b.commit({ type: 'ins', id: 120, el: 'c', anchorId: null });
  syncReplicas(a, b); // NOW A has heard from B
  const before = a.read().join(''), beforeSymbols = a.symbolCount();
  const r1 = a.compactStable();
  assert.equal(r1.compacted, true, 'A fires once heard from everyone');
  assert.ok(r1.stats.symbolsAfter < r1.stats.symbolsBefore, 'compaction shrinks the coordinate cost');
  assert.equal(a.read().join(''), before, 'certified compaction preserves reads');
  assert.ok(a.symbolCount() < beforeSymbols, 'live state size dropped');
  assert.equal(a.epoch, 1, 'a new epoch opened');
});

test('orset gets everything EXCEPT state compaction (parametric refusal)', () => {
  const a = new DistributedReplica(orset, 'A'), b = new DistributedReplica(orset, 'B');
  a.register('B'); b.register('A');
  a.commit({ type: 'add', tag: 'A#0', el: 'x' });
  b.commit({ type: 'add', tag: 'B#0', el: 'y' });
  syncReplicas(a, b);
  const r = a.compactStable();
  assert.equal(r.compacted, false, 'orset refuses state compaction: it has no compact/remapState');
  assert.match(r.reason, /does not support state compaction/);
  assert.equal(eq(a.read()), eq(['x', 'y']), 'but convergence and reads are unaffected');
});

// ------------------------------------------------------------- (d) commit GC
test('commit GC prunes below the pairwise-meet horizon, reads preserved (embed + orset)', () => {
  for (const dt of [compactibleEmbedRGA, orset]) {
    const a = new DistributedReplica(dt, 'A'), b = new DistributedReplica(dt, 'B');
    a.register('B'); b.register('A');
    const ins = (id, el, anchor) => dt === orset
      ? { type: 'add', tag: 'x#' + id, el } : { type: 'ins', id, el, anchorId: anchor };
    a.commit(ins(1, 'p', null)); // shared prefix p
    syncReplicas(a, b);          // both hold p (root -> p)
    a.commit(ins(2, 'q', dt === orset ? null : 1)); // A branch: q
    b.commit(ins(3, 'r', dt === orset ? null : 1)); // B branch: r (concurrent)
    syncReplicas(a, b);          // merge; both converge past the meet (p)
    const readBefore = eq(a.read());
    const sizeBefore = a.dag.size;
    const g = a.gc();            // prune history strictly below the meet horizon
    assert.ok(g.dropped > 0, `${dt === orset ? 'orset' : 'embed'}: gc pruned commits below the horizon`);
    assert.ok(a.dag.size < sizeBefore, 'the store shrank');
    assert.equal(eq(a.read()), readBefore, 'reads preserved across commit GC');
    // the session keeps going after GC: one more op each, re-converge, still equal
    a.commit(ins(4, 's', null)); b.commit(ins(5, 't', null));
    syncReplicas(a, b);
    assert.equal(eq(a.read()), eq(b.read()), 'post-GC editing still converges');
  }
});

// -------------------------------- (e) cross-epoch merge = the certificate join
test('cross-epoch merge TRANSLATES (reads == twin), does not throw', () => {
  const a = new DistributedReplica(compactibleEmbedRGA, 'A'), b = new DistributedReplica(compactibleEmbedRGA, 'B');
  const ta = new DistributedReplica(compactibleEmbedRGA, 'A'), tb = new DistributedReplica(compactibleEmbedRGA, 'B'); // never-compacted twin
  a.register('B'); b.register('A');
  for (const r of [a, ta]) { r.commit({ type: 'ins', id: 50, el: 'a', anchorId: null }); r.commit({ type: 'ins', id: 80, el: 'b', anchorId: null }); }
  syncReplicas(a, b); syncReplicas(ta, tb);
  b.commit({ type: 'ins', id: 120, el: 'c', anchorId: null }); tb.commit({ type: 'ins', id: 120, el: 'c', anchorId: null });
  syncReplicas(a, b); syncReplicas(ta, tb); // converge at epoch 0
  // A compacts alone -> A at epoch 1, B still at epoch 0 (a divergent-epoch pair)
  assert.equal(a.compactStable().compacted, true);
  assert.equal(a.epoch, 1); assert.equal(b.epoch, 0);
  // B authors a straggler, ingests A's epoch-1 head, then MERGES ACROSS the epoch:
  // the certificate-determined join (coordinate translation).
  b.commit({ type: 'ins', id: 150, el: 'd', anchorId: null }); tb.commit({ type: 'ins', id: 150, el: 'd', anchorId: null });
  b.ingest(a.delta(b.ancestryGids()));
  assert.doesNotThrow(() => b.mergeWithGid(a.headGid), 'cross-epoch merge translates coordinates');
  syncReplicas(ta, tb);
  assert.equal(b.read().join(''), tb.read().join(''), 'the merged read equals the never-compacted twin');
  assert.equal(b.read().join(''), 'dcba', 'hand-derived: [150,120,80,50] = d,c,b,a');
});
