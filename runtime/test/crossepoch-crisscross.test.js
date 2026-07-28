// CRISS-CROSS x EPOCH (the doubly-hard corner). A merge whose MCA antichain is
// a criss-cross AND spans epochs (one member below a compaction, one at/after
// it) is lifted DOWN to a common frame (EPOCH0, via the epoch inverse maps that
// coordState makes available for peritext) and folded there, so it RESOLVES.
// Deferring here (throwing CrissCrossError), on a compacted doc under
// opportunistic merging, would leave peers permanently diverged and re-trigger
// the sync storm. This pins it: an opportunistic (criss-cross-inducing)
// peritext mesh with concurrent compaction converges, with ZERO unresolved
// deferrals.

import test from 'node:test';
import assert from 'node:assert/strict';
import { DistributedReplica } from '../src/replica.js';
import { compactiblePeritext } from '../src/compact-peritext.js';
import { embedRGA } from '../src/datatypes/embedRGA.js';

const mint = (k) => k * 1000 + 7;
const txt = (r) => r.read().map((e) => e.char).join('');
function mulberry32(a) { return () => { a |= 0; a = (a + 0x6d2b79f5) | 0; let t = Math.imul(a ^ (a >>> 15), 1 | a); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }

test('opportunistic peritext mesh + compaction converges, no unresolved deferrals', () => {
  const rng = mulberry32(0xC0FFEE);
  const pick = (xs) => xs[Math.floor(rng() * xs.length)];
  const N = 4;
  const reps = Array.from({ length: N }, (_, i) => new DistributedReplica(compactiblePeritext, 'p' + i));
  for (const r of reps) for (const s of reps) if (r !== s) r.register(s.name);
  let id = 0, deferred = 0;
  // seed shared history + tombstones so compaction has work
  const seed = [];
  for (let i = 0; i < 10; i++) { id++; seed.push({ type: 'ins', id: mint(id), el: 'abcdefghij'[i], anchorId: i === 0 ? null : mint(id - 1) }); }
  reps[0].commitBatch(seed);
  // OPPORTUNISTIC pairwise sync (ingest + mergeWithGid, order-dependent -> criss-crosses)
  const sync = (a, b) => {
    try { a.ingest(b.delta(a.ancestryGids())); a.mergeWithGid(b.headGid); }
    catch (e) { if (e.name === 'CrissCrossError' || /cross-epoch/.test(e.message)) deferred++; else throw e; }
  };
  for (const r of reps) sync(r, reps[0]);

  for (let round = 0; round < 60; round++) {
    for (const r of reps) {
      if (rng() < 0.6) { const live = embedRGA.readIds(r.head.state.text.shadow); id++; r.commit({ type: 'ins', id: mint(id), el: 'z', anchorId: live.length && rng() < 0.7 ? pick(live) : null }); }
      else { const live = embedRGA.readIds(r.head.state.text.shadow); if (live.length) r.commit({ type: 'del', id: pick(live) }); }
    }
    if (rng() < 0.2) { try { pick(reps).compactStable(); } catch {} } // ungated -> incomparable epochs
    for (let s = 0; s < 6; s++) { const a = pick(reps), b = pick(reps); if (a !== b) sync(a, b); }
  }
  // final: fully connect everyone (opportunistic), several passes
  for (let pass = 0; pass < 6; pass++) for (const a of reps) for (const b of reps) if (a !== b) sync(a, b);

  const reads = reps.map(txt);
  assert.equal(deferred, 0, `every merge RESOLVED (no criss-cross/cross-epoch deferrals), got ${deferred}`);
  for (let i = 1; i < N; i++) assert.equal(reads[i], reads[0], `p${i} converged`);
  assert.ok(reps.map((r) => r.headGid).every((h) => h === reps[0].headGid), 'identical head SHA');
});
