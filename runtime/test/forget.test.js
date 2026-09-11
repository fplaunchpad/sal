// FORGET a departed writer to unstall the certified GC. A peer that authored
// and then went dark stays registered conservatively (unregister keeps
// writers), so its frontier evidence PINS the stability cut at its last-synced
// position -- nothing typed since can be reclaimed. `forget` drops it from BOTH
// the roster and the conservative ever-authored summary, releasing the horizon. SOUNDNESS is the
// operator's to grant: a forgotten peer that returns must re-sync fresh, not
// merge a stale-head delta. PASS+FAIL shaped: the cut is capped WHILE the dark
// author is rostered, then GC fires AFTER the forget, reads preserved.

import test from 'node:test';
import assert from 'node:assert/strict';
import { DistributedReplica } from '../src/replica.js';
import { compactibleEmbedRGA } from '../src/compact.js';

test('unregister keeps a writer but drops a never-authored lurker', () => {
  const p = new DistributedReplica(compactibleEmbedRGA, 'P');
  p.register('L'); // a lurker that joined and never authored
  p.commit({ type: 'ins', id: 1, el: 'a', anchorId: null });
  assert.equal(p.unregister('L'), true, 'the lurker is dropped');
  assert.equal(p.unregister('P'), false, 'self is never dropped');
  // an author is NOT dropped by unregister (conservative)
  const q = new DistributedReplica(compactibleEmbedRGA, 'Q');
  q.commit({ type: 'ins', id: 2, el: 'b', anchorId: null });
  p.ingest(q.delta(p.ancestryGids()));
  p.mergeWithGid(q.headGid); // P now holds Q's authored op -> Q is an author here
  assert.equal(p.unregister('Q'), false, 'a writer stays registered');
});

test('forget lifts a departed author: the GC horizon advances, reads preserved', () => {
  const p = new DistributedReplica(compactibleEmbedRGA, 'P');
  p.commit({ type: 'ins', id: 10, el: 'a', anchorId: null });
  p.commit({ type: 'ins', id: 20, el: 'b', anchorId: 10 });
  p.commit({ type: 'ins', id: 30, el: 'c', anchorId: 20 });
  const q = new DistributedReplica(compactibleEmbedRGA, 'Q');
  q.commit({ type: 'ins', id: 99, el: 'z', anchorId: null });
  p.ingest(q.delta(p.ancestryGids()));
  p.mergeWithGid(q.headGid);       // P registered Q and holds its evidence
  // P keeps editing past Q's frozen frontier, then deletes a run
  for (let i = 40; i <= 60; i += 10) p.commit({ type: 'ins', id: i, el: 'x', anchorId: i - 10 });
  p.commit({ type: 'del', id: 20 });
  p.commit({ type: 'del', id: 40 });
  const readBefore = p.read().join('');

  // WITH Q registered but dark: the cut caps at Q's position, so the settled
  // deletes above it cannot be reclaimed -> compaction refuses
  const blocked = p.compactStable();
  assert.equal(blocked.compacted, false, 'a dark author caps the horizon: GC refused');
  assert.ok([...p.registered].includes('Q'), 'Q still rostered');

  // FORGET Q -> the horizon is released; GC fires and preserves reads
  assert.equal(p.forget('Q'), true, 'Q dropped from the roster');
  assert.equal(p.forget('Q'), false, 'idempotent: already gone');
  const g = p.compactStable();
  assert.equal(g.compacted, true, 'horizon advanced: GC reclaimed the settled deletes');
  assert.equal(p.read().join(''), readBefore, 'reads preserved across forget + GC');
});
