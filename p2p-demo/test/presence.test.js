// Presence registry tests (task #107): the ephemeral off-DAG peer-awareness
// layer. Deterministic (the test supplies `now`, no wall clock). PASS+FAIL
// shaped: each positive is pinned by the degenerate it must avoid (a stale peer
// lingering, a departed peer staying, a cursor read as a selection, an
// unstable/constant color).

import test from 'node:test';
import assert from 'node:assert/strict';
import { Presence, peerColor, presenceSpan } from '../src/presence.js';

test('update + list: peers are recorded, name-sorted, colored', () => {
  const p = new Presence();
  p.update('bob', { anchor: 3, focus: 3 }, 1000);
  p.update('alice', { anchor: 2, focus: 5 }, 1000);
  const names = p.list().map((x) => x.name);
  assert.deepEqual(names, ['alice', 'bob'], 'sorted by name, not insertion order');
  assert.equal(p.list()[0].color, peerColor('alice'), 'carries the stable per-peer color');
  // FAIL companion: not empty, and not insertion order.
  assert.notEqual(names.length, 0);
  assert.notDeepEqual(names, ['bob', 'alice']);
});

test('prune drops peers unheard past the ttl, keeps fresh ones', () => {
  const p = new Presence(5000);
  p.update('stale', { anchor: 0, focus: 0 }, 1000);
  p.update('fresh', { anchor: 1, focus: 1 }, 9000);
  p.prune(10000); // stale last seen 1000, 9000ms ago > 5000; fresh 1000ms ago
  const names = p.list().map((x) => x.name);
  assert.deepEqual(names, ['fresh'], 'only the fresh peer survives');
  // FAIL companion: without prune the stale peer would still be listed.
  const q = new Presence(5000);
  q.update('stale', { anchor: 0, focus: 0 }, 1000);
  q.update('fresh', { anchor: 1, focus: 1 }, 9000);
  assert.deepEqual(q.list().map((x) => x.name), ['fresh', 'stale']);
});

test('remove is an explicit departure', () => {
  const p = new Presence();
  p.update('gone', { anchor: 0, focus: 0 }, 1000);
  p.update('here', { anchor: 0, focus: 0 }, 1000);
  p.remove('gone');
  assert.deepEqual(p.list().map((x) => x.name), ['here']);
  assert.equal(p.list().length, 1); // FAIL companion: the departed peer is not still present
});

test('presenceSpan: a selection normalizes; a bare cursor is empty', () => {
  assert.deepEqual(presenceSpan({ anchor: 5, focus: 2 }), [2, 5], 'backward selection normalizes to [lo,hi)');
  const [lo, hi] = presenceSpan({ anchor: 3, focus: 3 });
  assert.equal(lo, hi, 'a bare cursor has an empty span');
  // FAIL companion: a real selection is NOT empty.
  const [a, b] = presenceSpan({ anchor: 2, focus: 5 });
  assert.notEqual(a, b);
});

test('peerColor is stable per name and distinguishes peers', () => {
  assert.equal(peerColor('alice'), peerColor('alice'), 'same name -> same color in every tab');
  assert.notEqual(peerColor('a'), peerColor('b'), 'different names -> different colors');
  assert.match(peerColor('x'), /^hsl\(/); // FAIL companion: a real hsl color, not a constant/empty
});
