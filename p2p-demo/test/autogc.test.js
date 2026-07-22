// AUTO-GC policy tests: PASS+FAIL shaped around each guard of the predicate.

import test from 'node:test';
import assert from 'node:assert/strict';
import { shouldCompact, AUTOGC_DEFAULTS } from '../src/autogc.js';

const base = {
  symbols: 50000, visibleChars: 100, cutComplete: true, meetSize: 5,
  name: 'alice', roster: ['alice', 'bob'],
};

test('fires exactly when every guard holds', () => {
  assert.equal(shouldCompact(base), true, 'the reference case fires');

  // each guard, negated in isolation (FAIL companions):
  assert.equal(shouldCompact({ ...base, cutComplete: false }), false, 'incomplete cut blocks');
  assert.equal(shouldCompact({ ...base, meetSize: 0 }), false, 'empty meet blocks');
  assert.equal(shouldCompact({ ...base, symbols: AUTOGC_DEFAULTS.minSymbols }), false, 'below the floor blocks');
  assert.equal(shouldCompact({ ...base, symbols: 3100 }), false, 'ratio not met blocks (3100 < 32*100)');
  assert.equal(shouldCompact({ ...base, name: 'bob' }), false, 'only the leader fires');
});

test('the leader is the least rostered name, deterministically', () => {
  assert.equal(shouldCompact({ ...base, roster: ['zed', 'alice'] }), true, 'alice leads {alice, zed}');
  assert.equal(shouldCompact({ ...base, name: 'zed', roster: ['zed', 'alice'] }), false);
  // a solo peer is its own leader (the cut is trivially its own frontier)
  assert.equal(shouldCompact({ ...base, roster: ['alice'] }), true);
});

test('the ratio scales with the visible document', () => {
  // a big doc with proportionate coordinates does NOT fire (nothing bloated)
  assert.equal(shouldCompact({ ...base, symbols: 50000, visibleChars: 5000 }), false,
    '50k symbols over 5k chars is only 10x: healthy');
  // the same symbols over a small doc DOES (the bloat case)
  assert.equal(shouldCompact({ ...base, symbols: 50000, visibleChars: 100 }), true);
});

test('the adaptive floor stops re-firing against the compacted baseline', () => {
  // after an attempt left 5671 symbols, the same 5671 must NOT re-fire even
  // though it exceeds the fixed ratio (53x for a 106-char typing chain)
  const post = { ...base, symbols: 5671, visibleChars: 106, floorSymbols: 5671 };
  assert.equal(shouldCompact(post), false, 'no growth, no fire');
  // 1.5x growth past the floor fires again
  assert.equal(shouldCompact({ ...post, symbols: 8600 }), true, 'real growth fires');
  // FAIL companion: just under the growth factor still blocked
  assert.equal(shouldCompact({ ...post, symbols: 8500 }), false, '8500 < 1.5*5671');
});
