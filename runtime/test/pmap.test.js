// PMap (persistent HAMT) unit tests: randomized equivalence vs Map,
// structural-sharing sanity, transient freeze correctness, collision-node
// coverage (real FNV-1a collisions found by birthday search), and the
// deterministic sorted iteration policy.

import test from 'node:test';
import assert from 'node:assert/strict';
import { PMap, PSet, hashKey, cmpKeys } from '../src/pmap.js';

function mulberry32(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const sortedOf = (map) => [...map.entries()].sort((a, b) => cmpKeys(a[0], b[0]));

const assertEquiv = (pm, m, label) => {
  assert.equal(pm.size, m.size, `${label}: size`);
  assert.deepEqual(pm.entries(), sortedOf(m), `${label}: entries`);
};

test('randomized equivalence vs Map: mixed set/delete/get, number keys', () => {
  const rng = mulberry32(0xbeef);
  let pm = PMap.empty();
  const m = new Map();
  for (let batch = 0; batch < 40; batch++) {
    for (let i = 0; i < 100; i++) {
      const k = Math.floor(rng() * 500);
      if (rng() < 0.35) { pm = pm.delete(k); m.delete(k); }
      else { const v = 'v' + Math.floor(rng() * 1000); pm = pm.set(k, v); m.set(k, v); }
      assert.equal(pm.get(k), m.get(k));
      assert.equal(pm.has(k), m.has(k));
    }
    assertEquiv(pm, m, `batch ${batch}`);
  }
});

test('randomized equivalence vs Map: string keys, delete to empty and rebuild', () => {
  const rng = mulberry32(0x51e57);
  let pm = PMap.empty();
  const m = new Map();
  const keys = Array.from({ length: 300 }, (_, i) => 'p' + (i % 7) + '#' + i);
  for (let round = 0; round < 30; round++) {
    for (let i = 0; i < 80; i++) {
      const k = keys[Math.floor(rng() * keys.length)];
      if (rng() < 0.45) { pm = pm.delete(k); m.delete(k); }
      else { pm = pm.set(k, round * 1000 + i); m.set(k, round * 1000 + i); }
    }
    assertEquiv(pm, m, `round ${round}`);
  }
  for (const k of [...m.keys()]) { pm = pm.delete(k); m.delete(k); }
  assert.equal(pm.size, 0);
  assert.deepEqual(pm.entries(), []);
  pm = pm.set('x', 1);
  assert.deepEqual(pm.entries(), [['x', 1]]);
});

test('large map: 50k sequential integer keys (deep trie), spot equivalence', () => {
  let t = PMap.empty().begin();
  for (let i = 1; i <= 50000; i++) t.set(i, i * 3);
  const pm = t.freeze();
  assert.equal(pm.size, 50000);
  for (const k of [1, 2, 31, 32, 1024, 49999, 50000]) assert.equal(pm.get(k), k * 3);
  assert.equal(pm.get(50001), undefined);
  const ks = pm.keys();
  assert.equal(ks[0], 1); assert.equal(ks[49999], 50000); // sorted ascending
  let pm2 = pm;
  for (let i = 1; i <= 50000; i += 2) pm2 = pm2.delete(i);
  assert.equal(pm2.size, 25000);
  assert.equal(pm2.has(2), true); assert.equal(pm2.has(3), false);
  assert.equal(pm.size, 50000, 'original untouched');
});

test('structural sharing: the old root is unchanged after set/delete', () => {
  let pm = PMap.empty();
  for (let i = 0; i < 200; i++) pm = pm.set(i, 'v' + i);
  const snapshot = pm.entries();
  const pm2 = pm.set(42, 'CHANGED').set(999, 'NEW');
  const pm3 = pm.delete(7);
  assert.deepEqual(pm.entries(), snapshot, 'old map unchanged by set');
  assert.equal(pm.get(42), 'v42');
  assert.equal(pm.has(999), false);
  assert.equal(pm.has(7), true, 'old map unchanged by delete');
  assert.equal(pm2.get(42), 'CHANGED');
  assert.equal(pm2.get(999), 'NEW');
  assert.equal(pm3.has(7), false);
  // no-op set/delete return the SAME map (identity, not just equality)
  assert.equal(pm.set(42, 'v42'), pm);
  assert.equal(pm.delete(31337), pm);
});

test('transient: freeze correctness, source map untouched, use-after-freeze throws', () => {
  let pm = PMap.empty();
  for (let i = 0; i < 100; i++) pm = pm.set(i, i);
  const before = pm.entries();
  const t = pm.begin();
  for (let i = 50; i < 150; i++) t.set(i, i * 10);
  for (let i = 0; i < 25; i++) t.delete(i);
  assert.equal(t.get(60), 600); assert.equal(t.has(10), false);
  const frozen = t.freeze();
  assert.deepEqual(pm.entries(), before, 'source of the transient untouched');
  assert.equal(frozen.size, 125);
  assert.equal(frozen.get(49), 49);
  assert.equal(frozen.get(149), 1490);
  assert.throws(() => t.set(1, 1), /freeze/);
  // frozen result is a normal persistent map
  const frozen2 = frozen.set(200, 'z');
  assert.equal(frozen.has(200), false);
  assert.equal(frozen2.get(200), 'z');
});

test('transient equivalence vs Map under a random mixed batch', () => {
  const rng = mulberry32(0xf00d);
  const t = PMap.empty().begin();
  const m = new Map();
  for (let i = 0; i < 5000; i++) {
    const k = rng() < 0.5 ? Math.floor(rng() * 800) : 's' + Math.floor(rng() * 800);
    if (rng() < 0.3) { t.delete(k); m.delete(k); }
    else { t.set(k, i); m.set(k, i); }
  }
  assertEquiv(t.freeze(), m, 'transient batch');
});

test('collision nodes: real 32-bit hash collisions behave like distinct keys', () => {
  // birthday-search a genuine hashKey collision among string keys
  const seen = new Map();
  let a = null, b = null;
  for (let i = 0; i < 300000; i++) {
    const k = 'k' + i;
    const h = hashKey(k);
    if (seen.has(h)) { a = seen.get(h); b = k; break; }
    seen.set(h, k);
  }
  assert.ok(a !== null, 'expected a 32-bit collision within 300k keys');
  assert.equal(hashKey(a), hashKey(b));
  let pm = PMap.empty().set(a, 'A').set(b, 'B');
  assert.equal(pm.get(a), 'A'); assert.equal(pm.get(b), 'B');
  assert.equal(pm.size, 2);
  pm = pm.set(a, 'A2');
  assert.equal(pm.get(a), 'A2'); assert.equal(pm.get(b), 'B');
  const del = pm.delete(a);
  assert.equal(del.has(a), false); assert.equal(del.get(b), 'B');
  assert.equal(del.size, 1);
  assert.equal(pm.get(a), 'A2', 'persistence across collision delete');
  // and through a transient
  const t = PMap.empty().begin();
  t.set(a, 1); t.set(b, 2); t.delete(a);
  const f = t.freeze();
  assert.deepEqual(f.entries(), [[b, 2]]);
});

test('iteration policy: sorted, insertion-order independent, Map/Set interop', () => {
  const ks = [17, 3, 250000, 42, 1, 99];
  let up = PMap.empty(), down = PMap.empty();
  for (const k of ks) up = up.set(k, 'v' + k);
  for (const k of [...ks].reverse()) down = down.set(k, 'v' + k);
  assert.deepEqual(up.entries(), down.entries(), 'same set => same iteration');
  assert.deepEqual(up.keys(), [1, 3, 17, 42, 99, 250000]);
  assert.deepEqual([...up], up.entries(), 'Symbol.iterator = sorted entries');
  assert.deepEqual([...new Map(up).keys()].sort((x, y) => x - y), up.keys());
  const mixed = PMap.empty().set('b', 1).set(2, 2).set('a', 3).set(1, 4);
  assert.deepEqual(mixed.keys(), [1, 2, 'a', 'b'], 'numbers before strings');
  const fe = [];
  mixed.forEach((v, k) => fe.push([k, v]));
  assert.deepEqual(fe, mixed.entries().map(([k, v]) => [k, v]), 'forEach(v, k) order');
});

test('PSet: persistent add/delete, sorted iteration, transient, from()', () => {
  let s = PSet.empty();
  s = s.add(5).add(2).add(9).add(2);
  assert.equal(s.size, 3);
  assert.ok(s.has(9) && !s.has(4));
  assert.deepEqual([...s], [2, 5, 9]);
  const s2 = s.delete(5);
  assert.deepEqual([...s2], [2, 9]);
  assert.deepEqual([...s], [2, 5, 9], 'old set unchanged');
  assert.equal(s.add(5), s, 'no-op add returns the same set');
  const t = s.begin();
  t.add(100); t.delete(2);
  const f = t.freeze();
  assert.deepEqual([...f], [5, 9, 100]);
  assert.deepEqual([...s], [2, 5, 9], 'source unchanged by transient');
  assert.deepEqual([...PSet.from([3, 1, 2, 1])], [1, 2, 3]);
  assert.deepEqual([...new Set(f.values())], [5, 9, 100], 'Set interop');
});
