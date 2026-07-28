// The core content hash (src/hash.js): the pure-JS SHA-256 is
// correct bit-for-bit vs node:crypto (so the runtime does not rest on a
// hand-rolled hash being merely plausible), stableStringify is order-invariant,
// and commitContentId mints the Merkle-DAG commit id every content-addressed
// store (the wire Peer, the DistributedReplica, git persistence) agrees on.

import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { sha256hex, stableStringify, contentId, commitContentId } from '../src/hash.js';

function mulberry32(seed) {
  let a = seed >>> 0;
  return () => { a = (a + 0x6d2b79f5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
}

test('sha256hex matches node:crypto (NIST vectors + randomized)', () => {
  const crypt = (s) => createHash('sha256').update(s, 'utf8').digest('hex');
  assert.equal(sha256hex(''), 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855');
  assert.equal(sha256hex('abc'), 'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad');
  const rng = mulberry32(7);
  for (let i = 0; i < 200; i++) {
    let s = '';
    const len = Math.floor(rng() * 300);
    for (let j = 0; j < len; j++) s += String.fromCharCode(32 + Math.floor(rng() * 90));
    assert.equal(sha256hex(s), crypt(s), `mismatch on random string #${i}`);
  }
});

test('stableStringify is key-order invariant (the content-address must not depend on build order)', () => {
  assert.equal(stableStringify({ a: 1, b: 2 }), stableStringify({ b: 2, a: 1 }));
  assert.equal(contentId({ x: [1, { p: 2, q: 3 }] }), contentId({ x: [1, { q: 3, p: 2 }] }));
  assert.notEqual(contentId({ a: 1 }), contentId({ a: 2 }), 'distinct content -> distinct id');
});

test('commitContentId: Merkle DAG, merge is parent-order-independent, root is fixed', () => {
  const fingerprint = (s) => JSON.stringify(s);
  const root = commitContentId({ parents: [], op: null, state: null }, []);
  assert.equal(root, commitContentId({ parents: [], op: null, state: null }, []), 'root id is deterministic');

  const authored = { parents: ['root'], op: { replica: 'A', seq: 0, payload: { k: 1 } }, state: null };
  const idA = commitContentId(authored, [root]);
  assert.equal(idA, commitContentId(authored, [root]), 'authored id is deterministic');
  assert.notEqual(idA, root);

  // merge(a,b) == merge(b,a): the SORTED-parent hash the criss-cross argument needs
  const m1 = commitContentId({ parents: ['x', 'y'], op: null, state: null }, ['x', 'y']);
  const m2 = commitContentId({ parents: ['y', 'x'], op: null, state: null }, ['y', 'x']);
  assert.equal(m1, m2, 'merge commit id is independent of parent order');

  // compaction commit folds in a state fingerprint; needs the fingerprint fn
  const comp = { parents: ['p'], op: null, state: { live: [1, 2] } };
  const idC = commitContentId(comp, [idA], { fingerprint });
  assert.equal(idC, commitContentId(comp, [idA], { fingerprint }));
  assert.throws(() => commitContentId(comp, [idA]), /needs a fingerprint/);

  // pluggable hash: swapping the digest changes the id but keeps determinism
  const viaPlug = commitContentId(authored, [root], { hash: (o) => 'X' + JSON.stringify(o).length });
  assert.match(viaPlug, /^X\d+$/);
  assert.notEqual(viaPlug, idA);
});
