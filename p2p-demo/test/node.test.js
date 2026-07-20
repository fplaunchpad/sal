// Node unit tests: the demo's Node is now a thin adapter over the runtime's
// first-class DistributedReplica (task #108 folded the ad-hoc combination into
// the core, unifying the hash). These pin the DEMO surface: the SHA re-export is
// correct, the SHA-addressed wire sync converges, and certified compaction fires
// / refuses. The old FNV-vs-SHA cross-check against sync.js's Peer is GONE --
// wire and disk now share one hash, so there is no rival hash to cross-check
// against (core convergence-vs-orset parametricity lives in
// runtime/test/replica.test.js).

import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { Node } from '../src/node.js';
import { sha256hex } from '../src/hash.js';
import { compactibleEmbedRGA } from '../../runtime/src/compact.js';

const dt = compactibleEmbedRGA;

function mulberry32(seed) {
  let a = seed >>> 0;
  return () => { a = (a + 0x6d2b79f5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
}
const pick = (rng, xs) => xs[Math.floor(rng() * xs.length)];

/** One bidirectional sync round between two Nodes (test helper). */
function syncNodes(a, b) {
  const hasA = a.ancestryGids(), hasB = b.ancestryGids();
  const toB = a.delta(hasB), toA = b.delta(hasA);
  const aHead = a.headGid, bHead = b.headGid;
  b.ingest(toB); a.ingest(toA);
  b.mergeWithGid(aHead); a.mergeWithGid(bHead);
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

test('Node: content-address gate dedups and gates on the SHA', () => {
  const a = new Node(dt, 'A'), b = new Node(dt, 'B');
  a.commit({ type: 'ins', id: 1, el: 'h', anchorId: null });
  a.commit({ type: 'ins', id: 2, el: 'i', anchorId: 1 });
  const d = a.delta(b.ancestryGids());
  assert.equal(b.ingest(d), 2, 'B ingests two commits');
  assert.equal(b.ingest(d), 0, 'idempotent: re-ingest adds nothing (SHA dedup)');
  // tamper: a wire commit whose payload does not match its claimed gid is rejected
  const bad = a.delta(new Node(dt, 'C').ancestryGids());
  bad[0].payload = { type: 'ins', id: 1, el: 'X', anchorId: null };
  const c = new Node(dt, 'C');
  assert.throws(() => c.ingest(bad), /content-address mismatch/);
});

test('Node converges over the SHA-addressed wire (N-node linear fold)', () => {
  const rng = mulberry32(0xBEEF);
  const N = 3;
  const nodes = Array.from({ length: N }, (_, i) => new Node(dt, 'p' + i));
  let mint = 0;
  for (let round = 0; round < 20; round++) {
    for (let i = 0; i < N; i++) {
      const view = dt.readIds(nodes[i].head.state);
      if (view.length > 3 && rng() < 0.25) {
        nodes[i].commit({ type: 'del', id: pick(rng, view) });
      } else {
        const id = ++mint;
        const anchorId = view.length && rng() < 0.7 ? pick(rng, view) : null;
        nodes[i].commit({ type: 'ins', id, el: String.fromCharCode(97 + (id % 26)), anchorId });
      }
    }
    // linear fold into index 0 (criss-cross-free), then broadcast back
    for (let pass = 0; pass < 2; pass++) for (let k = 1; k < N; k++) syncNodes(nodes[0], nodes[k]);
    const nread = nodes.map((n) => n.read().join(''));
    for (let i = 1; i < N; i++) assert.equal(nread[i], nread[0], `round ${round}: Node p${i} diverged`);
    // content addressing is deterministic: same converged history -> same head SHA
    for (let i = 1; i < N; i++) assert.equal(nodes[i].headGid, nodes[0].headGid,
      `round ${round}: converged nodes must hold the identical head SHA`);
  }
  assert.equal(nodes[0].headGid.length, 40, 'commit ids are 40-hex SHA content ids');
});

test('Node.compactStable: refuses without a certificate, fires with one, reads unchanged', () => {
  // Big Lamport deltas (cross-replica gaps) so rank-renumbering visibly shrinks.
  const a = new Node(dt, 'A'), b = new Node(dt, 'B');
  a.register('B'); b.register('A'); // roster: A knows B is a room member
  a.commit({ type: 'ins', id: 50, el: 'a', anchorId: null });
  a.commit({ type: 'ins', id: 80, el: 'b', anchorId: null });
  // A knows B is a member but has heard NOTHING from B -> certificate absent
  const r0 = a.compactStable();
  assert.equal(r0.compacted, false, 'A refuses: not heard from B');
  assert.deepEqual(r0.missing, ['B']);
  syncNodes(a, b); // B learns A's ops; A still has heard no B-authored op
  const r0b = a.compactStable();
  assert.equal(r0b.compacted, false, 'still refuses: B has authored nothing A absorbed');
  assert.deepEqual(r0b.missing, ['B']);
  b.commit({ type: 'ins', id: 120, el: 'c', anchorId: null });
  syncNodes(a, b); // NOW A has heard from B
  const before = a.read().join('');
  const beforeSymbols = a.symbolCount();
  const r1 = a.compactStable();
  assert.equal(r1.compacted, true, 'A fires once heard from everyone');
  assert.ok(r1.stats.symbolsAfter < r1.stats.symbolsBefore, 'compaction shrinks the coordinate cost');
  assert.equal(a.read().join(''), before, 'certified compaction preserves reads');
  assert.ok(a.symbolCount() < beforeSymbols, 'live state size dropped');
  assert.equal(a.epoch, 1, 'a new epoch opened');
});
