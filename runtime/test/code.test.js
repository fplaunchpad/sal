// The delta-code layer: Lean-pinned codeword values, executable
// code-parametricity (reads invariant under the code), and the cost gap
// that motivates the Elias-delta default.
//
// CODEWORD PROVENANCE: the dEnc pins below are the kernel-checked
// examples in Sal/MRDTs/Instances/RGAKernel/BinaryCode.lean
// (eliasDeltaCode), with List Bool mapped false->'0', true->'1', MSB
// first. If the port disagrees with a pin, the port is wrong.

import test from 'node:test';
import assert from 'node:assert/strict';
import { Runtime } from '../src/runtime.js';
import { CrissCrossError } from '../src/lca.js';
import {
  makeEmbedRGA, unaryCode, eliasDeltaCode, binEnc, dEnc,
} from '../src/datatypes/embedRGA.js';

test('dEnc matches the kernel-checked Lean values', () => {
  assert.equal(dEnc(1), '0');
  assert.equal(dEnc(2), '1000');
  assert.equal(dEnc(3), '1001');
  assert.equal(dEnc(4), '10100');
  assert.equal(dEnc(8), '11000000');
  // the length identities kernel-checked alongside them
  assert.equal(dEnc(2).length, 4); assert.equal(binEnc(2).length, 3);
  assert.equal(dEnc(8).length, 8); assert.equal(binEnc(8).length, 7);
  assert.equal(dEnc(16).length, binEnc(16).length);
  assert.equal(dEnc(32).length, 10); assert.equal(binEnc(32).length, 11);
  assert.equal(dEnc(1024).length, 17); assert.equal(binEnc(1024).length, 21);
  // |dEnc d| = size d + 2*size(size d) - 2 (dEnc_length), spot-checked
  const size = (n) => n.toString(2).length;
  for (const d of [1, 2, 5, 9, 33, 700, 4097]) {
    assert.equal(dEnc(d).length, size(d) + 2 * size(size(d)) - 2);
  }
});

const CODES = [unaryCode, eliasDeltaCode];

// Directed scenarios as replica scripts: [replica, 'commit', payload] or
// [replica, 'sync', otherReplica]; expected read on every replica at the end.
const DIRECTED = [
  ['L1 delete-reorder', 1, [
    [0, 'commit', { type: 'ins', id: 1, el: 'a', anchorId: null }],
    [0, 'commit', { type: 'ins', id: 2, el: 'b', anchorId: null }],
    [0, 'commit', { type: 'ins', id: 3, el: 'c', anchorId: 1 }],
    [0, 'commit', { type: 'del', id: 1 }],
  ], ['b', 'c']],
  ['fooling-pair world 1', 2, [
    [0, 'commit', { type: 'ins', id: 1, el: 1, anchorId: null }],
    [1, 'sync', 0],
    [0, 'commit', { type: 'ins', id: 5, el: 5, anchorId: 1 }],
    [0, 'commit', { type: 'del', id: 1 }],
    [1, 'commit', { type: 'ins', id: 2, el: 2, anchorId: null }],
    [0, 'sync', 1],
  ], [2, 5]],
  ['fooling-pair world 2', 2, [
    [0, 'commit', { type: 'ins', id: 1, el: 1, anchorId: null }],
    [1, 'sync', 0],
    [0, 'commit', { type: 'del', id: 1 }],
    [0, 'commit', { type: 'ins', id: 5, el: 5, anchorId: null }],
    [1, 'commit', { type: 'ins', id: 2, el: 2, anchorId: null }],
    [0, 'sync', 1],
  ], [5, 2]],
];

test('code-invariance: directed fixtures pass under BOTH codes unchanged', () => {
  for (const code of CODES) {
    const DT = makeEmbedRGA(code);
    for (const [name, nRep, script, expect] of DIRECTED) {
      const rt = new Runtime(DT);
      const reps = Array.from({ length: nRep }, (_, i) => rt.replica('r' + i));
      for (const [r, kind, arg] of script) {
        if (kind === 'commit') reps[r].commit(arg); else reps[r].sync(reps[arg]);
      }
      for (const rep of reps) {
        assert.deepEqual(rep.read(), expect, `${name} under ${code.name}`);
      }
    }
  }
});

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
const pick = (rng, xs) => xs[Math.floor(rng() * xs.length)];

test('code-invariance: 100 randomized head-sync runs read identically under both codes', () => {
  for (let seed = 0; seed < 100; seed++) {
    const rng = mulberry32(seed * 2654435761 + 5);
    const nRep = 3 + (seed % 2);
    const nSteps = 25 + Math.floor(rng() * 16);
    const twins = CODES.map((c) => new Runtime(makeEmbedRGA(c)));
    const reps = twins.map((rt) =>
      Array.from({ length: nRep }, (_, i) => rt.replica('r' + i)));
    let next = 1;
    for (let step = 0; step < nSteps; step++) {
      const r = Math.floor(rng() * nRep);
      if (rng() < 0.35) {
        const j = Math.floor(rng() * nRep);
        if (j !== r) {
          // identical DAG shapes => the criss-cross verdict must agree too
          const errs = twins.map((_, t) => {
            try { reps[t][r].sync(reps[t][j]); return false; }
            catch (e) { if (e instanceof CrissCrossError) return true; throw e; }
          });
          assert.equal(errs[0], errs[1], `criss-cross verdict @${step}`);
        }
      } else {
        const doc = reps[0][r].read(); // elements are their own ids
        const op = doc.length > 0 && rng() < 0.3
          ? { type: 'del', id: pick(rng, doc) }
          : { type: 'ins', id: next++, el: next - 1,
              anchorId: doc.length > 0 && rng() < 0.6 ? pick(rng, doc) : null };
        for (const rr of reps) rr[r].commit(op);
      }
      for (let i = 0; i < nRep; i++) {
        assert.deepEqual(reps[1][i].read(), reps[0][i].read(), `read @${step} r${i}`);
      }
    }
  }
});

test('cost gap: growing cross-replica Lamport deltas, elias beats unary substantially', (t) => {
  // Two replicas prepend at the top (root anchor) in interleaved bursts
  // with periodic syncs: the delta of insert i is its full Lamport ts, so
  // unary coordinates grow LINEARLY with global op count while eliasDelta
  // grows as log2 + O(log log).
  const totals = CODES.map((code) => {
    const DT = makeEmbedRGA(code);
    const rt = new Runtime(DT);
    const a = rt.replica('A'), b = rt.replica('B');
    for (let i = 1; i <= 200; i++) {
      (i % 2 === 0 ? a : b).commit({ type: 'ins', id: i, el: i, anchorId: null });
      if (i % 20 === 0) a.sync(b);
    }
    a.sync(b);
    assert.equal(a.read().length, 200);
    return DT.symbolCount(a.head.state);
  });
  const [unaryTotal, eliasTotal] = totals;
  t.diagnostic(`total coordinate symbols over 200 ops: unary=${unaryTotal} eliasDelta=${eliasTotal} (factor ${(unaryTotal / eliasTotal).toFixed(1)}x)`);
  assert.ok(eliasTotal * 4 < unaryTotal,
    `expected a substantial gap: unary=${unaryTotal} elias=${eliasTotal}`);
});
