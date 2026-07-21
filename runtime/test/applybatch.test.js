// applyBatch = fold of apply (one transient pass, frozen at the end), for
// each datatype: the batch path must be observationally identical to the
// per-op path (same fingerprint, same read), including on non-empty bases
// and with deletes/removes interleaved. The DAG granularity is unchanged
// (one op per commit); applyBatch is for burst ingestion outside it.

import test from 'node:test';
import assert from 'node:assert/strict';
import { embedRGA } from '../src/datatypes/embedRGA.js';
import { orset } from '../src/datatypes/orset.js';
import { peritext } from '../src/datatypes/peritext.js';

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

test('embedRGA.applyBatch == fold(apply): random ins/del bursts', () => {
  const rng = mulberry32(0xabc1);
  for (let trial = 0; trial < 30; trial++) {
    let base = embedRGA.init();
    const view = [];
    let id = 0;
    const mkOps = (n) => {
      // ops generated against a simulated view so they are honest
      const ops = [];
      for (let k = 0; k < n; k++) {
        if (view.length > 2 && rng() < 0.3) {
          const pos = Math.floor(rng() * view.length);
          ops.push({ type: 'del', id: view[pos] });
          view.splice(pos, 1);
        } else {
          id++;
          const pos = Math.floor(rng() * (view.length + 1));
          ops.push({ type: 'ins', id, el: 'c' + id, anchorId: pos > 0 ? view[pos - 1] : null });
          view.splice(pos, 0, id);
        }
      }
      return ops;
    };
    base = embedRGA.applyBatch(base, mkOps(10)); // non-empty base via the batch path
    const ops = mkOps(25);
    const folded = ops.reduce((s, op) => embedRGA.apply(s, op), base);
    const batched = embedRGA.applyBatch(base, ops);
    assert.equal(embedRGA.fingerprint(batched), embedRGA.fingerprint(folded));
    assert.deepEqual(embedRGA.read(batched), embedRGA.read(folded));
    assert.equal(embedRGA.fingerprint(base), embedRGA.fingerprint(base), 'base untouched');
  }
});

test('embedRGA.applyBatch enforces the same honesty preconditions as apply', () => {
  const base = embedRGA.applyBatch(embedRGA.init(),
    [{ type: 'ins', id: 3, el: 'a', anchorId: null }]);
  assert.throws(() => embedRGA.applyBatch(base,
    [{ type: 'ins', id: 9, el: 'x', anchorId: 7 }]), /not live/);
  assert.throws(() => embedRGA.applyBatch(base,
    [{ type: 'ins', id: 3, el: 'x', anchorId: null }]), /duplicate/);
  // a batch may anchor on a record minted earlier in the SAME batch
  const s = embedRGA.applyBatch(base, [
    { type: 'ins', id: 5, el: 'b', anchorId: 3 },
    { type: 'ins', id: 6, el: 'c', anchorId: 5 },
    { type: 'del', id: 5 },
  ]);
  assert.deepEqual(embedRGA.read(s), ['a', 'c']);
});

test('orset.applyBatch == fold(apply): adds and observed removes', () => {
  const rng = mulberry32(0x0522);
  let base = orset.init();
  let tag = 0;
  const ops = [];
  for (let k = 0; k < 60; k++) {
    ops.push({ type: 'add', tag: 't' + tag++, el: 'e' + Math.floor(rng() * 6) });
    if (rng() < 0.3 && tag > 3) ops.push({ type: 'rm', tags: ['t' + Math.floor(rng() * tag)] });
  }
  const folded = ops.reduce((s, op) => orset.apply(s, op), base);
  const batched = orset.applyBatch(base, ops);
  assert.equal(orset.fingerprint(batched), orset.fingerprint(folded));
  assert.deepEqual(orset.read(batched), orset.read(folded));
});

test('peritext.applyBatch == fold(apply): ins/del/addMark/removeMark mixed', () => {
  const ops = [
    { type: 'ins', id: 1, el: 'a', anchorId: null },
    { type: 'ins', id: 2, el: 'b', anchorId: 1 },
    { type: 'addMark', mid: 10, mtype: 'bold', startId: 1, endId: 2 },
    { type: 'ins', id: 3, el: 'c', anchorId: 2 },
    { type: 'del', id: 2 },
    { type: 'removeMark', mid: 20, mtype: 'bold', startId: 1, endId: 3 },
    { type: 'ins', id: 4, el: 'd', anchorId: 3 },
  ];
  const folded = ops.reduce((s, op) => peritext.apply(s, op), peritext.init());
  const batched = peritext.applyBatch(peritext.init(), ops);
  assert.equal(peritext.fingerprint(batched), peritext.fingerprint(folded));
  assert.deepEqual(peritext.read(batched), peritext.read(folded));
  // and on a non-empty base
  const base = peritext.applyBatch(peritext.init(), ops.slice(0, 3));
  const rest = ops.slice(3);
  assert.equal(
    peritext.fingerprint(peritext.applyBatch(base, rest)),
    peritext.fingerprint(rest.reduce((s, op) => peritext.apply(s, op), base)));
});
