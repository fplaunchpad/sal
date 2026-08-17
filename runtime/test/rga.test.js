import test from 'node:test';
import assert from 'node:assert/strict';

import { rga, rgaApplicable } from '../src/datatypes/rga.js';
import { embedRGA } from '../src/datatypes/embedRGA.js';
import { peritextRGA, peritextEmbedRGA, peritextSidedEmbedRGA } from '../src/datatypes/peritext.js';
import { Runtime } from '../src/runtime.js';
import { compactiblePeritextRGA } from '../src/compact-rga-peritext.js';

const ins = (id, el, anchorId = null) => ({ type: 'ins', id, el, anchorId });
const del = (id) => ({ type: 'del', id });

test('RGA mirrors the Lean add/remove SPOTs and rejects dishonest minting', () => {
  let s = rga.init();
  assert.equal(rgaApplicable(s, ins(1, 7)), true);
  s = rga.apply(s, ins(1, 7));
  assert.deepEqual(rga.read(s), [7]);
  s = rga.apply(s, del(1));
  assert.deepEqual(rga.read(s), []);
  assert.throws(() => rga.apply(rga.init(), ins(2, 'x', 42)), /not known/);
  assert.throws(() => rga.apply(rga.init(), del(7)), /before insertion/);
  assert.throws(() => rga.apply(rga.apply(rga.init(), ins(1, 'a')), ins(1, 'b')), /duplicate/);
  assert.throws(() => rga.apply(s, ins(1, 'again')), /duplicate|resurrection/);
});

test('optimized RGA tree traversal equals the Lean timestamp-fold order', () => {
  const ops = [ins(1, 'a'), ins(2, 'b', 1), ins(3, 'c', 2), ins(4, 'd', 1), ins(5, 'e', 2)];
  const s = ops.reduce((q, op) => rga.apply(q, op), rga.init());
  // Ascending timestamp fold with insert-after yields 1,4,2,5,3.
  assert.deepEqual(rga.readIds(s), [1, 4, 2, 5, 3]);
  const back = rga.decodeState(rga.encodeState(s));
  assert.equal(rga.fingerprint(back), rga.fingerprint(s));
  const bytes = rga.encodeSnapshot(s);
  assert.deepEqual(rga.read(rga.decodeSnapshot(bytes)), rga.read(s));
  assert.throws(() => rga.decodeSnapshot(bytes.subarray(0, bytes.length - 1)), /truncated|varint/);
  assert.throws(() => rga.decodeSnapshot(Uint8Array.from([...bytes, 0])), /trailing/);
});

test('RGA union merge converges and preserves tombstones', () => {
  const rt = new Runtime(rga), a = rt.replica('a'), b = rt.replica('b');
  a.commit(ins(1, 'a')); a.sync(b);
  a.commit(ins(2, 'x', 1)); b.commit(ins(3, 'y', 1));
  a.commit(del(2)); a.sync(b);
  assert.deepEqual(a.read(), b.read());
  assert.deepEqual(a.read(), ['a', 'y']);
});

test('RGA and EmbedRGA stay read-equivalent on randomized honest histories', () => {
  for (let seed = 1; seed <= 40; seed++) {
    let x = seed >>> 0, next = 0, a = rga.init(), b = embedRGA.init();
    const rnd = () => ((x = Math.imul(x ^ (x >>> 15), 1 | x) + 0x6d2b79f5 >>> 0) / 2 ** 32);
    for (let k = 0; k < 120; k++) {
      const ids = rga.readIds(a);
      let op;
      if (ids.length && rnd() < .3) op = del(ids[Math.floor(rnd() * ids.length)]);
      else {
        const pos = Math.floor(rnd() * (ids.length + 1));
        op = ins(++next, `c${next}`, pos ? ids[pos - 1] : null);
      }
      a = rga.apply(a, op); b = embedRGA.apply(b, op);
      assert.deepEqual(rga.read(a), embedRGA.read(b));
    }
  }
});

test('PeritextRGA matches both tombstone-free Peritext variants sequentially', () => {
  const dts = [peritextRGA, peritextEmbedRGA, peritextSidedEmbedRGA];
  const ops = [ins(1, 'a'), ins(2, 'b', 1),
    { type: 'addMark', mid: 10, mtype: 'bold', startId: 1, endId: 2 },
    del(1), ins(3, 'c', 2)];
  const reads = dts.map((dt) => ops.reduce((s, op) => dt.apply(s,
    op.type === 'ins' && dt.needsPrepare ? dt.prepare(s, op) : op), dt.init())).map((s, i) => dts[i].read(s));
  assert.deepEqual(reads[0], reads[1]);
  assert.deepEqual(reads[1], reads[2]);
  const snap = peritextRGA.decodeState(peritextRGA.encodeState(
    ops.reduce((s, op) => peritextRGA.apply(s, op), peritextRGA.init())));
  assert.deepEqual(peritextRGA.read(snap), reads[0]);
});

test('PeritextRGA state GC drops settled dead leaves but retains live ancestry', () => {
  const dt = compactiblePeritextRGA;
  let leaves = dt.init();
  for (const op of [ins(1, 'a'), ins(2, 'b'), del(1)]) leaves = dt.apply(leaves, op);
  const c1 = dt.compact(leaves, { settledIds: new Set([1, 2]), settledDelIds: new Set([1]) });
  assert.equal(c1.stats.recordsDropped, 1);
  assert.deepEqual(dt.read(c1.state).map((e) => e.char), ['b']);

  let spine = dt.init();
  for (const op of [ins(1, 'a'), ins(2, 'b', 1), del(1)]) spine = dt.apply(spine, op);
  const c2 = dt.compact(spine, { settledIds: new Set([1, 2]), settledDelIds: new Set([1]) });
  assert.equal(c2.stats.recordsDropped, 0, 'the live child still needs its dead anchor');
  assert.deepEqual(dt.read(c2.state).map((e) => e.char), ['b']);
});
