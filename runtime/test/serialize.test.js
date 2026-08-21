// Run-table serializer tests.
//
// EXPECTED ACCOUNTING VALUES ARE HAND-DERIVED from the run-table format.
// run_table_measure.py, never #eval'd from serialize.js: the
// directed totals below were printed by run_table_measure.account(t, False)
// on the same three trees, so a serialize.js bug shows as a mismatch against
// the independent Python model. Reference flipped-Elias-delta lengths
// (bits_D):  d: 1 2 3 4 5 6 7 8  ->  1 4 4 5 5 5 5 8.
//
// Suites:
//   1. bits_D pinned to the code length and to hand values;
//   2. directed accounting: TYPE (one run), D1 (mid-run concurrent insert,
//      three entries), DEL (delete mid-run, dead 'c' kept) -- totals and
//      every component matched against the Python model;
//   3. display identity: tableWalk == read, decode(encode(s)).read == read,
//      coordinate multiset preserved (losslessness), on the directed trees;
//   4. the metaBits reconciliation identity: the serialized metadata bit
//      count == account.total - rec_id - rec_off - hdr_poff (the recoverable
//      positional fields the model charges and the encoder drops);
//   5. size strictly below the as-shipped absolute-chain JSON on a typing
//      run and a delete-heavy state, ratios pinned;
//   6. coalesce + tail-attachment: a foreign run in a gap splits to three
//      entries, deleting it re-coalesces to one (canonical rebuild), tail
//      attachment asserted throughout;
//   7. PBT: 120 random histories with deletes and three-way merges;
//      decode(encode(s)).read() == s.read() and the walk == read on every
//      state (base, both branches, merged, evolved).

import test from 'node:test';
import assert from 'node:assert/strict';
import { embedRGA as D, eliasDeltaCode } from '../src/datatypes/embedRGA.js';
import {
  encode, decode, buildRunTable, accountingBits, tableWalk,
  bitsD, bitLength, roundTripReads,
} from '../src/serialize.js';

const readStr = (s) => D.read(s).join('');
const jsonBytes = (s) => Buffer.byteLength(D.fingerprint(s), 'utf8');

/** type a string as one anchor chain (delta 1 throughout): ids 1..n. */
function typing(str, anchor = null, id0 = 0) {
  let s = D.init(); let prev = anchor; let id = id0; const ids = [];
  for (const ch of str) { id++; s = D.apply(s, { type: 'ins', id, el: ch, anchorId: prev }); prev = id; ids.push(id); }
  return { s, ids };
}

// ---------------------------------------------------------------- 1. bits_D
test('bitsD == flipped-Elias-delta codeword length, and hand values', () => {
  for (let d = 1; d <= 300; d++) assert.equal(bitsD(d), eliasDeltaCode.enc(d).length);
  assert.deepEqual([1, 2, 3, 4, 5, 6, 7, 8].map(bitsD), [1, 4, 4, 5, 5, 5, 5, 8]);
  assert.equal(bitLength(0), 0); assert.equal(bitLength(3), 2); assert.equal(bitLength(8), 4);
});

// ------------------------------------------------- 2. directed accounting
test('TYPE abcdef: one fusible run, total 39 bits (Python model)', () => {
  const { s } = typing('abcdef');
  const a = accountingBits(buildRunTable(s));
  assert.equal(a.n_ent, 1); assert.equal(a.n_rec, 6); assert.equal(a.w, 1);
  assert.equal(a.rec_id, 6); assert.equal(a.rec_off, 24); assert.equal(a.hdr_len, 5);
  assert.equal(a.total, 39);
});

test('D1 mid-run concurrent insert (X after c): three entries, total 67', () => {
  const { s } = typing('abcdef');
  const d1 = D.apply(s, { type: 'ins', id: 7, el: 'X', anchorId: 3 });
  const a = accountingBits(buildRunTable(d1));
  assert.equal(a.n_ent, 3); assert.equal(a.n_rec, 7); assert.equal(a.w, 2);
  assert.equal(a.rec_id, 14); assert.equal(a.rec_off, 19); assert.equal(a.hdr_flag, 3);
  assert.equal(a.hdr_parent, 6); assert.equal(a.hdr_poff, 9);
  assert.equal(a.hdr_delta, 7); assert.equal(a.hdr_len, 9);
  assert.equal(a.total, 67);
  assert.equal(tableWalk(buildRunTable(d1)).join(''), 'abcXdef');
});

test('DEL delete mid-run (c): dead c kept as structure, total 51', () => {
  const { s } = typing('abcdef');
  const del = D.apply(s, { type: 'del', id: 3 });
  const t = buildRunTable(del);
  const a = accountingBits(t);
  assert.equal(a.n_ent, 3); assert.equal(a.n_rec, 5); assert.equal(a.w, 2);
  assert.equal(a.n_live_runs, 2); // one dead entry (the 'c' spine node)
  assert.equal(a.rec_id, 10); assert.equal(a.rec_off, 14); assert.equal(a.hdr_poff, 6);
  assert.equal(a.hdr_delta, 3); assert.equal(a.hdr_len, 9); assert.equal(a.total, 51);
  assert.equal(t.entries.filter((e) => !e.live).length, 1);
  assert.equal(readStr(del), 'abdef');
});

// ------------------------------------------------- 3. display identity
test('display identity on the directed trees: walk == read == decode-read', () => {
  const { s: base } = typing('abcdef');
  const trees = [
    base,
    D.apply(base, { type: 'ins', id: 7, el: 'X', anchorId: 3 }),
    D.apply(base, { type: 'del', id: 3 }),
    D.init(),
  ];
  for (const s of trees) {
    const t = buildRunTable(s);
    assert.equal(tableWalk(t).join(''), readStr(s));
    assert.equal(readStr(decode(encode(s))), readStr(s));
    roundTripReads(s);
  }
});

// ------------------------------------------------- 4. reconciliation identity
test('metaBits == account.total - rec_id - rec_off - hdr_poff (recoverable)', () => {
  const cases = [typing('abcdef').s,
    D.apply(typing('abcdef').s, { type: 'ins', id: 7, el: 'X', anchorId: 3 }),
    D.apply(typing('abcdef').s, { type: 'del', id: 3 })];
  for (const s of cases) {
    const a = accountingBits(buildRunTable(s));
    const buf = encode(s);
    assert.equal(buf.metaBits, a.total - a.rec_id - a.rec_off - a.hdr_poff);
  }
});

// ------------------------------------------------- 5. size vs absolute chain
test('serialized size strictly below as-shipped JSON: typing run >= 50x', () => {
  const { s } = typing('a'.repeat(500));
  const e = encode(s).length, j = jsonBytes(s);
  assert.ok(e < j);
  assert.ok(j / e > 50, `typing-run ratio ${(j / e).toFixed(1)} not > 50`);
  assert.equal(buildRunTable(s).entries.length, 1); // one long run
});

test('serialized size strictly below as-shipped JSON: delete-heavy >= 3x', () => {
  let s = D.init(); const view = []; let id = 0;
  for (let k = 0; k < 600; k++) { id++; const pos = view.length ? (id * 7) % view.length : 0; const anchor = pos > 0 ? view[pos - 1] : null; s = D.apply(s, { type: 'ins', id, el: 'x', anchorId: anchor }); view.splice(pos, 0, id); }
  for (let k = 0; k < 550; k++) { const pos = (k * 13) % view.length; s = D.apply(s, { type: 'del', id: view[pos] }); view.splice(pos, 1); }
  const e = encode(s).length, j = jsonBytes(s);
  assert.ok(e < j);
  assert.ok(j / e > 3, `delete-heavy ratio ${(j / e).toFixed(1)} not > 3`);
  roundTripReads(s);
});

// ------------------------------------------------- 6. coalesce + tail attach
test('coalesce: foreign run in a gap -> 3 entries, deleting it -> 1', () => {
  const { s } = typing('abcdef');
  // XYZ chain anchored after c (id 3), a foreign run landing in the gap
  let g = D.apply(s, { type: 'ins', id: 100, el: 'X', anchorId: 3 });
  g = D.apply(g, { type: 'ins', id: 101, el: 'Y', anchorId: 100 });
  g = D.apply(g, { type: 'ins', id: 102, el: 'Z', anchorId: 101 });
  assert.equal(readStr(g), 'abcXYZdef');
  assert.equal(buildRunTable(g).entries.length, 3); // [abc] [XYZ] [def]
  // delete the interloper: canonical rebuild re-coalesces to ONE run
  let back = g;
  for (const id of [100, 101, 102]) back = D.apply(back, { type: 'del', id });
  assert.equal(readStr(back), 'abcdef');
  const t = buildRunTable(back);
  assert.equal(t.entries.length, 1);
  assert.deepEqual(t.entries[0].members.map((m) => m.el), ['a', 'b', 'c', 'd', 'e', 'f']);
  // buildRunTable asserts tail-attachment internally; confirm it never threw
  for (const e of t.entries) if (e.parent >= 0) assert.equal(e.poff, t.entries[e.parent].members.length - 1);
});

// ------------------------------------------------- 7. PBT (merges + deletes)
function prng(seed) {
  let a = seed >>> 0;
  return () => { a |= 0; a = (a + 0x6d2b79f5) | 0; let t = Math.imul(a ^ (a >>> 15), 1 | a); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
}

function evolve(rng, s0, view0, nops, idBase) {
  let s = new Map(s0); const view = [...view0]; let id = idBase;
  for (let k = 0; k < nops; k++) {
    if (view.length > 3 && rng() < 0.3) {
      const pos = Math.floor(rng() * view.length);
      s = D.apply(s, { type: 'del', id: view[pos] }); view.splice(pos, 1);
    } else {
      id++; const pos = Math.floor(rng() * (view.length + 1));
      const anchor = pos > 0 ? view[pos - 1] : null;
      s = D.apply(s, { type: 'ins', id, el: String.fromCharCode(97 + Math.floor(rng() * 26)), anchorId: anchor });
      view.splice(pos, 0, id);
    }
  }
  return { s, view };
}

test('PBT: 120 random histories (deletes + 3-way merges) round-trip losslessly', () => {
  const rng = prng(0x5a1104);
  let states = 0;
  const gate = (s) => {
    const t = buildRunTable(s);
    assert.equal(tableWalk(t).join(''), readStr(s), 'walk != read');
    assert.equal(readStr(decode(encode(s))), readStr(s), 'decode-read != read');
    const a = accountingBits(t);
    assert.equal(encode(s).metaBits, a.total - a.rec_id - a.rec_off - a.hdr_poff);
    states++;
  };
  for (let trial = 0; trial < 120; trial++) {
    const { s: base, view } = evolve(rng, D.init(), [], 8 + Math.floor(rng() * 12), 0);
    gate(base);
    const A = evolve(rng, base, view, 6 + Math.floor(rng() * 10), 1_000_000);
    const B = evolve(rng, base, view, 6 + Math.floor(rng() * 10), 2_000_000);
    gate(A.s); gate(B.s);
    const merged = D.merge3(base, A.s, B.s);
    gate(merged);
    // evolve the merged state further, anchoring on its live view
    const mview = D.readIds(merged);
    gate(evolve(rng, merged, mview, 5 + Math.floor(rng() * 8), 3_000_000).s);
  }
  assert.ok(states >= 600, `only ${states} states gated`);
});
