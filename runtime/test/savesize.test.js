// SAVE-SIZE PROBE (task #104 surfaced): compactiblePeritext.saveBytes is the
// run-table serialization of the text shadow plus compact JSON of the
// deleted set and mark records: the durable cost, vs the in-memory
// coordinate JSON that snapshotBytes reports. PASS+FAIL shaped: the probe
// must be far below the JSON on a chain-heavy doc (the whole point), must
// grow with content (not a constant), and the shadow serialization must
// round-trip losslessly.

import test from 'node:test';
import assert from 'node:assert/strict';
import { compactiblePeritext } from '../src/compact-peritext.js';
import { roundTripReads } from '../src/serialize.js';
import { DistributedReplica } from '../src/replica.js';

// editor-shaped history: sparse minted ids (n*1000+7), continuation typing,
// a mark, a few deletes
function buildDoc(n) {
  const r = new DistributedReplica(compactiblePeritext, 'E');
  const mint = (k) => k * 1000 + 7;
  const ops = [];
  for (let i = 1; i <= n; i++) {
    ops.push({ type: 'ins', id: mint(i), el: 'abcdefghij'[i % 10], anchorId: i === 1 ? null : mint(i - 1) });
  }
  ops.push({ type: 'addMark', mid: mint(n + 1), mtype: 'bold', startId: mint(2), endId: mint(5), startSide: 'before', endSide: 'after', ts: mint(n + 1) });
  for (let d = 3; d <= Math.min(9, n); d += 3) ops.push({ type: 'del', id: mint(d) });
  r.commitBatch(ops);
  return r;
}

test('saveBytes is the run-table cost: far below the NAIVE coordinate JSON, grows with content', () => {
  const r = buildDoc(60);
  const save = r.saveBytes();
  // the naive v1-style coordinate JSON (absolute '0'/'1' chains per record):
  // the representation both saveBytes and encodeState v2 exist to beat
  const naive = new TextEncoder().encode(JSON.stringify(
    [...r.head.state.text.shadow.entries()].map(([id, c]) => [id, c.coord, c.el]))).length;
  assert.ok(save > 0, 'nonzero');
  assert.ok(save < naive / 10,
    `run-table save (${save}B) is an order below the coordinate JSON (${naive}B)`);
  // and the v2 snapshot (what snapshotBytes now measures) is in the same
  // small regime as the save, no longer the naive JSON
  assert.ok(r.snapshotBytes() < naive / 5,
    `v2 snapshot (${r.snapshotBytes()}B) also far below naive (${naive}B)`);

  // FAIL companions: not a constant (more content costs more), and the
  // datatype-less fallback is the JSON itself
  const small = buildDoc(5).saveBytes();
  assert.ok(small < save, `5-char doc (${small}B) < 60-char doc (${save}B)`);
  assert.ok(small > 20, 'even the small doc pays for its records');
});

test('the shadow serialization is lossless (reads identical after decode)', () => {
  const r = buildDoc(40);
  assert.equal(roundTripReads(r.head.state.text.shadow), true, 'round-trip reads equal');
});

test('encodeState v2: run-table shadow + id sidecar round-trips, incl. POST-GC', () => {
  const r = buildDoc(60);
  const dt = compactiblePeritext;

  // pre-compaction round-trip: reads, marks, and the fingerprint all survive
  const enc = dt.encodeState(r.head.state);
  assert.equal(enc.v, 2, 'the v2 shape');
  const back = dt.decodeState(enc);
  assert.deepEqual(dt.read(back), dt.read(r.head.state), 'reads equal (chars + marks + ids)');
  assert.equal(dt.fingerprint(back), dt.fingerprint(r.head.state), 'fingerprint equal');

  // the snapshot is FAR below the v1 coordinate JSON (the point of v2)
  const v2Bytes = new TextEncoder().encode(JSON.stringify(enc)).length;
  const v1Bytes = new TextEncoder().encode(JSON.stringify(
    { text: { shadow: [...r.head.state.text.shadow.entries()].map(([id, c]) => [id, c.coord, c.el]),
      deleted: [...r.head.state.text.deleted] },
      marks: [...r.head.state.marks.entries()].map(([, m]) => m) })).length;
  assert.ok(v2Bytes < v1Bytes / 10, `v2 (${v2Bytes}B) an order below v1 (${v1Bytes}B)`);

  // POST-COMPACTION: ids are no longer delta sums (rank renumbering), so this
  // is the case the sidecar exists for
  const g = r.compactStable();
  assert.equal(g.compacted, true, 'compaction fired (solo replica: cut trivially complete)');
  const enc2 = dt.encodeState(r.head.state);
  const back2 = dt.decodeState(enc2);
  assert.deepEqual(dt.read(back2), dt.read(r.head.state), 'post-GC reads equal');
  assert.equal(dt.fingerprint(back2), dt.fingerprint(r.head.state), 'post-GC fingerprint equal');

  // FAIL companion: legacy v1 input still decodes (back-compat dispatch)
  const legacy = dt.decodeState({ text: { shadow: [[5, '1001', 'z']], deleted: [] }, marks: [] });
  assert.equal(dt.read(legacy).map((e) => e.char).join(''), 'z', 'v1 shape still accepted');
});
