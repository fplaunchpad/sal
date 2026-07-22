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

test('saveBytes is the run-table cost: far below snapshot JSON, grows with content', () => {
  const r = buildDoc(60);
  const save = r.saveBytes();
  const json = r.snapshotBytes();
  assert.ok(save > 0, 'nonzero');
  assert.ok(save < json / 10,
    `run-table save (${save}B) is an order below the coordinate JSON (${json}B)`);

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
