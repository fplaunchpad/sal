import test from 'node:test';
import assert from 'node:assert/strict';
import { IndexedSequence } from '../lib/indexed-sequence.mjs';

test('indexed sequence matches array insertion, lookup, and deletion', () => {
  const seq = new IndexedSequence(), arr = [];
  let seed = 0x12345678;
  const rnd = () => ((seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0) / 2 ** 32);
  for (let i = 0; i < 20_000; i++) {
    if (arr.length === 0 || rnd() < 0.62) {
      const rank = Math.floor(rnd() * (arr.length + 1));
      const value = `v${i}`;
      arr.splice(rank, 0, value); seq.insert(rank, value);
    } else {
      const rank = Math.floor(rnd() * arr.length);
      assert.equal(seq.delete(rank), arr.splice(rank, 1)[0]);
    }
    assert.equal(seq.length, arr.length);
    if (arr.length) {
      const rank = Math.floor(rnd() * arr.length);
      assert.equal(seq.get(rank), arr[rank]);
    }
  }
  assert.deepEqual(seq.toArray(), arr);
});

test('indexed sequence rejects invalid mutation ranks', () => {
  const seq = IndexedSequence.from([1, 2, 3]);
  assert.throws(() => seq.insert(4, 4), RangeError);
  assert.throws(() => seq.delete(3), RangeError);
  assert.equal(seq.get(-1), undefined);
});
