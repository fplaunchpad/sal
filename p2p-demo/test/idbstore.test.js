// IndexedDB RefStore round-trips (task #95), the browser sibling of the git
// backend. These exercise the STORE LOGIC + the shared record round-trip
// (nodeRecords / rebuildNode) against the in-memory backend (MemoryKV), so they
// run headlessly with no dependency (node has no IndexedDB). The real IndexedDB
// adapter (openIdbKV) is a thin shim over the browser API, covered by the
// browser/integration path, not here.
//
// PASS+FAIL shaped: every round-trip is pinned by a degenerate the store must
// NOT produce (an empty/scrambled read, a fabricated doc, cross-doc bleed, a
// silently-loaded tampered record).

import test from 'node:test';
import assert from 'node:assert/strict';
import { Node } from '../src/node.js';
import { RefStore, MemoryKV } from '../src/idbstore.js';

// same helper as gitstore.test.js: type `text` as a chain of embedRGA inserts.
function typeDoc(node, text, anchor = null) {
  let a = anchor, id = node.seq === 0 ? 1000 : 1000 + node.seq * 100;
  for (const ch of text) { node.commit({ type: 'ins', id, el: ch, anchorId: a }); a = id; id++; }
  return node;
}

test('persistNode -> loadNode: reads and SHA head equal the original', async () => {
  const src = typeDoc(new Node(undefined, 'A'), 'hello');
  const original = src.read().join('');
  assert.equal(original, 'hello');

  const store = new RefStore(new MemoryKV());
  const r = await store.persistNode('doc-1', src);
  assert.equal(r.commits, src.dag.size, 'every commit persisted (root included)');

  const loaded = await store.loadNode('doc-1');
  assert.equal(loaded.read().join(''), original, 'loaded reads equal the original');
  assert.equal(loaded.headGid, src.headGid, 'same SHA head after round-trip');
  assert.equal(loaded.seq, src.seq, 'authoring seq resumed');

  // FAIL companions: the store neither loses order, empties the doc, nor invents one.
  assert.notEqual(loaded.read().join(''), '', 'not the empty degenerate');
  assert.notEqual(loaded.read().join(''), 'olleh', 'reading order not lost/reversed');
  assert.equal(await store.loadNode('no-such-doc'), null, 'an absent doc is null, not fabricated');
  assert.equal(await store.getHead('no-such-doc'), null, 'absent head is null');
});

test('re-persist after an edit grows the store; reload reflects the edit', async () => {
  const store = new RefStore(new MemoryKV());
  const node = typeDoc(new Node(undefined, 'A'), 'cat');
  await store.persistNode('doc-2', node);
  const before = (await store.getRecords('doc-2')).length;
  assert.equal(before, node.dag.size, 'record count == DAG size');

  const ids = node.datatype.readIds(node.head.state);
  typeDoc(node, 'X', ids[ids.length - 1]); // append after the last-shown char
  await store.persistNode('doc-2', node);   // idempotent re-put + the new commit
  const after = (await store.getRecords('doc-2')).length;

  assert.equal(after, before + 1, 'exactly one new record, not duplicated');
  const loaded = await store.loadNode('doc-2');
  assert.equal(loaded.read().join(''), 'catX', 'reload carries the edit');
  assert.notEqual(loaded.read().join(''), 'cat', 'the edit is not lost'); // FAIL companion
});

test('two docs in one store stay isolated; drop(A) leaves B intact', async () => {
  const store = new RefStore(new MemoryKV());
  await store.persistNode('A', typeDoc(new Node(undefined, 'A'), 'hello'));
  await store.persistNode('B', typeDoc(new Node(undefined, 'B'), 'world'));

  assert.equal((await store.loadNode('A')).read().join(''), 'hello');
  assert.equal((await store.loadNode('B')).read().join(''), 'world');
  assert.deepEqual(
    (await store.listDocs()).map((d) => d.docId).sort(), ['A', 'B'],
    'directory lists both docs',
  );

  await store.drop('A');
  assert.equal(await store.loadNode('A'), null, 'dropped doc is gone');            // FAIL companion
  assert.equal((await store.loadNode('B')).read().join(''), 'world', 'B untouched'); // isolation pin
});

test('a tampered durable record trips the content-address gate on load', async () => {
  const store = new RefStore(new MemoryKV());
  await store.persistNode('doc-3', typeDoc(new Node(undefined, 'A'), 'hello'));

  // pin: the untampered store loads cleanly (the gate is not vacuously throwing).
  assert.equal((await store.loadNode('doc-3')).read().join(''), 'hello');

  // corrupt one op record's payload but keep its stored sha; ingest recomputes
  // the gid from the payload and must reject the mismatch.
  const recs = await store.getRecords('doc-3');
  const op = recs.find((r) => r.kind === 'op');
  assert.ok(op, 'there is an op record to tamper');
  op.payload = { ...op.payload, el: 'Z' };
  await store.putObjects('doc-3', [op]); // overwrites at the same sha key

  await assert.rejects(store.loadNode('doc-3'), /content-address mismatch/,
    'a corrupted durable store cannot silently load wrong data');
});
