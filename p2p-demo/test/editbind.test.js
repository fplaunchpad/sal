// STAGE 3 (headless): the textarea binding is correct. Under a single author,
// applying the diff of arbitrary contiguous edits reproduces the target text in
// the RGA read exactly. Also checks that two nodes typing then syncing converge
// (the multi-editor path re-renders from state, so it only needs convergence).

import test from 'node:test';
import assert from 'node:assert/strict';
import { Node } from '../src/node.js';
import { applyTextEdit } from '../src/editbind.js';
import { compactibleEmbedRGA as DT } from '../../runtime/src/compact.js';

function mulberry32(seed) {
  let a = seed >>> 0;
  return () => { a = (a + 0x6d2b79f5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
}

// a state-based mint like the browser's: strictly increasing, unique per salt
function makeMint(node, salt) {
  let lamport = 0;
  return () => {
    let mx = 0; for (const id of node.head.state.keys()) if (id > mx) mx = id;
    lamport = Math.max(lamport, Math.floor(mx / 1000)) + 1;
    return lamport * 1000 + salt;
  };
}

const CHARS = 'abcdefg ';
const randStr = (rng, n) => Array.from({ length: n }, () => CHARS[Math.floor(rng() * CHARS.length)]).join('');

test('single-author binding: random contiguous edits reproduce the text exactly', () => {
  const rng = mulberry32(0x9E3779B1);
  const node = new Node(DT, 'A');
  const mint = makeMint(node, 7);
  let text = '';
  for (let step = 0; step < 400; step++) {
    // build a random contiguous replacement of `text`
    const L = text.length;
    const start = Math.floor(rng() * (L + 1));
    const delLen = Math.floor(rng() * (L - start + 1));
    const insLen = Math.floor(rng() * 4);
    const neu = text.slice(0, start) + randStr(rng, insLen) + text.slice(start + delLen);
    const ids = DT.readIds(node.head.state);
    applyTextEdit(node, ids, text, neu, mint);
    assert.equal(node.read().join(''), neu, `step ${step}: RGA read must equal the target text`);
    text = neu;
  }
  assert.ok(node.read().length >= 0);
});

test('two editors type independently, then converge to one document', () => {
  const A = new Node(DT, 'A'), B = new Node(DT, 'B');
  const mA = makeMint(A, 1), mB = makeMint(B, 2);
  applyTextEdit(A, DT.readIds(A.head.state), '', 'hello ', mA);
  applyTextEdit(B, DT.readIds(B.head.state), '', 'world', mB);
  // bidirectional sync (test helper)
  const sync = (x, y) => {
    const dx = x.delta(y.ancestryGids()), dy = y.delta(x.ancestryGids());
    const xh = x.headGid, yh = y.headGid;
    y.ingest(dx); x.ingest(dy); y.mergeWithGid(xh); x.mergeWithGid(yh);
  };
  sync(A, B);
  assert.equal(A.read().join(''), B.read().join(''), 'converged to equal reads');
  // both fragments survive the merge (order is RGA's; both present)
  const doc = A.read().join('');
  for (const ch of 'hello') assert.ok(doc.includes(ch));
  for (const ch of 'world') assert.ok(doc.includes(ch));
});
