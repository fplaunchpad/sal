// MANUAL MERGE (git-style explicit sync). In manual mode a peer still FETCHES
// every delta (ingest: content-addressed, head untouched -- `git fetch`) but
// merges only on mergeStaged() (`git merge`). Because merge3 is total there is
// never a conflict prompt; manual is a consent policy. The key local-first
// property pinned here: the staged merge needs NO network (the commits are
// already local), so review-then-merge works offline.

import test from 'node:test';
import assert from 'node:assert/strict';
import { startRelay } from '../src/relay.mjs';
import { Node } from '../src/node.js';
import { WsTransport, NetworkNode } from '../src/transport.js';
import { compactibleEmbedRGA } from '../../runtime/src/compact.js';

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

async function until(cond, ms = 5000, step = 25) {
  const rounds = Math.ceil(ms / step);
  for (let i = 0; i < rounds; i++) { if (cond()) return true; await sleep(step); }
  return cond();
}

async function makeNet(url, room, name, opts = {}) {
  const node = new Node(compactibleEmbedRGA, name);
  const tp = new WsTransport(url, room, name);
  await tp.ready;
  return new NetworkNode(node, tp, { passive: false, ...opts });
}

test('manual mode: deltas are FETCHED not merged; mergeStaged() merges OFFLINE', async () => {
  const relay = await startRelay(0);
  const url = `ws://127.0.0.1:${relay.port}`;
  try {
    const alice = await makeNet(url, 'doc-manual', 'alice');
    const bob = await makeNet(url, 'doc-manual', 'bob', { manual: true });
    await until(() => alice.node.registered.size === 2 && bob.node.registered.size === 2);

    alice.node.commit({ type: 'ins', id: 1, el: 'h', anchorId: null });
    alice.node.commit({ type: 'ins', id: 2, el: 'i', anchorId: 1 });
    alice.announce();
    const aliceHead = alice.node.headGid;

    // the delta ARRIVES (fetch) but the doc does NOT move (no merge)
    assert.ok(await until(() => bob.staged.size === 1), 'alice head staged at bob');
    await sleep(150); // FAIL companion window: nothing may auto-merge
    assert.equal(bob.node.read().join(''), '', 'manual bob did not merge');
    assert.notEqual(bob.node.headGid, aliceHead, 'bob head unmoved');

    // local editing in manual mode is unaffected
    bob.node.commit({ type: 'ins', id: 9, el: 'x', anchorId: null });
    assert.equal(bob.node.read().join(''), 'x', 'local commits land while unmerged');

    // go OFFLINE, then merge: the commits are already local, no network needed
    alice.tp.close(); bob.tp.close();
    const left = bob.mergeStaged();
    assert.equal(left, 0, 'everything staged merged');
    const text = bob.node.read().join('');
    assert.equal(text.length, 3, 'both sides of the divergence present');
    assert.ok(text.includes('hi'), "alice's run survives contiguously");
    assert.ok(text.includes('x'), "bob's own edit survives");
  } finally { await relay.close(); }
});

test('setManual(false) merges the backlog; explicit pull() merges even in manual', async () => {
  const relay = await startRelay(0);
  const url = `ws://127.0.0.1:${relay.port}`;
  try {
    const alice = await makeNet(url, 'doc-manual2', 'alice');
    const bob = await makeNet(url, 'doc-manual2', 'bob', { manual: true });
    await until(() => alice.node.registered.size === 2 && bob.node.registered.size === 2);

    alice.node.commit({ type: 'ins', id: 1, el: 'a', anchorId: null });
    alice.announce();
    assert.ok(await until(() => bob.staged.size === 1), 'staged');
    assert.equal(bob.node.read().join(''), '', 'not merged yet');

    bob.setManual(false); // leaving manual mode drains the backlog
    assert.equal(bob.node.read().join(''), 'a', 'auto mode catch-up on toggle');
    assert.equal(bob.staged.size, 0);
    assert.equal(bob.node.headGid, alice.node.headGid, 'same head SHA');

    // back to manual; an AWAITED pull is an explicit sync and always merges
    bob.setManual(true);
    alice.node.commit({ type: 'ins', id: 2, el: 'b', anchorId: 1 });
    await bob.pull('alice');
    assert.equal(bob.node.read().join(''), 'ab', 'pull() merged despite manual mode');

    alice.tp.close(); bob.tp.close();
  } finally { await relay.close(); }
});
