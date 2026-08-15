// FETCH-ALIGNED GC RECEIPTS over the real WebSocket transport. A quiet peer
// acknowledges the verified epoch it reached; it does not mint a document op.

import test from 'node:test';
import assert from 'node:assert/strict';
import { startRelay } from '../src/relay.mjs';
import { Node } from '../src/node.js';
import { WsTransport, NetworkNode, converge } from '../src/transport.js';
import { compactiblePeritext } from '../../runtime/src/compact-peritext.js';

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
async function until(cond, ms = 5000, step = 20) {
  for (let left = ms; left > 0; left -= step) {
    if (cond()) return true;
    await sleep(step);
  }
  return cond();
}
async function makeNet(url, room, name) {
  const node = new Node(compactiblePeritext, name);
  const tp = new WsTransport(url, room, name);
  await tp.ready;
  return new NetworkNode(node, tp, { passive: true });
}

test('quiet peer fetch acknowledgement unlocks empty-document epoch pruning', async () => {
  const relay = await startRelay(0);
  const url = `ws://127.0.0.1:${relay.port}`;
  let alice, bob;
  try {
    alice = await makeNet(url, 'ack-gc', 'alice');
    bob = await makeNet(url, 'ack-gc', 'bob');
    await until(() => alice.node.registered.size === 2 && bob.node.registered.size === 2);

    alice.node.commit({ type: 'ins', id: 1, el: 'x', anchorId: null });
    await converge([alice, bob]);
    alice.node.commit({ type: 'del', id: 1 });
    await converge([alice, bob]);
    bob.node.commit({ type: 'del', id: 1 });
    await converge([alice, bob]);

    const compacted = alice.node.compactStable();
    assert.equal(compacted.compacted, true);
    assert.equal(alice.node.symbolCount(), 0);

    bob.tp.sendTo('alice', { t: 'ack', head: 'forged-head', epoch: alice.node.epochKey });
    await sleep(40);
    assert.equal(alice.node.pruneToEpochBase().pruned, 0,
      'missing/forged receipt does not license history pruning');

    await bob.pull('alice');
    assert.ok(await until(() => alice.node.fetchAcks.get('bob') === alice.node.epochKey),
      'alice received bob\'s verified epoch receipt');

    bob.tp.sendTo('alice', { t: 'ack', head: bob.node.headGid, epoch: bob.node.epochKey });
    await sleep(40);
    const pruned = alice.node.pruneToEpochBase();
    assert.ok(pruned.pruned > 0);
    assert.equal(alice.node.dag.size, 1, 'only the constant-size empty epoch base remains');
  } finally {
    alice?.tp.close(); bob?.tp.close();
    await relay.close();
  }
});
