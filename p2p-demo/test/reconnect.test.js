// RECONNECT regression test: browsers close the sockets of long-backgrounded
// tabs. Before the reconnect logic in WsTransport, a dropped page became a
// ZOMBIE: UI said "connected", every send was silently discarded, and the two
// sides diverged forever. Now a drop emits 'down', the transport rejoins with
// backoff, emits 'up', and NetworkNode's announce-on-up catches up BOTH ways.

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

async function makeNet(url, room, name) {
  const node = new Node(compactibleEmbedRGA, name);
  const tp = new WsTransport(url, room, name);
  await tp.ready;
  return new NetworkNode(node, tp, { passive: false });
}

test('transport survives a socket drop: down, rejoin, up', async () => {
  const relay = await startRelay(0);
  try {
    const tp = new WsTransport(`ws://127.0.0.1:${relay.port}`, 'doc-rc', 'alice');
    await tp.ready;
    const events = [];
    tp.on('down', () => events.push('down'));
    tp.on('up', () => events.push('up'));

    tp.ws.close(); // simulate the browser dropping a backgrounded tab's socket
    assert.ok(await until(() => events.includes('up')), `rejoined (saw: ${events})`);
    assert.deepEqual(events, ['down', 'up'], 'one drop, one recovery');
    assert.equal(tp.ws.readyState, 1, 'socket is open again');

    tp.close(); // a DELIBERATE close must NOT trigger a reconnect
    await sleep(600);
    assert.deepEqual(events, ['down', 'up'], 'no phantom reconnect after close()');
  } finally { await relay.close(); }
});

test('peers re-converge after a drop: edits from BOTH sides of the outage land', async () => {
  const relay = await startRelay(0);
  const url = `ws://127.0.0.1:${relay.port}`;
  try {
    const alice = await makeNet(url, 'doc-rc2', 'alice');
    const bob = await makeNet(url, 'doc-rc2', 'bob');
    await until(() => alice.node.registered.size === 2 && bob.node.registered.size === 2);

    alice.tp.ws.close(); // alice's tab gets backgrounded and dropped
    await until(() => alice.tp.ws.readyState !== 1);

    // both sides edit DURING the outage
    bob.node.commit({ type: 'ins', id: 1, el: 'b', anchorId: null });
    bob.announce(); // reaches nobody relevant: alice is down
    alice.node.commit({ type: 'ins', id: 2, el: 'a', anchorId: null });
    alice.announce(); // silently dropped: socket is closed

    // FAIL companion: while down, bob must NOT have alice's edit
    await sleep(200);
    assert.ok(!bob.node.read().includes('a'), 'no teleporting ops while down');

    // after the auto-rejoin, announce-on-up merges the outage edits both ways
    assert.ok(await until(() =>
      alice.node.read().join('') === bob.node.read().join('') && alice.node.read().length === 2),
      `re-converged (alice "${alice.node.read().join('')}", bob "${bob.node.read().join('')}")`);
    assert.equal(alice.node.headGid, bob.node.headGid, 'same head SHA after recovery');

    alice.tp.close(); bob.tp.close();
  } finally { await relay.close(); }
});
