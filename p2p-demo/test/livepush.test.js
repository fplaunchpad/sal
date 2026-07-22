// LIVE PUSH regression test: a lone typist's edits must reach an idle peer.
//
// The gossip's `have` only tops up the ANNOUNCER (receivers send back what the
// announcer lacks). Before the pull-on-have fix in NetworkNode, an ACTIVE idle
// peer receiving a have that advertised an unknown head did nothing, so a
// single editing peer never propagated: the browser editor sat at "syncing"
// forever. converge()-based tests never see this (they drive explicit pulls),
// hence this dedicated PASS+FAIL pair:
//   PASS  active idle peer catches up from the announce alone, same head SHA
//   FAIL  passive idle peer must NOT catch up (pure pull is preserved; the
//         deterministic converge() fold depends on passive never reacting)

import test from 'node:test';
import assert from 'node:assert/strict';
import { startRelay } from '../src/relay.mjs';
import { Node } from '../src/node.js';
import { WsTransport, NetworkNode } from '../src/transport.js';
import { compactibleEmbedRGA } from '../../runtime/src/compact.js';

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

async function makeNet(url, room, name, passive) {
  const node = new Node(compactibleEmbedRGA, name);
  const tp = new WsTransport(url, room, name);
  await tp.ready;
  return new NetworkNode(node, tp, { passive });
}

async function until(cond, ms = 3000, step = 25) {
  const rounds = Math.ceil(ms / step);
  for (let i = 0; i < rounds; i++) { if (cond()) return true; await sleep(step); }
  return cond();
}

test('live push: a lone typist reaches an idle ACTIVE peer via announce alone', async () => {
  const relay = await startRelay(0);
  const url = `ws://127.0.0.1:${relay.port}`;
  try {
    const alice = await makeNet(url, 'doc-livepush', 'alice', false);
    const bob = await makeNet(url, 'doc-livepush', 'bob', false);
    await until(() => alice.node.registered.size === 2 && bob.node.registered.size === 2);

    // alice types; bob does NOTHING (no converge, no pull, no edits)
    alice.node.commit({ type: 'ins', id: 1, el: 'h', anchorId: null });
    alice.node.commit({ type: 'ins', id: 2, el: 'i', anchorId: 1 });
    alice.announce();

    assert.ok(await until(() => bob.node.read().join('') === 'hi'),
      `bob caught up from the announce (got "${bob.node.read().join('')}")`);
    assert.equal(bob.node.headGid, alice.node.headGid, 'same head SHA (fast-forward, no merge)');

    // and the reverse direction still works: bob types, alice catches up
    bob.node.commit({ type: 'ins', id: 3, el: '!', anchorId: 2 });
    bob.announce();
    assert.ok(await until(() => alice.node.read().join('') === 'hi!'), 'alice caught up from bob');

    alice.tp.close(); bob.tp.close();
  } finally { await relay.close(); }
});

test('live push does NOT fire for a PASSIVE idle peer (pure pull preserved)', async () => {
  const relay = await startRelay(0);
  const url = `ws://127.0.0.1:${relay.port}`;
  try {
    const alice = await makeNet(url, 'doc-passive', 'alice', false);
    const bob = await makeNet(url, 'doc-passive', 'bob', true); // passive
    await until(() => alice.node.registered.size === 2 && bob.node.registered.size === 2);

    alice.node.commit({ type: 'ins', id: 1, el: 'x', anchorId: null });
    alice.announce();
    await sleep(300); // long enough that the active path WOULD have converged

    assert.equal(bob.node.read().join(''), '', 'passive bob did not absorb the push');
    assert.notEqual(bob.node.headGid, alice.node.headGid, 'passive bob head unchanged');

    // an explicit pull (what converge() does) still brings him up
    await bob.pull('alice');
    assert.equal(bob.node.read().join(''), 'x', 'explicit pull still works');

    alice.tp.close(); bob.tp.close();
  } finally { await relay.close(); }
});
