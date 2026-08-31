// ROSTER vs the certified GC: the stability cut needs evidence from every
// REGISTERED peer, so a drive-by visitor (join, never author, leave) used to
// block GC forever. Now a leave drops a never-authored peer from the roster;
// a peer that DID author stays registered conservatively (the GC-horizon vs
// offline-peers edge, design note 8A).

import test from 'node:test';
import assert from 'node:assert/strict';
import { startRelay } from '../src/relay.mjs';
import { Node } from '../src/node.js';
import { WsTransport, NetworkNode, converge, barrierCompact } from '../src/transport.js';
import { compactibleEmbedRGA } from '../../runtime/src/compact.js';

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

async function until(cond, ms = 5000, step = 25) {
  const rounds = Math.ceil(ms / step);
  for (let i = 0; i < rounds; i++) { if (cond()) return true; await sleep(step); }
  return cond();
}

async function makeNet(url, room, name, passive = true) {
  const node = new Node(compactibleEmbedRGA, name);
  const tp = new WsTransport(url, room, name);
  await tp.ready;
  return new NetworkNode(node, tp, { passive });
}

test('a lurker blocks the cut while present, unblocks on leave; GC then fires', async () => {
  const relay = await startRelay(0);
  const url = `ws://127.0.0.1:${relay.port}`;
  let alice, bob, lurker;
  try {
    alice = await makeNet(url, 'doc-roster', 'alice');
    bob = await makeNet(url, 'doc-roster', 'bob');
    await until(() => alice.node.registered.size === 2 && bob.node.registered.size === 2);

    // a doc whose coordinates the GC can actually shrink: SPARSE ids as the
    // editor mints them (lamport*1000+salt), 30 chars, 10 deletes, then a
    // checkpoint round from each writer
    const mint = (n) => n * 1000 + 7;
    for (let i = 1; i <= 30; i++) {
      alice.node.commit({ type: 'ins', id: mint(i), el: String.fromCharCode(96 + (i % 26)), anchorId: i === 1 ? null : mint(i - 1) });
    }
    await converge([alice, bob]);
    for (let d = 2; d <= 20; d += 2) bob.node.commit({ type: 'del', id: mint(d) });
    await converge([alice, bob]);
    alice.node.commit({ type: 'ins', id: mint(31), el: '!', anchorId: mint(30) });
    await converge([alice, bob]);
    bob.node.commit({ type: 'ins', id: mint(32), el: '?', anchorId: mint(31) });
    await converge([alice, bob]);
    assert.ok(alice.node.stableCut().complete, 'two-writer cut complete');

    // the LURKER: joins (everyone registers it), authors nothing
    lurker = new WsTransport(url, 'doc-roster', 'lurker');
    await lurker.ready;
    assert.ok(await until(() => alice.node.registered.has('lurker')), 'lurker rostered');
    const sc = alice.node.stableCut();
    assert.ok(!sc.complete && sc.missing.includes('lurker'),
      'FAIL companion: a present lurker blocks the cut (no evidence yet)');

    // and compaction itself REFUSES while the lurker is rostered
    assert.equal(alice.node.compactStable().compacted, false,
      'compactStable refuses without the lurker\'s evidence');

    // the lurker LEAVES without ever writing: dropped everywhere, the cut
    // completes, and the coordinated barrier compacts both peers
    lurker.close();
    assert.ok(await until(() => !alice.node.registered.has('lurker')), 'alice dropped the lurker');
    assert.ok(await until(() => !bob.node.registered.has('lurker')), 'bob dropped the lurker');
    assert.ok(alice.node.stableCut().complete, 'cut complete again');
    const readBefore = alice.node.read().join('');
    const results = await barrierCompact([alice, bob], -1);
    assert.equal(results[0].compacted, true, 'alice compacted after the lurker left');
    assert.equal(results[1].compacted, true, 'bob compacted after the lurker left');
    assert.equal(alice.node.read().join(''), readBefore, 'reads preserved across GC');
    assert.equal(bob.node.read().join(''), readBefore, 'peers still agree');
    assert.equal(alice.node.epoch, 1, 'epoch advanced');
  } finally {
    // close transports FIRST: their reconnect loops would retry against the
    // closed relay forever and keep the test runner alive
    alice?.tp.close(); bob?.tp.close(); try { lurker?.close(); } catch {}
    await relay.close();
  }
});

test('a WRITER that leaves stays registered (its ops still gate the cut)', async () => {
  const relay = await startRelay(0);
  const url = `ws://${'127.0.0.1'}:${relay.port}`;
  let alice, carol;
  try {
    alice = await makeNet(url, 'doc-roster2', 'alice');
    carol = await makeNet(url, 'doc-roster2', 'carol');
    await until(() => alice.node.registered.size === 2 && carol.node.registered.size === 2);

    carol.node.commit({ type: 'ins', id: 1, el: 'x', anchorId: null });
    await alice.pull('carol'); // alice HAS carol's authored commit
    assert.ok(alice.node.everAuthored.has('carol'), 'carol is a known author');

    carol.tp.close(); // the writer departs
    await sleep(200); // the leave arrives...
    assert.ok(alice.node.registered.has('carol'),
      '...but a writer is NOT dropped: departed writers still gate the cut');
    assert.equal(alice.node.unregister('carol'), false, 'explicit unregister refuses too');
  } finally {
    alice?.tp.close(); carol?.tp.close();
    await relay.close();
  }
});
