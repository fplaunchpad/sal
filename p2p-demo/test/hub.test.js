// THE SYNC HUB (design-note step 4): a headless per-room replica living with
// the relay, so docs survive everyone disconnecting. PASS+FAIL shaped:
//   - availability: A edits and LEAVES; B joins an empty room later and
//     converges from the hub alone (previously impossible: the FAIL shape is
//     pinned by running the same trace against a hubless relay).
//   - durability: the hub store outlives the relay process; a NEW relay over
//     the same store serves the doc.
//   - invisibility: the hub never enters a client's roster, so the stability
//     cut stays a matter between real peers.
//   - datatype: a peritext room's marks survive the hub round-trip.

import test from 'node:test';
import assert from 'node:assert/strict';
import { startRelay } from '../src/relay.mjs';
import { Node } from '../src/node.js';
import { WsTransport, NetworkNode } from '../src/transport.js';
import { MemoryKV } from '../src/idbstore.js';
import { compactibleEmbedRGA } from '../../runtime/src/compact.js';
import { compactiblePeritext } from '../../runtime/src/compact-peritext.js';

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
async function until(cond, ms = 5000, step = 25) {
  const rounds = Math.ceil(ms / step);
  for (let i = 0; i < rounds; i++) { if (cond()) return true; await sleep(step); }
  return cond();
}
async function makeNet(url, room, name, { datatype = compactibleEmbedRGA, dt = 'embedRGA' } = {}) {
  const node = new Node(datatype, name);
  const tp = new WsTransport(url, room, name, { dt });
  await tp.ready;
  return new NetworkNode(node, tp, { passive: false });
}

test('availability: edit, leave, and a LATER peer catches up from the hub', async () => {
  const relay = await startRelay(0, { hub: true });
  const url = `ws://127.0.0.1:${relay.port}`;
  try {
    const a = await makeNet(url, 'doc-hub', 'alice');
    a.node.commit({ type: 'ins', id: 1, el: 'h', anchorId: null });
    a.node.commit({ type: 'ins', id: 2, el: 'i', anchorId: 1 });
    a.announce();
    // wait for the hub to have pulled (observable via the persisted head)
    const hub = await relay.hubs.get('doc-hub');
    assert.ok(await until(() => hub.node.headGid === a.node.headGid), 'hub caught up');
    const aHead = a.node.headGid;
    a.tp.close();
    await sleep(150); // alice is gone

    const b = await makeNet(url, 'doc-hub', 'bob'); // empty room, later
    assert.ok(await until(() => b.node.read().join('') === 'hi'), 'bob converged from the hub alone');
    assert.equal(b.node.headGid, aHead, 'same head SHA');
    // invisibility: bob rosters only himself (the hub never joins)
    assert.deepEqual([...b.node.registered].sort(), ['alice', 'bob'].sort().filter((n) => b.node.registered.has(n)),
      'no #hub in the roster');
    assert.ok(!b.node.registered.has('#hub'), 'hub name absent');
    b.tp.close();
  } finally { await relay.close(); }
});

test('FAIL companion: without the hub, the later peer gets nothing', async () => {
  const relay = await startRelay(0); // hubless
  const url = `ws://127.0.0.1:${relay.port}`;
  try {
    const a = await makeNet(url, 'doc-nohub', 'alice');
    a.node.commit({ type: 'ins', id: 1, el: 'x', anchorId: null });
    a.announce();
    await sleep(150);
    a.tp.close();
    const b = await makeNet(url, 'doc-nohub', 'bob');
    await sleep(400);
    assert.equal(b.node.read().join(''), '', 'stateless relay: the doc left with alice');
    b.tp.close();
  } finally { await relay.close(); }
});

test('durability: the hub store outlives the relay process', async () => {
  const kv = new MemoryKV(); // stands in for DO storage / disk
  let relay = await startRelay(0, { hub: true, hubKV: kv });
  let url = `ws://127.0.0.1:${relay.port}`;
  const a = await makeNet(url, 'doc-dur', 'alice');
  a.node.commit({ type: 'ins', id: 1, el: 'z', anchorId: null });
  a.announce();
  const hub = await relay.hubs.get('doc-dur');
  assert.ok(await until(() => hub.node.headGid === a.node.headGid), 'hub synced');
  await hub.flushPersist();
  const aHead = a.node.headGid;
  a.tp.close();
  await relay.close(); // the PROCESS dies; kv survives

  relay = await startRelay(0, { hub: true, hubKV: kv }); // a fresh relay, same store
  url = `ws://127.0.0.1:${relay.port}`;
  try {
    const b = await makeNet(url, 'doc-dur', 'bob');
    assert.ok(await until(() => b.node.read().join('') === 'z'), 'doc restored from the store');
    assert.equal(b.node.headGid, aHead, 'same head SHA across the restart');
    b.tp.close();
  } finally { await relay.close(); }
});

test('peritext room: marks survive the hub round-trip', async () => {
  const relay = await startRelay(0, { hub: true });
  const url = `ws://127.0.0.1:${relay.port}`;
  try {
    const a = await makeNet(url, 'doc-rt', 'alice', { datatype: compactiblePeritext, dt: 'peritext' });
    const mint = (k) => k * 1000 + 7;
    a.node.commitBatch([
      { type: 'ins', id: mint(1), el: 'o', anchorId: null },
      { type: 'ins', id: mint(2), el: 'k', anchorId: mint(1) },
      { type: 'addMark', mid: mint(3), mtype: 'bold', startId: mint(1), endId: mint(2), startSide: 'before', endSide: 'after', ts: mint(3) },
    ]);
    a.announce();
    const hub = await relay.hubs.get('doc-rt');
    assert.ok(await until(() => hub.node.headGid === a.node.headGid), 'hub synced');
    a.tp.close();
    await sleep(150);

    const b = await makeNet(url, 'doc-rt', 'bob', { datatype: compactiblePeritext, dt: 'peritext' });
    assert.ok(await until(() => b.node.read().map((e) => e.char).join('') === 'ok'), 'text from the hub');
    assert.ok(b.node.read().every((e) => e.marks.some((m) => m.mtype === 'bold')), 'marks intact');
    b.tp.close();
  } finally { await relay.close(); }
});
