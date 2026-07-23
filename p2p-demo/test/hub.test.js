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

test('history pruning: the hub forgets below a settled epoch; late joiners bootstrap from the base', async () => {
  const kv = new MemoryKV();
  let relay = await startRelay(0, { hub: true, hubKV: kv });
  let url = `ws://127.0.0.1:${relay.port}`;
  const stored = async () => (await kv.entries('objects')).filter(([k]) => k.startsWith('doc-prune')).map(([, r]) => r);

  // alice builds real history in a peritext room (the deployed editor's
  // datatype; its compaction drops settled deletes, giving the GC work)
  const mint = (k) => k * 1000 + 7;
  const a = await makeNet(url, 'doc-prune', 'alice', { datatype: compactiblePeritext, dt: 'peritext' });
  a.node.commitBatch([...Array(20)].map((_, i) => ({ type: 'ins', id: mint(i + 1), el: 'abcdefghij'[i % 10], anchorId: i === 0 ? null : mint(i) })));
  for (let i = 21; i <= 30; i++) a.node.commit({ type: 'ins', id: mint(i), el: 'x', anchorId: mint(i - 1) });
  for (let d = 2; d <= 14; d += 3) a.node.commit({ type: 'del', id: mint(d) }); // tombstones give the GC work
  a.announce();
  const hub = await relay.hubs.get('doc-prune');
  assert.ok(await until(() => hub.node.headGid === a.node.headGid), 'hub caught up');
  await hub.flushPersist();
  const before = await stored();
  assert.ok(before.length >= 12, `full history stored pre-compact (${before.length} records)`);
  assert.ok(before.some((r) => r.kind === 'root'), 'root still stored: nothing pruned yet');

  // alice compacts (solo: cut complete) and keeps typing past the epoch,
  // so her evidence reaches epoch 1 and the hub's prune gate opens
  const g = a.node.compactStable();
  assert.equal(g.compacted, true, 'fixture compacted');
  a.node.commit({ type: 'ins', id: mint(31), el: '!', anchorId: mint(30) });
  a.announce();
  assert.ok(await until(() => hub.node.headGid === a.node.headGid), 'hub past the epoch');
  await hub.flushPersist();
  const after = await stored();
  assert.ok(after.length < before.length, `store shrank (${before.length} -> ${after.length})`);
  assert.ok(after.length <= 4, `O(document), not O(history) (${after.length} records)`);
  assert.ok(after.some((r) => r.kind === 'compact'), 'epoch base stored');
  assert.ok(!after.some((r) => r.kind === 'root'), 'genesis forgotten');
  const aHead = a.node.headGid;
  const aRead = a.node.read().map((e) => e.char).join('');
  a.tp.close();
  await relay.close(); // the process dies; the PRUNED store survives

  relay = await startRelay(0, { hub: true, hubKV: kv }); // wake from the pruned store
  url = `ws://127.0.0.1:${relay.port}`;
  try {
    const b = await makeNet(url, 'doc-prune', 'bob', { datatype: compactiblePeritext, dt: 'peritext' });
    assert.ok(await until(() => b.node.read().map((e) => e.char).join('') === aRead), 'bob bootstrapped from the epoch base');
    assert.equal(b.node.headGid, aHead, 'same head SHA through prune + restart');
    // and the bootstrapped chain is still writable: bob authors, the hub follows
    b.node.commit({ type: 'ins', id: mint(99), el: '.', anchorId: mint(31) });
    b.announce();
    const hub2 = await relay.hubs.get('doc-prune');
    assert.ok(await until(() => hub2.node.read().map((e) => e.char).join('') === aRead + '.'), 'post-bootstrap edit reached the hub');
    b.tp.close();
  } finally { await relay.close(); }
});
