// STAGE 2 headline integration test: real WebSocket transport, 4 p2p nodes,
// each with its OWN store, concurrently editing and gossiping to convergence;
// certified GC fired mid-session under live sync; then git persist -> clone ->
// load a NEW node -> reconnect -> catch up. If this passes, the demo works
// even without touching the browser UI.

import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { startRelay } from '../src/relay.mjs';
import { Node } from '../src/node.js';
import { WsTransport, NetworkNode, converge, barrierCompact } from '../src/transport.js';
import { persist, load } from '../src/gitstore.js';
import { compactibleEmbedRGA } from '../../runtime/src/compact.js';

const SCRATCH = process.env.P2P_SCRATCH
  || '/private/tmp/claude-501/-Users-kc-repos-sal/74a8d128-cfeb-4afb-ab2c-8c8e4f58a7ce/scratchpad';
const base = fs.existsSync(SCRATCH) ? SCRATCH : os.tmpdir();
const mkrepo = (tag) => fs.mkdtempSync(path.join(base, `int-${tag}-`));

function mulberry32(seed) {
  let a = seed >>> 0;
  return () => { a = (a + 0x6d2b79f5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
}
const pick = (rng, xs) => xs[Math.floor(rng() * xs.length)];

async function makeNet(url, room, name, passive = true) {
  const node = new Node(compactibleEmbedRGA, name);
  const tp = new WsTransport(url, room, name);
  await tp.ready;
  return new NetworkNode(node, tp, { passive });
}

test('headline: 4 nodes converge over the wire; certified GC under sync; git clone catch-up', async () => {
  const relay = await startRelay(0);
  const url = `ws://127.0.0.1:${relay.port}`;
  const room = 'doc-headline';
  const NAMES = ['alice', 'bob', 'carol'];
  const nns = [];
  let mint = 0;

  try {
    for (const nm of NAMES) nns.push(await makeNet(url, room, nm));
    // let the join/roster handshake settle, then confirm every node knows the roster
    await converge(nns);
    for (const nn of nns) assert.equal(nn.node.registered.size, NAMES.length, `${nn.node.name} sees full roster`);

    // ---- Phase A: concurrent random edits, gossip to convergence ----
    const rng = mulberry32(0x5A1AD);
    for (let round = 0; round < 12; round++) {
      for (const nn of nns) {
        for (let k = 0; k < 4; k++) {
          const view = compactibleEmbedRGA.readIds(nn.node.head.state);
          if (view.length > 4 && rng() < 0.25) { nn.node.commit({ type: 'del', id: pick(rng, view) }); continue; }
          const id = ++mint; // strictly increasing global tick -> id > any live anchor
          const anchorId = view.length && rng() < 0.7 ? pick(rng, view) : null;
          nn.node.commit({ type: 'ins', id, el: String.fromCharCode(97 + (id % 26)), anchorId });
        }
      }
      await converge(nns);
      const reads = nns.map((nn) => nn.node.read().join(''));
      for (let i = 1; i < reads.length; i++) assert.equal(reads[i], reads[0], `round ${round}: ${nns[i].node.name} diverged`);
    }
    const convergedDoc = nns[0].node.read().join('');
    assert.ok(convergedDoc.length > 10, 'a non-trivial document was built');

    // ---- Phase B: certified GC UNDER LIVE SYNC (the running-GC witness) ----
    const symbolsBefore = nns.map((nn) => nn.node.symbolCount());
    const results = await barrierCompact(nns, -1); // -1: a no-op checkpoint id
    for (let i = 0; i < nns.length; i++) {
      assert.equal(results[i].compacted, true, `${nns[i].node.name} certified-compacted`);
      assert.ok(results[i].stats.symbolsAfter < results[i].stats.symbolsBefore, 'coordinate cost shrank');
      assert.equal(nns[i].node.epoch, 1, `${nns[i].node.name} advanced to epoch 1`);
    }
    // reads UNCHANGED by the compaction, and still equal across all nodes
    const afterGc = nns.map((nn) => nn.node.read().join(''));
    for (const r of afterGc) assert.equal(r, convergedDoc, 'certified GC preserved reads');
    for (let i = 0; i < nns.length; i++)
      assert.ok(nns[i].node.symbolCount() < symbolsBefore[i], `${nns[i].node.name} state size dropped`);
    // identical compaction across nodes: same head SHA everywhere
    for (let i = 1; i < nns.length; i++)
      assert.equal(nns[i].node.headGid, nns[0].node.headGid, 'all nodes hold the identical compacted head SHA');

    // keep editing AFTER GC and re-converge (GC did not wedge the session)
    for (const nn of nns) {
      const view = compactibleEmbedRGA.readIds(nn.node.head.state);
      nn.node.commit({ type: 'ins', id: ++mint, el: '!', anchorId: view.length ? view[0] : null });
    }
    await converge(nns);
    const postEdit = nns.map((nn) => nn.node.read().join(''));
    for (let i = 1; i < postEdit.length; i++) assert.equal(postEdit[i], postEdit[0], 'post-GC editing still converges');

    // ---- Phase C: git persist -> clone -> load a NEW node -> reconnect -> catch up ----
    const srcRepo = mkrepo('persist');
    persist(nns[0].node, srcRepo, { message: 'headline snapshot (epoch 1)' });
    const clone = mkrepo('clone'); fs.rmSync(clone, { recursive: true, force: true });
    execFileSync('git', ['clone', '-q', srcRepo, clone]);
    const dave = load(clone); // a fresh Node reconstructed from git, at epoch 1
    assert.equal(dave.read().join(''), nns[0].node.read().join(''), 'loaded clone reads equal the live doc');

    // meanwhile the live nodes make MORE edits (dave is now behind)
    for (const nn of nns) nn.node.commit({ type: 'ins', id: ++mint, el: '?', anchorId: null });
    await converge(nns);
    const liveDoc = nns[0].node.read().join('');
    assert.notEqual(liveDoc, dave.read().join(''), 'dave is behind after the live edits');

    // reconnect dave over the transport and catch up
    const daveTp = new WsTransport(url, room, 'dave'); await daveTp.ready;
    const daveNet = new NetworkNode(dave, daveTp, { passive: true });
    nns.push(daveNet);
    await converge(nns); // dave folds in and everyone converges
    const finalReads = nns.map((nn) => nn.node.read().join(''));
    for (let i = 1; i < finalReads.length; i++)
      assert.equal(finalReads[i], finalReads[0], `${nns[i].node.name} did not converge after dave rejoined`);
    assert.equal(dave.read().join(''), liveDoc, 'git-cloned node caught up to the live document over the wire');
  } finally {
    for (const nn of nns) nn.tp.close();
    await relay.close();
  }
});
