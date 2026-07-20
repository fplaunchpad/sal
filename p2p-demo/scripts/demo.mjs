// `npm run demo` -- a scripted, headless multi-node collaboration scenario over
// the REAL WebSocket transport, printing a readable transcript. It exercises
// every stage: p2p convergence, certified GC under live sync, and the git
// persist -> clone -> load -> catch-up story. No browser required.

import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { startRelay } from '../src/relay.mjs';
import { Node } from '../src/node.js';
import { WsTransport, NetworkNode, converge, barrierCompact } from '../src/transport.js';
import { persist, load } from '../src/gitstore.js';
import { compactibleEmbedRGA as DT } from '../../runtime/src/compact.js';

const SCRATCH = process.env.P2P_SCRATCH || path.join(os.tmpdir());
const base = fs.existsSync(SCRATCH) ? SCRATCH : os.tmpdir();
const log = (...a) => console.log(...a);
const rule = (s) => log('\n' + '='.repeat(4) + ' ' + s + ' ' + '='.repeat(Math.max(0, 66 - s.length)));

/** Type `text` into `node`, each char anchored after the previous, starting
 *  after the displayed id `afterId` (null = document start). Returns last id. */
let MINT = 0;
function type(node, text, afterId = null) {
  let a = afterId;
  for (const ch of text) { const id = ++MINT; node.commit({ type: 'ins', id, el: ch, anchorId: a }); a = id; }
  return a;
}
const lastId = (node) => { const ids = DT.readIds(node.head.state); return ids[ids.length - 1] ?? null; };
const doc = (nn) => nn.node.read().join('');

async function net(url, room, name) {
  const node = new Node(DT, name);
  const tp = new WsTransport(url, room, name); await tp.ready;
  return new NetworkNode(node, tp, { passive: true });
}

async function main() {
  const relay = await startRelay(0);
  const url = `ws://127.0.0.1:${relay.port}`;
  log(`sal p2p-demo -- collaborative editor over the verified MRDT runtime`);
  log(`relay listening at ${url} (star relay; see README "Honest limits")`);
  const room = 'demo';
  const nns = [];
  try {
    rule('1. three peers join the room, each with its OWN store');
    for (const nm of ['alice', 'bob', 'carol']) nns.push(await net(url, room, nm));
    const [alice, bob, carol] = nns;
    await converge(nns);
    log(`   roster known to alice: [${[...alice.node.registered].sort().join(', ')}]`);

    rule('2. alice types, everyone converges over the wire');
    type(alice.node, 'Hello');
    await converge(nns);
    for (const nn of nns) log(`   ${nn.node.name.padEnd(6)} reads: "${doc(nn)}"`);

    rule('3. CONCURRENT edits: bob appends, carol inserts at the front');
    type(bob.node, ', world', lastId(bob.node)); // bob appends after "Hello"
    type(carol.node, '>> ', null);                // carol prepends (concurrent)
    log(`   before sync: bob="${doc(bob)}"  carol="${doc(carol)}"`);
    await converge(nns);
    for (const nn of nns) log(`   ${nn.node.name.padEnd(6)} reads: "${doc(nn)}"`);
    const converged = doc(alice);
    log(`   -> all ${nns.length} peers converged to one document.`);

    rule('4. certified GC UNDER LIVE SYNC (compactStable at a settled barrier)');
    const before = nns.map((nn) => nn.node.symbolCount());
    log(`   live coordinate symbols per peer (state size): [${before.join(', ')}]`);
    const results = await barrierCompact(nns, -1);
    const after = nns.map((nn) => nn.node.symbolCount());
    for (let i = 0; i < nns.length; i++) {
      const r = results[i];
      log(`   ${nns[i].node.name.padEnd(6)} compact: ${r.compacted}` +
        (r.compacted ? `  symbols ${r.stats.symbolsBefore} -> ${r.stats.symbolsAfter}  (epoch ${nns[i].node.epoch})` : `  (${r.reason})`));
    }
    log(`   state size after GC:  [${after.join(', ')}]`);
    log(`   reads unchanged by GC: ${nns.every((nn) => doc(nn) === converged)}  (certified, reads preserved)`);
    log(`   all peers on the identical compacted head SHA: ${nns.every((nn) => nn.node.headGid === alice.node.headGid)}`);

    rule('5. git PERSISTENCE: point at a repo, get the doc');
    const repo = fs.mkdtempSync(path.join(base, 'demo-src-'));
    const p = persist(alice.node, repo, { message: 'demo: converged + compacted doc' });
    log(`   persisted ${p.commits} commits (SHA-addressed) + heads.json + doc.txt to`);
    log(`     ${repo}`);
    log(`   git log:`);
    for (const line of execFileSync('git', ['-C', repo, 'log', '--oneline'], { encoding: 'utf8' }).trim().split('\n')) log(`     ${line}`);
    log(`   doc.txt on disk: "${fs.readFileSync(path.join(repo, 'doc.txt'), 'utf8')}"`);

    rule('6. git CLONE -> load a NEW peer -> reconnect -> catch up');
    const clone = fs.mkdtempSync(path.join(base, 'demo-clone-')); fs.rmSync(clone, { recursive: true, force: true });
    execFileSync('git', ['clone', '-q', repo, clone]);
    const dave = load(clone);
    log(`   cloned + loaded 'dave' from git: reads "${dave.read().join('')}"  (== live doc: ${dave.read().join('') === converged})`);
    // the live peers keep editing while dave was offline
    type(bob.node, '!', lastId(bob.node));
    await converge(nns);
    log(`   meanwhile the live peers edited: "${doc(alice)}"  (dave is now behind)`);
    const daveTp = new WsTransport(url, room, 'dave'); await daveTp.ready;
    const daveNet = new NetworkNode(dave, daveTp, { passive: true }); nns.push(daveNet);
    await converge(nns);
    log(`   dave reconnected and caught up: "${dave.read().join('')}"  (converged: ${nns.every((nn) => doc(nn) === doc(alice))})`);

    rule('done');
    log(`Verified underneath: the commit-DAG merge, the criss-cross gate, the`);
    log(`certified stability cut, and the GC that fired above are the sal runtime's`);
    log(`kernel-clean pieces (runtime/README.md). This script is demo glue on top.`);
  } finally {
    for (const nn of nns) nn.tp.close();
    await relay.close();
  }
}

main().catch((e) => { console.error(e); process.exit(1); });
