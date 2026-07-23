#!/usr/bin/env node
// PULL A LIVE DOC INTO A GIT REPO. A headless peer joins the room, pulls the
// document from whoever is online (your open browser tab), and persists it
// with src/gitstore.js: one JSON per commit (the SAME SHAs as the wire),
// heads.json, and a readable doc.txt, committed in the target repo. Push
// that repo anywhere with plain git; `git clone` + load() round-trips.
//
//   node scripts/doc2git.mjs --room <room> --repo <path>
//        [--relay ws://127.0.0.1:8787] [--plain] [--message "snapshot"]
//
// --plain selects the plain-text editor's datatype (web/index.html rooms);
// the default is the rich-text peritext (web/richtext.html rooms).
// The script authors nothing, so on disconnect the roster hygiene drops it
// (it never blocks anyone's certified GC).

import { Node } from '../src/node.js';
import { WsTransport, NetworkNode } from '../src/transport.js';
import { persist } from '../src/gitstore.js';
import { compactiblePeritext } from '../../runtime/src/compact-peritext.js';
import { compactibleEmbedRGA } from '../../runtime/src/compact.js';

const args = process.argv.slice(2);
const opt = (name, dflt) => {
  const i = args.indexOf('--' + name);
  return i >= 0 ? args[i + 1] : dflt;
};
const room = opt('room', null);
const repo = opt('repo', null);
const relay = opt('relay', 'ws://127.0.0.1:8787');
const message = opt('message', `doc2git snapshot of room ${room}`);
const datatype = args.includes('--plain') ? compactibleEmbedRGA : compactiblePeritext;

if (!room || !repo) {
  console.error('usage: node scripts/doc2git.mjs --room <room> --repo <path> [--relay ws://host:port] [--plain]');
  process.exit(2);
}

const name = 'doc2git-' + Math.random().toString(16).slice(2, 6);
const node = new Node(datatype, name);
const tp = new WsTransport(relay, room, name);

const bail = (msg, code = 1) => { console.error(msg); try { tp.close(); } catch {} process.exit(code); };
setTimeout(() => bail(`timed out: no relay at ${relay}?`), 15000);

const roster = await tp.ready;
const nn = new NetworkNode(node, tp, { passive: true });
const peers = roster.filter((p) => p !== name);
if (peers.length === 0) {
  bail(`nobody is online in room "${room}" (the relay is stateless: keep the tab with the doc open)`);
}

console.log(`[doc2git] room "${room}", pulling from: ${peers.join(', ')}`);
let got = 0;
for (const p of peers) {
  try { await nn.pull(p); got++; } catch (e) { console.warn(`[doc2git] pull ${p} failed: ${e.message}`); }
}
if (got === 0 || node.dag.size <= 1) bail('no document received (no peer answered with history)');

const chars = node.read().length;
const r = persist(node, repo, { message });
tp.close();
console.log(`[doc2git] persisted ${r.commits} commits, ${chars} chars, head ${r.headSha.slice(0, 8)}`);
console.log(`[doc2git] repo: ${repo} (git commit ${r.gitSha ? r.gitSha.slice(0, 8) : 'unchanged'})`);
console.log(`[doc2git] push it wherever you like:`);
console.log(`    cd ${repo} && git remote add origin <url> && git push -u origin main`);
process.exit(0);
