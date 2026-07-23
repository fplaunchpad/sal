#!/usr/bin/env node
// TURN A DOWNLOADED .saldoc.json BUNDLE INTO A GIT REPO. The bundle is the
// editor's "download" export: the replica's WHOLE commit DAG (records +
// heads), the same shape the wire and every durable backend use. Rebuild is
// content-address gated (a tampered record throws), then gitstore persists:
// commits/<sha>.json + heads.json + readable doc.txt, committed in the
// target repo. Push from there with plain git.
//
//   node scripts/bundle2git.mjs <file.saldoc.json> --repo <path> [--message m]

import fs from 'node:fs';
import { rebuildNode } from '../src/records.js';
import { persist } from '../src/gitstore.js';
import { compactiblePeritext } from '../../runtime/src/compact-peritext.js';
import { compactibleEmbedRGA } from '../../runtime/src/compact.js';

const args = process.argv.slice(2);
const file = args.find((a) => !a.startsWith('--'));
const opt = (name, dflt) => {
  const i = args.indexOf('--' + name);
  return i >= 0 ? args[i + 1] : dflt;
};
const repo = opt('repo', null);
if (!file || !repo) {
  console.error('usage: node scripts/bundle2git.mjs <file.saldoc.json> --repo <path> [--message m]');
  process.exit(2);
}

const bundle = JSON.parse(fs.readFileSync(file, 'utf8'));
if (bundle.v !== 1 || !Array.isArray(bundle.records) || !bundle.heads) {
  console.error('not a v1 .saldoc bundle (expected { v: 1, doc, datatype, records, heads })');
  process.exit(2);
}
const datatype = bundle.datatype === 'peritext' ? compactiblePeritext : compactibleEmbedRGA;
const message = opt('message', `bundle2git snapshot of doc ${bundle.doc ?? '?'}`);

const node = rebuildNode(bundle.records, bundle.heads, datatype); // SHA-gated
const chars = node.read().length;
const r = persist(node, repo, { message });
console.log(`[bundle2git] persisted ${r.commits} commits, ${chars} chars, head ${r.headSha.slice(0, 8)}`);
console.log(`[bundle2git] repo: ${repo} (git commit ${r.gitSha ? r.gitSha.slice(0, 8) : 'unchanged'})`);
console.log(`[bundle2git] push it wherever you like:`);
console.log(`    cd ${repo} && git remote add origin <url> && git push -u origin main`);
