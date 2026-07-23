// STAGE 1 test: git persistence round-trips, `git clone` yields a loadable
// doc, an edit on the clone shows sensible `git log`/`git diff` history, and
// the fencing refuses the sal repo.

import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { Node } from '../src/node.js';
import { persist, load, assertSafeRepo } from '../src/gitstore.js';

// scratch repos: the given scratchpad if present, else the OS temp dir -- both
// OUTSIDE the sal repo (the fencing forbids sal itself).
const SCRATCH = process.env.P2P_SCRATCH
  || '/private/tmp/claude-501/-Users-kc-repos-sal/74a8d128-cfeb-4afb-ab2c-8c8e4f58a7ce/scratchpad';
const base = fs.existsSync(SCRATCH) ? SCRATCH : os.tmpdir();
const mkrepo = (tag) => fs.mkdtempSync(path.join(base, `gs-${tag}-`));
const git = (repo, args) => execFileSync('git', ['-C', repo, ...args], { encoding: 'utf8' }).trim();

function typeDoc(node, text, anchor = null) {
  let a = anchor, id = node.seq === 0 ? 1000 : 1000 + node.seq * 100;
  for (const ch of text) { node.commit({ type: 'ins', id, el: ch, anchorId: a }); a = id; id++; }
  return node;
}

test('persist -> git clone -> load: reads equal the original', () => {
  const src = new Node(undefined, 'A');
  typeDoc(src, 'hello');
  const original = src.read().join('');
  assert.equal(original.length, 5, 'five characters typed (RGA display order)');

  const repo = mkrepo('src');
  const r = persist(src, repo, { message: 'initial doc' });
  assert.equal(r.commits, src.dag.size, 'every commit persisted');
  assert.ok(fs.existsSync(path.join(repo, 'doc.txt')), 'doc.txt materialized');
  assert.ok(fs.existsSync(path.join(repo, 'heads.json')), 'heads.json written');

  const clone = mkrepo('clone');
  fs.rmSync(clone, { recursive: true, force: true });
  execFileSync('git', ['clone', '-q', repo, clone]);
  assert.ok(fs.existsSync(path.join(clone, 'commits')), 'clone carries commits/');

  const loaded = load(clone);
  assert.equal(loaded.read().join(''), original, 'loaded clone reads equal the original');
  assert.equal(loaded.headGid, src.headGid, 'same SHA head after clone+load');
});

test('edit on the clone -> persist -> git log / git diff show sensible history', () => {
  const src = new Node(undefined, 'A');
  typeDoc(src, 'cat');
  const repo = mkrepo('hist');
  persist(src, repo, { message: 'write cat' });
  const firstDoc = fs.readFileSync(path.join(repo, 'doc.txt'), 'utf8');

  const clone = mkrepo('histclone');
  fs.rmSync(clone, { recursive: true, force: true });
  execFileSync('git', ['clone', '-q', repo, clone]);
  const doc = load(clone);
  assert.equal(doc.read().join(''), src.read().join(''));

  // edit: append more characters, then persist to the CLONE's repo
  const liveIds = doc.datatype.readIds(doc.head.state);
  typeDoc(doc, 'X', liveIds[liveIds.length - 1]); // insert after the last-shown char
  const r2 = persist(doc, clone, { message: 'append X' });
  const secondDoc = fs.readFileSync(path.join(clone, 'doc.txt'), 'utf8');

  assert.notEqual(secondDoc, firstDoc, 'doc.txt changed after the edit');
  const log = git(clone, ['log', '--oneline']);
  assert.equal(log.split('\n').length, 2, 'two git commits in the clone history');
  assert.match(log, /append X/, 'the edit commit is in the log');
  const diff = git(clone, ['show', '--stat', 'HEAD']);
  assert.match(diff, /doc\.txt/, 'git show reports doc.txt among the changed files');
  assert.ok(r2.gitSha, 'the edit produced a real git commit sha');

  // re-load the edited clone: reads still round-trip
  const reloaded = load(clone);
  assert.equal(reloaded.read().join(''), doc.read().join(''), 'edited clone re-loads identically');
});

test('git-fencing: the sal repo is refused', () => {
  assert.throws(() => assertSafeRepo(path.resolve(import.meta.dirname, '../..')),
    /refusing to operate on the sal repo/);
  assert.throws(() => assertSafeRepo(path.resolve(import.meta.dirname, '../../.git')),
    /refusing to operate on the sal repo/);
  assert.throws(() => persist(new Node(undefined, 'A'), path.resolve(import.meta.dirname, '../..')),
    /git-fencing/);
});

test('peritext doc persists: doc.txt is the chars, load round-trips marks', async () => {
  const { compactiblePeritext } = await import('../../runtime/src/compact-peritext.js');
  const repo = mkrepo('peritext');
  const n = new Node(compactiblePeritext, 'A');
  const mint = (k) => k * 1000 + 7;
  n.commitBatch([
    { type: 'ins', id: mint(1), el: 'h', anchorId: null },
    { type: 'ins', id: mint(2), el: 'i', anchorId: mint(1) },
    { type: 'addMark', mid: mint(3), mtype: 'bold', startId: mint(1), endId: mint(2), startSide: 'before', endSide: 'after', ts: mint(3) },
  ]);
  const r = persist(n, repo);
  assert.equal(fs.readFileSync(path.join(repo, 'doc.txt'), 'utf8'), 'hi',
    'doc.txt is the characters, not [object Object]');
  const back = load(repo, compactiblePeritext);
  assert.equal(back.read().map((e) => e.char).join(''), 'hi');
  assert.ok(back.read().every((e) => e.marks.some((m) => m.mtype === 'bold')), 'marks survive the repo');
  assert.equal(back.headGid, r.headSha, 'same head SHA after clone-shaped load');
});

test('bundle2git CLI: a .saldoc bundle becomes a loadable git repo', async () => {
  const { compactiblePeritext } = await import('../../runtime/src/compact-peritext.js');
  const { nodeRecords } = await import('../src/records.js');
  const n = new Node(compactiblePeritext, 'kc');
  const mint = (k) => k * 1000 + 3;
  n.commitBatch([
    { type: 'ins', id: mint(1), el: 'o', anchorId: null },
    { type: 'ins', id: mint(2), el: 'k', anchorId: mint(1) },
  ]);
  const bundle = { v: 1, doc: 'cli-doc', datatype: 'peritext', ...nodeRecords(n, { datatypeLabel: 'peritext' }) };
  const file = path.join(mkrepo('bundlejson'), 'doc.saldoc.json');
  fs.writeFileSync(file, JSON.stringify(bundle));
  const repo = mkrepo('bundlerepo');
  const out = execFileSync('node', ['scripts/bundle2git.mjs', file, '--repo', repo], { encoding: 'utf8' });
  assert.match(out, /persisted 2 commits/);
  assert.equal(fs.readFileSync(path.join(repo, 'doc.txt'), 'utf8'), 'ok');
  const back = load(repo, compactiblePeritext);
  assert.equal(back.headGid, n.headGid, 'same head SHA through download -> CLI -> repo');
  // FAIL companion: a tampered record trips the SHA gate through the same CLI
  const bad = structuredClone(bundle);
  const op = bad.records.find((r) => r.kind === 'op');
  op.payload[0].el = 'X';
  const badFile = path.join(mkrepo('bundlebad'), 'bad.saldoc.json');
  fs.writeFileSync(badFile, JSON.stringify(bad));
  assert.throws(() => execFileSync('node', ['scripts/bundle2git.mjs', badFile, '--repo', mkrepo('badrepo')], { encoding: 'utf8', stdio: 'pipe' }),
    /content-address mismatch/);
});
