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
