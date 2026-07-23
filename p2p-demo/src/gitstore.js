// GIT PERSISTENCE (task #95, stage 1): the "point at a git repo, get a doc"
// half. Persist a Node's commit DAG into a git-tracked directory and rebuild a
// working Node from one.
//
// LAYOUT written into the target repo:
//   commits/<sha>.json   one file per commit, SHA-content-addressed (the SAME
//                        sha the wire uses -- src/node.js). authored commits
//                        carry the op payload + parent shas + author; merges
//                        carry parent shas; compaction commits carry their
//                        re-coded state inline (not recomputable from a parent).
//   heads.json           { head, replica, seq, epoch, roster, datatype }.
//   doc.txt              the materialized document text, for human/`git diff`
//                        friendliness: editing the doc changes doc.txt, so a
//                        plain `git log -p` reads as sensible edit history.
// Then `git add -A && git commit` IN THAT REPO. `git clone` yields all three;
// load(clonePath) replays commits/*.json into a fresh Node whose reads equal
// the original and which re-enters the live wire seamlessly (same shas).
//
// GIT FENCING (critical): every git command runs with cwd = the target repo,
// which is a SEPARATE repository; we refuse any path that is, contains, or sits
// inside the sal repo, and before writing we ASSERT `git rev-parse
// --show-toplevel` resolves to the target itself (never sal). The demo's repos
// live under p2p-demo/data/ (gitignored) or a caller path; sal is never touched.

import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import fs from 'node:fs';
import path from 'node:path';
import { Node } from './node.js';
import { compactibleEmbedRGA } from '../../runtime/src/compact.js';
import { commitRecord, nodeRecords, rebuildNode, topoOrder } from './records.js';

// the record shape + rebuild now live in the BROWSER-SAFE src/records.js
// (this file shells out to git and can never load in a tab); re-exported
// here so existing importers keep working
export { commitRecord, nodeRecords, rebuildNode, topoOrder };

const SAL_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..'); // p2p-demo/src -> sal

/** Refuse any path that is / contains / lives inside the sal repository. */
export function assertSafeRepo(repoPath) {
  const resolved = path.resolve(repoPath);
  const salGit = path.join(SAL_ROOT, '.git');
  const inside = (child, parent) => child === parent || child.startsWith(parent + path.sep);
  if (resolved === SAL_ROOT || inside(resolved, salGit)) {
    throw new Error(`git-fencing: refusing to operate on the sal repo itself (${resolved})`);
  }
  if (inside(SAL_ROOT, resolved)) {
    throw new Error(`git-fencing: refusing a path that contains the sal repo (${resolved})`);
  }
  return resolved;
}

const git = (repo, args) => execFileSync('git', ['-C', repo, ...args], { encoding: 'utf8' }).trim();

/** Assert the target really is its own git repo (toplevel == itself), never
 *  sal. Canonicalizes both sides (git reports the realpath; macOS symlinks
 *  /var -> /private/var, so a raw string compare would spuriously fail). */
function assertOwnRepo(repoPath) {
  const real = (p) => { try { return fs.realpathSync(p); } catch { return path.resolve(p); } };
  const top = real(git(repoPath, ['rev-parse', '--show-toplevel']));
  if (top !== real(repoPath)) {
    throw new Error(`git-fencing: ${repoPath} resolves to a DIFFERENT repo toplevel ${top}; aborting`);
  }
}

/** Persist `node`'s whole commit DAG into the git repo at `repoPath`, then
 *  commit. Returns { headSha, commits, docBytes, gitSha }. */
export function persist(node, repoPath, { message = 'p2p-demo snapshot' } = {}) {
  const repo = assertSafeRepo(repoPath);
  fs.mkdirSync(path.join(repo, 'commits'), { recursive: true });
  if (!fs.existsSync(path.join(repo, '.git'))) {
    execFileSync('git', ['init', '-q', '-b', 'main', repo]);
    git(repo, ['config', 'user.email', 'demo@p2p-demo.local']);
    git(repo, ['config', 'user.name', 'p2p-demo']);
  }
  assertOwnRepo(repo); // hard guard: this is its OWN repo, not sal

  // fresh commits/ each time: the DAG is the source of truth, doc.txt the view
  const { records, heads } = nodeRecords(node);
  const cdir = path.join(repo, 'commits');
  for (const f of fs.readdirSync(cdir)) if (f.endsWith('.json')) fs.rmSync(path.join(cdir, f));
  for (const rec of records) fs.writeFileSync(path.join(cdir, rec.sha + '.json'), JSON.stringify(rec));
  const n = records.length;
  fs.writeFileSync(path.join(repo, 'heads.json'), JSON.stringify(heads, null, 2));
  // datatype-aware materialization: embedRGA reads are chars, peritext reads
  // are {id, char, marks} entries; doc.txt is the human view either way
  const docText = node.read().map((e) => (e && typeof e === 'object' && 'char' in e ? e.char : String(e))).join('');
  fs.writeFileSync(path.join(repo, 'doc.txt'), docText);

  git(repo, ['add', '-A']);
  // commit only if there is something to commit (avoid a git error on no-op)
  const status = git(repo, ['status', '--porcelain']);
  let gitSha = null;
  if (status) { git(repo, ['commit', '-q', '-m', message]); gitSha = git(repo, ['rev-parse', 'HEAD']); }
  else { try { gitSha = git(repo, ['rev-parse', 'HEAD']); } catch { gitSha = null; } }
  return { headSha: node.headGid, commits: n, docBytes: Buffer.byteLength(docText), gitSha };
}

/** Rebuild a working Node from the git repo at `repoPath`. Reads equal the
 *  persisted node's; the Node re-enters the live wire with identical shas. */
export function load(repoPath, datatype = compactibleEmbedRGA) {
  const repo = path.resolve(repoPath);
  const heads = JSON.parse(fs.readFileSync(path.join(repo, 'heads.json'), 'utf8'));
  const cdir = path.join(repo, 'commits');
  const records = fs.readdirSync(cdir).filter((f) => f.endsWith('.json'))
    .map((f) => JSON.parse(fs.readFileSync(path.join(cdir, f), 'utf8')));
  return rebuildNode(records, heads, datatype);
}
