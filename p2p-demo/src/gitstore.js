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

/** Serialize a Node's commit at local id `cid` to its on-disk record. */
export function commitRecord(node, cid) {
  const c = node.dag.get(cid);
  const sha = node.gid.get(cid);
  const parents = c.parents.map((p) => node.gid.get(p));
  const epoch = node.epochOf.get(cid);
  if (c.parents.length === 0) return { sha, kind: 'root', parents, epoch };
  if (c.op !== null) {
    return { sha, kind: 'op', parents, epoch,
      op: { replica: c.op.replica, seq: c.op.seq }, payload: c.op.payload };
  }
  if (c.parents.length === 1) {
    // compaction commit: its re-coded state is not recomputable from a parent,
    // so persist it inline via the datatype's own encoder (the same encoding the
    // core DistributedReplica.ingest decodes through datatype.decodeState).
    return { sha, kind: 'compact', parents, epoch, state: node.datatype.encodeState(c.state) };
  }
  return { sha, kind: 'merge', parents, epoch };
}

/** Pure: a node's whole DAG as on-disk records + the heads meta. No I/O, so
 *  it is shared by the git backend (this file) and the IndexedDB backend
 *  (src/idbstore.js): both persist through the SAME record shape and therefore
 *  round-trip identically. `rebuildNode` is the inverse. */
export function nodeRecords(node) {
  const records = [];
  for (const c of node.dag.values()) records.push(commitRecord(node, c.id));
  const heads = { head: node.headGid, replica: node.name, seq: node.seq,
    epoch: node.epoch, roster: [...node.registered], datatype: 'embedRGA' };
  return { records, heads };
}

/** Pure inverse of `nodeRecords`: rebuild a working Node from records + heads.
 *  Replays the records through `ingest` (content-address gated: a tampered
 *  record throws) then `mergeWithGid` to the persisted head. Shared by both
 *  backends. */
export function rebuildNode(records, heads, datatype = compactibleEmbedRGA) {
  const ordered = topoOrder(records);
  const node = new Node(datatype, heads.replica);
  for (const name of heads.roster ?? []) node.register(name);
  const wire = [];
  for (const r of ordered) {
    if (r.kind === 'root') continue; // the fresh Node already has the shared root
    if (r.kind === 'op') {
      wire.push({ gid: r.sha, kind: 'op', parents: r.parents, op: r.op, payload: r.payload });
    } else if (r.kind === 'merge') {
      wire.push({ gid: r.sha, kind: 'merge', parents: r.parents });
    } else if (r.kind === 'compact') {
      wire.push({ gid: r.sha, kind: 'compact', parents: r.parents, epoch: r.epoch, state: r.state });
    }
  }
  node.ingest(wire);
  node.mergeWithGid(heads.head); // fast-forward to the persisted head
  node.seq = heads.seq;          // resume authoring at the right seq
  return node;
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
  const docText = node.read().join('');
  fs.writeFileSync(path.join(repo, 'doc.txt'), docText);

  git(repo, ['add', '-A']);
  // commit only if there is something to commit (avoid a git error on no-op)
  const status = git(repo, ['status', '--porcelain']);
  let gitSha = null;
  if (status) { git(repo, ['commit', '-q', '-m', message]); gitSha = git(repo, ['rev-parse', 'HEAD']); }
  else { try { gitSha = git(repo, ['rev-parse', 'HEAD']); } catch { gitSha = null; } }
  return { headSha: node.headGid, commits: n, docBytes: Buffer.byteLength(docText), gitSha };
}

/** Topologically order records (parents before children). */
export function topoOrder(records) {
  const byId = new Map(records.map((r) => [r.sha, r]));
  const out = [], seen = new Set();
  const visit = (sha) => {
    if (seen.has(sha) || !byId.has(sha)) return;
    seen.add(sha);
    for (const p of byId.get(sha).parents) visit(p);
    out.push(byId.get(sha));
  };
  for (const r of records) visit(r.sha);
  return out;
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
