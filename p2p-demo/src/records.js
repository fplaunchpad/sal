// The PERSISTENCE RECORD SHAPE, browser-safe (no Node-only imports): a
// replica's whole commit DAG as pure-data records plus a heads meta, and the
// inverse rebuild. The durable format IS the wire format: records are
// delta()/ingest() shaped, so every backend that persists through them (the
// git directory codec in gitstore.js, the IndexedDB RefStore in idbstore.js)
// round-trips identically and re-enters the live wire with identical SHAs.
// Extracted from gitstore.js, which re-exports for compatibility; the split
// exists because gitstore shells out to `git` (node:child_process) and can
// never load in a browser tab, where idbstore must.

import { Node } from './node.js';
import { compactibleEmbedRGA } from '../../runtime/src/compact.js';
import { cutToWire } from '../../runtime/src/replica.js';

/** One commit as a pure-data record (content-addressed by its sha). */
export function commitRecord(node, cid) {
  const c = node.dag.get(cid);
  const sha = node.gid.get(cid);
  const parents = c.parents.map((p) => node.gid.get(p));
  const epoch = node.epochOf.get(cid);
  if (c.parents.length === 0) {
    // an EPOCH BASE (pruned history): re-serialize as a compact record with
    // its original wire parent, so its content id checks out on ingest
    const eb = node.epochBase?.get(cid);
    if (eb) {
      return { sha, kind: 'compact', parents: [eb], epoch,
        state: node.datatype.encodeState(c.state) };
    }
    return { sha, kind: 'root', parents, epoch };
  }
  if (c.op !== null) {
    return { sha, kind: 'op', parents, epoch,
      op: { replica: c.op.replica, seq: c.op.seq }, payload: c.op.payload };
  }
  if (c.parents.length === 1) {
    // compaction commit: its re-coded state is not recomputable from a parent,
    // so persist it inline via the datatype's own encoder (the same encoding the
    // core DistributedReplica.ingest decodes through datatype.decodeState). Also
    // persist the CUT (a non-hashed hint) so a reloaded replica can recompute
    // this epoch's translate and still lift older-epoch edits across it (Case 1).
    const rec = { sha, kind: 'compact', parents, epoch, state: node.datatype.encodeState(c.state) };
    const cut = node.compactCut?.get(cid);
    if (cut) rec.cut = cutToWire(cut);
    return rec;
  }
  return { sha, kind: 'merge', parents, epoch };
}

/** Pure: a node's whole DAG as records + the heads meta. Shared by the git
 *  backend and the IndexedDB backend. `rebuildNode` is the inverse. */
/** Which datatype a node carries, detected structurally (records.js must
 *  not import datatype modules): peritext states are { text, marks }. */
export function datatypeLabelOf(node) {
  const st = node.head.state;
  return st && typeof st === 'object' && st.text && st.marks !== undefined ? 'peritext' : 'embedRGA';
}

export function nodeRecords(node, { datatypeLabel = datatypeLabelOf(node) } = {}) {
  const records = [];
  for (const c of node.dag.values()) records.push(commitRecord(node, c.id));
  const heads = { head: node.headGid, replica: node.name, seq: node.seq,
    epoch: node.epoch, roster: [...node.registered], datatype: datatypeLabel };
  return { records, heads };
}

/** Parents-before-children order over records. */
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

/** Records -> ingest-shaped wire commits (parents-before-children; the
 *  shared root is skipped: every fresh Node already has it). Used by
 *  rebuildNode and by IMPORT-into-an-existing-node (the editor's
 *  open-.saldoc), where ingest's content-address gate + SHA dedup make the
 *  operation tamper-proof and idempotent. */
export function wireFromRecords(records) {
  const wire = [];
  for (const r of topoOrder(records)) {
    if (r.kind === 'root') continue;
    if (r.kind === 'op') {
      wire.push({ gid: r.sha, kind: 'op', parents: r.parents, op: r.op, payload: r.payload });
    } else if (r.kind === 'merge') {
      wire.push({ gid: r.sha, kind: 'merge', parents: r.parents });
    } else if (r.kind === 'compact') {
      wire.push({ gid: r.sha, kind: 'compact', parents: r.parents, epoch: r.epoch, state: r.state, cut: r.cut });
    }
  }
  return wire;
}

/** Pure inverse of `nodeRecords`: rebuild a working Node from records + heads.
 *  Replays the records through `ingest` (content-address gated: a tampered
 *  record throws) then `mergeWithGid` to the persisted head.
 *  `opts.name` reopens the doc AS a different replica (a returning device
 *  with a new session name): the stored history ingests unchanged, the
 *  roster keeps every past author, and the authoring seq resumes only when
 *  the name matches the persisted author (else it starts fresh). */
export function rebuildNode(records, heads, datatype = compactibleEmbedRGA, opts = {}) {
  const asName = opts.name ?? heads.replica;
  const node = new Node(datatype, asName);
  for (const name of heads.roster ?? []) node.register(name);
  node.ingest(wireFromRecords(records));
  node.mergeWithGid(heads.head); // fast-forward to the persisted head
  if (asName === heads.replica) node.seq = heads.seq; // resume authoring
  return node;
}
