// THE DELTA/OP SYNC WIRE (task #104, item 3): an Automerge-repo-style
// gossip protocol between peers that hold SEPARATE commit stores. Two peers
// exchange their DAG frontier (head content-ids), each computes which commits
// the other lacks (ancestor-set difference), and ships those as a DELTA:
// per commit only the op payload + parent refs + author replica-id, never the
// whole state. A state snapshot (src/serialize.js) is used only where one is
// genuinely warranted -- an initial bulk catch-up, offered when the delta
// would exceed the snapshot (see deltaOrSnapshot).
//
// CONTENT ADDRESSING (task #108: the ONE hash). Two separate stores assign
// different LOCAL ids ('c0'..) to the same commit, so the wire speaks GLOBAL
// content-ids minted by the core Merkle-DAG derivation commitContentId
// (src/hash.js): an authored commit hashes {parents, replica, seq, payload},
// a merge commit hashes its SORTED parent ids (so merge(a,b) and merge(b,a)
// are the SAME commit and never diverge into a spurious criss-cross), the root
// hashes {root:true}. Peers dedup on the global id: a commit already held is
// skipped. This is the SAME content id the git-persistence demo uses on disk
// (WIRE and DISK agree), replacing the FNV model hash a `Peer` used to carry.
// The `hash` constructor argument is pluggable (default: the SHA content id).
//
// HEAD-SYNC DISCIPLINE preserved: a peer only ever merges its CURRENT head
// with the CURRENT head another peer just advertised over the wire (now local
// after ingest), never with a stale interior commit -- exactly the hypothesis
// the commit GC's gc_safety consumes (runtime-gc-note.md section 4). merges
// go through the same lca() criss-cross gate as the shared-store runtime.
//
// THE FRONTIER IS BUILT FROM THE WIRE. Each peer maintains the same evidence
// frontier as the shared-store Replica (src/frontier.js), here fed by what
// arrives over sync: absorbing a peer's commits advances the per-replica
// evidence commits, so stableCut() is certifiable exactly once the peer has
// heard from everyone. This is the coupling in #106's framing -- the sync
// wire and the evidence-certificate producer are one subsystem.

import { Dag } from './dag.js';
import { lca, CrissCrossError } from './lca.js';
import { frontierOf, stableCut } from './frontier.js';
import { encode as encodeSnapshot } from './serialize.js';
import { commitContentId, contentId } from './hash.js';

const utf8 = new TextEncoder();
/** Byte size of a JSON-serializable wire message (browser-safe; no Buffer). */
export const wireBytes = (msg) => utf8.encode(JSON.stringify(msg)).length;

export class Peer {
  #headId;
  constructor(datatype, name, { hash = contentId } = {}) {
    this.datatype = datatype;
    this.name = name;
    this.hash = hash;
    this.dag = new Dag();
    this.seq = 0;
    this.gid = new Map();          // local id -> global content id
    this.byGid = new Map();        // global content id -> local id
    this.registered = new Set([name]); // replica ids this peer has heard of
    const root = this.dag.add({ parents: [], op: null, state: datatype.init() });
    this.#index(root);
    this.#headId = root.id;
    this.frontier = frontierOf(this.dag, this.#headId);
  }

  get head() { return this.dag.get(this.#headId); }
  get headGid() { return this.gid.get(this.#headId); }
  read() { return this.datatype.read(this.head.state); }

  #gidOf(commit) {
    const pg = commit.parents.map((p) => this.gid.get(p));
    return commitContentId(commit, pg, { fingerprint: this.datatype.fingerprint, hash: this.hash });
  }
  #index(commit) {
    const g = this.#gidOf(commit);
    this.gid.set(commit.id, g);
    this.byGid.set(g, commit.id);
    return g;
  }
  #refresh() { this.frontier = frontierOf(this.dag, this.#headId); }

  /** Apply one op on this peer's own current head (the only local mutator). */
  commit(payload) {
    const state = this.datatype.apply(this.head.state, payload);
    const c = this.dag.add({
      parents: [this.#headId], op: { replica: this.name, seq: this.seq++, payload }, state });
    this.#index(c);
    this.#headId = c.id;
    this.#refresh();
    return this.gid.get(c.id);
  }

  /** The set of global ids in this head's reflexive ancestry (a have-summary;
   *  cheap hashes, not payloads). */
  ancestryGids() {
    const s = new Set();
    for (const cid of this.dag.ancestorSet(this.#headId)) s.add(this.gid.get(cid));
    return s;
  }

  /** The DELTA: this head's ancestry commits whose global id the peer lacks,
   *  as wire commits (payload + parent refs + author id; NO state), in a
   *  parents-before-children order (local ids increase with creation). */
  delta(theirGids) {
    const missing = [];
    for (const cid of this.dag.ancestorSet(this.#headId)) {
      if (theirGids.has(this.gid.get(cid))) continue;
      const c = this.dag.get(cid);
      if (c.parents.length === 0) continue; // root is shared, never shipped
      missing.push({ cid, c });
    }
    missing.sort((x, y) => Number(x.cid.slice(1)) - Number(y.cid.slice(1)));
    return missing.map(({ c }) => ({
      gid: this.gid.get(c.id),
      parents: c.parents.map((p) => this.gid.get(p)),
      op: c.op ? { replica: c.op.replica, seq: c.op.seq } : null,
      payload: c.op ? c.op.payload : null,
    }));
  }

  /** Ingest a delta: add each missing commit, recomputing its state (apply for
   *  authored, merge3 for merges) -- never trusting a transmitted state. The
   *  recomputed global id must match the wire id (content-address gate). */
  ingest(wireCommits) {
    let added = 0;
    for (const wc of wireCommits) {
      if (this.byGid.has(wc.gid)) continue; // dedup: already held
      const localParents = wc.parents.map((g) => this.byGid.get(g));
      if (localParents.some((p) => p === undefined)) {
        throw new Error(`ingest: unknown parent for ${wc.gid} (delta not ancestor-closed)`);
      }
      let op, state;
      if (wc.op === null) {
        const [p0, p1] = localParents; // merge commit
        const l = lca(this.dag, p0, p1);
        state = this.datatype.merge3(
          this.dag.get(l).state, this.dag.get(p0).state, this.dag.get(p1).state);
        op = null;
      } else {
        op = { replica: wc.op.replica, seq: wc.op.seq, payload: wc.payload };
        state = this.datatype.apply(this.dag.get(localParents[0]).state, wc.payload);
        this.registered.add(wc.op.replica);
      }
      const c = this.dag.add({ parents: localParents, op, state });
      const g = this.#index(c);
      if (g !== wc.gid) throw new Error(`content-address mismatch: recomputed ${g} != wire ${wc.gid}`);
      added++;
    }
    if (added > 0) this.#refresh();
    return added;
  }

  /** Merge this peer's current head with the (now-local) commit named `gid`.
   *  Fast-forwards when one subsumes the other, else a head-sync merge through
   *  the unique lca (CrissCrossError on a criss-cross, the #90 gate). */
  mergeWithGid(gid) {
    const b = this.byGid.get(gid);
    if (b === undefined) throw new Error(`mergeWithGid: ${gid} not present (ingest first)`);
    const a = this.#headId;
    if (a === b) return this.headGid;
    if (this.dag.isAncestor(a, b)) { this.#headId = b; this.#refresh(); return this.headGid; }
    if (this.dag.isAncestor(b, a)) return this.headGid; // a subsumes b: no change
    const l = lca(this.dag, a, b);
    const merged = this.datatype.merge3(
      this.dag.get(l).state, this.dag.get(a).state, this.dag.get(b).state);
    const c = this.dag.add({ parents: [a, b], op: null, state: merged });
    this.#index(c);
    this.#headId = c.id;
    this.#refresh();
    return this.headGid;
  }

  /** The certified stable cut over the replicas this peer has heard of
   *  (src/frontier.js), fed entirely by wire arrivals. */
  stableCut() {
    return stableCut(this.dag, this.#headId, [...this.registered], this.name);
  }

  /** Whole-state snapshot (src/serialize.js) and its byte size -- the
   *  baseline the delta beats, and the initial-bulk-catch-up payload. */
  snapshot() { return encodeSnapshot(this.head.state); }
  snapshotBytes() { return this.snapshot().length; }
}

/** ONE full bidirectional sync round between two peers. Each computes the
 *  other's delta (from head frontiers snapshotted BEFORE any merge), both
 *  ingest, then both merge their head with the other's advertised head. After
 *  the round both stores hold every commit and (content-addressing the shared
 *  merge) their heads carry equal reads -- unless the pair criss-crosses, in
 *  which case the merges are gated (merged=false) like the shared-store PBT.
 *  Returns the DELTA payload bytes exchanged and the whole-state baseline. */
export function syncPeers(a, b) {
  const hasA = a.ancestryGids(), hasB = b.ancestryGids();
  const toB = a.delta(hasB); // commits B lacks, from A
  const toA = b.delta(hasA); // commits A lacks, from B
  const aHead = a.headGid, bHead = b.headGid;
  const baseline = a.snapshotBytes() + b.snapshotBytes();
  b.ingest(toB);
  a.ingest(toA);
  let merged = true;
  try {
    b.mergeWithGid(aHead);
    a.mergeWithGid(bHead);
  } catch (e) {
    if (e instanceof CrissCrossError) merged = false; else throw e;
  }
  const bytes = wireBytes({ t: 'delta', c: toB }) + wireBytes({ t: 'delta', c: toA });
  return { bytes, baseline, toBCount: toB.length, toACount: toA.length, merged };
}

/** The wire delta between two heads in a SHARED store (benchmark helper): the
 *  commits in fromHead's ancestry the toHead lacks, as wire commits (payload +
 *  parent refs + author id, NO state) -- the same shape syncPeers ships over
 *  separate stores, so wireBytes(...) measures the real per-sync payload the
 *  protocol would transmit. Uses the shared local ids as global ids (unique
 *  within one store). */
export function sharedDelta(dag, fromHeadId, toHeadId) {
  const have = dag.ancestorSet(toHeadId);
  const out = [];
  for (const cid of dag.ancestorSet(fromHeadId)) {
    if (have.has(cid)) continue;
    const c = dag.get(cid);
    if (c.parents.length === 0) continue; // root shared
    out.push({
      gid: cid, parents: c.parents,
      op: c.op ? { replica: c.op.replica, seq: c.op.seq } : null,
      payload: c.op ? c.op.payload : null,
    });
  }
  return out;
}

/** deltaOrSnapshot: the encoder's choice for a one-shot catch-up message --
 *  the delta unless it exceeds the whole-state snapshot, in which case a bulk
 *  snapshot is smaller (a brand-new peer, or one very far behind). This is the
 *  one place src/serialize.js is genuinely the right wire payload. */
export function deltaOrSnapshot(sender, receiverGids) {
  const d = sender.delta(receiverGids);
  const deltaSize = wireBytes({ t: 'delta', c: d });
  const snapSize = sender.snapshotBytes();
  return deltaSize <= snapSize
    ? { kind: 'delta', commits: d, bytes: deltaSize }
    : { kind: 'snapshot', bytes: snapSize };
}
