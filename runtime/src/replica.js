// THE FIRST-CLASS DISTRIBUTED REPLICA (task #108): the runtime's two-store
// split resolved into ONE object over ONE commit store that has BOTH wire sync
// AND certified compaction.
//
// The split it folds together:
//   - src/runtime.js `Replica` had ONE shared store with the certified state GC
//     (frontier -> stableCut -> compactStable) and the keep-set commit GC, but
//     NO wire: replicas shared a store and merged by moving head pointers.
//   - src/sync.js `Peer` had its OWN separate store with delta gossip
//     (ancestryGids / delta / ingest, content-address gated), but NO compaction.
// The p2p demo needed both, and glued them ad hoc under an ad-hoc SHA hash.
// DistributedReplica IS that combination, promoted into the core: a separate
// content-addressed store with (a) local ops, (b) delta gossip, (c) the
// certified stability GC, (d) the keep-set commit GC, (e) SHA content
// addressing throughout (src/hash.js). The p2p demo's Node is now a thin
// re-export of this object.
//
// DATATYPE-PARAMETRIC. Everything except state compaction is datatype-agnostic
// (init/apply/merge3/read). A datatype that also provides {compact, remapState,
// encodeState, decodeState} additionally gets the certified state GC; one that
// does not (e.g. orset) gets everything else and refuses compactStable. Both
// embedRGA and orset are exercised in test/replica.test.js.
//
// EPOCHS / CONCURRENT COMPACTION. compactStable opens a new epoch (re-coded
// coordinates), and a cross-epoch merge THROWS: the runtime linearizes
// compaction epochs. Concurrent divergent compaction (two replicas compacting
// different cuts, then merging across epochs) is the deferred protocol half
// (the #97 multi-epoch CompatChain, whiteboard/stability-vc-note.md section 8);
// we do NOT claim it. Callers reach a common epoch with a coordinated
// checkpoint barrier (barrierCompact, below).

import { Dag } from './dag.js';
import { lca } from './lca.js';
import { runGc } from './gc.js';
import { frontierOf, stableCut, insertIds } from './frontier.js';
import { commitContentId, contentId } from './hash.js';
import { compactibleEmbedRGA } from './compact.js';

export class DistributedReplica {
  #headId;
  constructor(datatype = compactibleEmbedRGA, name = 'r0', { hash = contentId } = {}) {
    this.datatype = datatype;
    this.name = name;
    this.hash = hash;
    this.dag = new Dag();
    this.seq = 0;
    this.gid = new Map();               // local id -> content id (sha)
    this.byGid = new Map();             // content id -> local id
    this.registered = new Set([name]);  // replica ids heard of / rostered
    this.epochs = [null];               // e -> translate(epoch e-1 -> e)
    this.epochOf = new Map();           // local id -> epoch number
    const root = this.dag.add({ parents: [], op: null, state: datatype.init() });
    this.epochOf.set(root.id, 0);
    this.#index(root);
    this.#headId = root.id;
    this.frontier = frontierOf(this.dag, this.#headId);
  }

  get head() { return this.dag.get(this.#headId); }
  get headGid() { return this.gid.get(this.#headId); }
  get epoch() { return this.epochOf.get(this.#headId); }
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

  /** Apply one op on this replica's own current head (the only local mutator). */
  commit(payload) {
    const state = this.datatype.apply(this.head.state, payload);
    const c = this.dag.add({
      parents: [this.#headId], op: { replica: this.name, seq: this.seq++, payload }, state });
    this.epochOf.set(c.id, this.epochOf.get(this.#headId));
    this.#index(c);
    this.#headId = c.id;
    this.#refresh();
    return this.gid.get(c.id);
  }

  /** Global ids in this head's reflexive ancestry (the have-summary). */
  ancestryGids() {
    const s = new Set();
    for (const cid of this.dag.ancestorSet(this.#headId)) s.add(this.gid.get(cid));
    return s;
  }

  /** The DELTA: ancestry commits the peer lacks, as wire commits (parents-
   *  before-children). Op payload for authored, parent refs for merges,
   *  datatype-encoded inline state for compaction commits (not recomputable). */
  delta(theirGids) {
    const missing = [];
    for (const cid of this.dag.ancestorSet(this.#headId)) {
      if (theirGids.has(this.gid.get(cid))) continue;
      const c = this.dag.get(cid);
      if (c.parents.length === 0) continue; // root shared, never shipped
      missing.push(cid);
    }
    missing.sort((x, y) => Number(x.slice(1)) - Number(y.slice(1)));
    return missing.map((cid) => {
      const c = this.dag.get(cid);
      const parents = c.parents.map((p) => this.gid.get(p));
      if (c.op !== null) {
        return { gid: this.gid.get(cid), kind: 'op', parents,
          op: { replica: c.op.replica, seq: c.op.seq }, payload: c.op.payload };
      }
      if (c.parents.length === 1) {
        return { gid: this.gid.get(cid), kind: 'compact', parents,
          epoch: this.epochOf.get(cid), state: this.datatype.encodeState(c.state) };
      }
      return { gid: this.gid.get(cid), kind: 'merge', parents };
    });
  }

  #mergeEpoch(p0, p1) {
    const e0 = this.epochOf.get(p0), e1 = this.epochOf.get(p1);
    if (e0 !== e1) {
      throw new Error(
        `cross-epoch merge (${e0} vs ${e1}): the runtime linearizes compaction ` +
        `epochs with a settled barrier; concurrent divergent compaction is the ` +
        `deferred protocol half (README, stability-vc-note section 8)`);
    }
    return e0;
  }

  /** Ingest a delta: add each missing commit, recomputing state (apply/merge3)
   *  except compaction commits (state inline, datatype-decoded, SHA-gated). The
   *  recomputed gid must equal the wire gid (content-address gate). */
  ingest(wireCommits) {
    let added = 0;
    for (const wc of wireCommits) {
      if (this.byGid.has(wc.gid)) continue;
      const localParents = wc.parents.map((g) => this.byGid.get(g));
      if (localParents.some((p) => p === undefined)) {
        throw new Error(`ingest: unknown parent for ${wc.gid} (delta not ancestor-closed)`);
      }
      let op = null, state, epoch;
      if (wc.kind === 'op') {
        op = { replica: wc.op.replica, seq: wc.op.seq, payload: wc.payload };
        state = this.datatype.apply(this.dag.get(localParents[0]).state, wc.payload);
        epoch = this.epochOf.get(localParents[0]);
        this.registered.add(wc.op.replica);
      } else if (wc.kind === 'compact') {
        state = this.datatype.decodeState(wc.state);
        epoch = this.epochOf.get(localParents[0]) + 1;
        while (this.epochs.length <= epoch) this.epochs.push(null);
      } else { // merge
        const [a, b] = localParents;
        epoch = this.#mergeEpoch(a, b);
        const l = lca(this.dag, a, b);
        state = this.datatype.merge3(this.dag.get(l).state, this.dag.get(a).state, this.dag.get(b).state);
      }
      const c = this.dag.add({ parents: localParents, op, state });
      this.epochOf.set(c.id, epoch);
      const g = this.#index(c);
      if (g !== wc.gid) throw new Error(`content-address mismatch: recomputed ${g} != wire ${wc.gid}`);
      added++;
    }
    if (added > 0) this.#refresh();
    return added;
  }

  /** Merge this replica's head with the (now-local) commit `gid`: fast-forward
   *  if one subsumes the other, else a head-sync merge through the unique lca. */
  mergeWithGid(gid) {
    const b = this.byGid.get(gid);
    if (b === undefined) throw new Error(`mergeWithGid: ${gid} not present (ingest first)`);
    const a = this.#headId;
    if (a === b) return this.headGid;
    if (this.dag.isAncestor(a, b)) { this.#headId = b; this.#refresh(); return this.headGid; }
    if (this.dag.isAncestor(b, a)) return this.headGid;
    const epoch = this.#mergeEpoch(a, b);
    const l = lca(this.dag, a, b);
    const merged = this.datatype.merge3(this.dag.get(l).state, this.dag.get(a).state, this.dag.get(b).state);
    const c = this.dag.add({ parents: [a, b], op: null, state: merged });
    this.epochOf.set(c.id, epoch);
    this.#index(c);
    this.#headId = c.id;
    this.#refresh();
    return this.headGid;
  }

  /** Roster membership: declare `name` a member of the closed replica set the
   *  stability certificate quantifies over. In a separate-store world a replica
   *  is otherwise only known once you ingest one of its ops; the transport calls
   *  this when a peer JOINS, so compactStable can REFUSE for a member never
   *  heard from (the open-membership / not-heard-from breaker). */
  register(name) { this.registered.add(name); }

  /** The certified stable cut over the registered (rostered) replica set. */
  stableCut() { return stableCut(this.dag, this.#headId, [...this.registered], this.name); }

  /** CERTIFIED STATE GC (src/runtime.js Replica.compactStable, over the separate
   *  store): compact at the largest cut this replica can PROVE from its frontier.
   *  Refuses (no-op) when the certificate is incomplete. Opens a new epoch.
   *  Only for datatypes that provide the compaction hooks. */
  compactStable(opts) {
    if (typeof this.datatype.compact !== 'function' || typeof this.datatype.remapState !== 'function') {
      return { compacted: false, reason: 'datatype does not support state compaction (needs compact + remapState)' };
    }
    const { complete, meet, missing } = this.stableCut();
    if (!complete) {
      return { compacted: false, missing,
        reason: `certificate absent: not heard from ${missing.join(', ')} since the cut` };
    }
    const settledIds = insertIds(meet);
    if (settledIds.size === 0) return { compacted: false, reason: 'the certified stable cut is empty' };
    // A datatype may shape its own cut from the certified meet (peritext:
    // settled deletes + settled mark mids, src/compact-peritext.js); either
    // way every in-flight field is empty, discharged by the certificate.
    const cut = typeof this.datatype.cutFromMeet === 'function'
      ? this.datatype.cutFromMeet(meet)
      : { settledIds, inflight: [] };
    const { state, translate, stats } = this.datatype.compact(this.head.state, cut, opts);
    if (stats.symbolsAfter === stats.symbolsBefore
        && !(stats.recordsDropped > 0 || stats.markPairsDropped > 0)) {
      return { compacted: false, reason: 'nothing to compact at this cut', stats };
    }
    this.epochs.push(translate);
    const newEpoch = this.epochOf.get(this.#headId) + 1;
    const c = this.dag.add({ parents: [this.#headId], op: null, state });
    this.epochOf.set(c.id, newEpoch);
    this.#index(c);
    this.#headId = c.id;
    this.#refresh();
    return { compacted: true, head: c, stats, cutSize: settledIds.size, epoch: newEpoch };
  }

  /** COMMIT GC (src/gc.js keep-set) over this replica's own DAG. Keeps the
   *  upward closure of the pairwise meets of `headIds` (default: this head plus
   *  the frontier's per-replica evidence commits -- the positions future
   *  head-sync merges take LCAs against), pruning history strictly below that
   *  horizon. Sound under the same discipline as the shared-store gc: head-sync
   *  merges only, closed membership (src/gc.js). Also prunes the content-id and
   *  epoch indexes of dropped commits. Returns { kept, dropped }. */
  gc(headIds) {
    const heads = headIds ?? [this.#headId, ...[...this.frontier.values()].map((e) => e.id)];
    const res = runGc(this.dag, heads);
    for (const cid of [...this.gid.keys()]) {
      if (!this.dag.has(cid)) {
        this.byGid.delete(this.gid.get(cid));
        this.gid.delete(cid);
        this.epochOf.delete(cid);
      }
    }
    return res;
  }

  /** Whole-state snapshot bytes (a cost probe / bulk-catch-up baseline).
   *  Datatype-generic: the encoded state (or fingerprint) as UTF-8 JSON. */
  snapshotBytes() {
    const enc = typeof this.datatype.encodeState === 'function'
      ? this.datatype.encodeState(this.head.state)
      : (this.datatype.fingerprint ? this.datatype.fingerprint(this.head.state) : [...this.head.state]);
    return new TextEncoder().encode(JSON.stringify(enc)).length;
  }

  /** Total live coordinate symbols (the state-size probe compaction shrinks).
   *  Only for datatypes that expose the cost probe (e.g. embedRGA). */
  symbolCount() {
    if (typeof this.datatype.symbolCount !== 'function') {
      throw new Error('datatype has no symbolCount cost probe');
    }
    return this.datatype.symbolCount(this.head.state);
  }
}

/** ONE bidirectional sync round between two DistributedReplicas (helper): each
 *  computes the other's delta from the pre-merge frontiers, both ingest, both
 *  merge their head with the other's advertised head. After it returns both
 *  stores hold every commit and carry equal reads (unless the pair criss-crosses
 *  or straddles epochs, which the caller's transport defers). */
export function syncReplicas(a, b) {
  const hasA = a.ancestryGids(), hasB = b.ancestryGids();
  const toB = a.delta(hasB), toA = b.delta(hasA);
  const aHead = a.headGid, bHead = b.headGid;
  b.ingest(toB); a.ingest(toA);
  b.mergeWithGid(aHead); a.mergeWithGid(bHead);
}
