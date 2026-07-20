// Node: a p2p replica over a SEPARATE commit store, SHA-256 content-addressed.
//
// This is the runtime's sync.js `Peer` (separate-store gossip: delta/ingest/
// merge over the wire) UNIFIED with runtime.js `Replica`'s certified state GC
// (compactStable via the evidence frontier), which sync.js's Peer lacks. #95
// needs both on one object AND a real SHA content-id (sync.js bakes a model FNV
// hash in a private method). Since runtime/src is import-only, the glue lives
// here; every load-bearing primitive is imported from the verified runtime:
//   Dag (commit store), lca (criss-cross gate), frontierOf/stableCut/insertIds
//   (the ONE frontier), compactEliasDelta/remapState (the state GC),
//   embed RGA + serialize (the datatype + snapshot).
// test/node.test.js cross-checks a Node against sync.js's Peer on the same op
// stream (identical reads + convergence), so this reimplementation is pinned to
// the reference, not merely plausible.
//
// CONTENT ADDRESSING (SHA, the #95 swap). Every commit is named by the
// SHA-256 of its canonical content, a Merkle DAG folding in parent ids:
//   root       -> sha({root:true})                     (shared by construction)
//   authored   -> sha({p:[parentGid], replica, seq, payload})
//   merge      -> sha({p: sorted([parentGids])})       (merge(a,b)==merge(b,a))
//   compaction -> sha({compact:true, p:[parentGid], fp}) (fp = state fingerprint)
// The same logical commit gets the same id on every peer and on disk, so the
// wire dedups and git persistence content-addresses with ONE hash.
//
// EPOCHS / COMPACTION. compactStable opens a new epoch (re-coded coordinates),
// exactly as runtime.js does. Merges are same-epoch only; a cross-epoch merge
// throws (the demo keeps epochs consistent with a settled BARRIER where every
// converged peer compacts identically -- concurrent divergent compaction is the
// runtime's own deferred protocol half). Compaction commits ship their state
// inline (they cannot be recomputed from a parent); the SHA gate still bounds
// trust in that state.

import { Dag } from '../../runtime/src/dag.js';
import { lca } from '../../runtime/src/lca.js';
import { frontierOf, stableCut, insertIds } from '../../runtime/src/frontier.js';
import { compactibleEmbedRGA } from '../../runtime/src/compact.js';
import { encode as encodeSnapshot } from '../../runtime/src/serialize.js';
import { contentId } from './hash.js';

const ROOT_CONTENT = { root: true };

export class Node {
  #headId;
  constructor(datatype = compactibleEmbedRGA, name = 'n0') {
    this.datatype = datatype;
    this.name = name;
    this.dag = new Dag();
    this.seq = 0;
    this.gid = new Map();               // local id -> content id (sha)
    this.byGid = new Map();             // content id -> local id
    this.registered = new Set([name]);  // replica ids heard of
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
    if (commit.parents.length === 0) return contentId(ROOT_CONTENT);
    const pg = commit.parents.map((p) => this.gid.get(p));
    if (commit.op !== null) {
      return contentId({ p: pg, replica: commit.op.replica, seq: commit.op.seq, payload: commit.op.payload });
    }
    if (commit.parents.length === 1) {           // compaction commit
      return contentId({ compact: true, p: pg, fp: this.datatype.fingerprint(commit.state) });
    }
    return contentId({ p: pg.slice().sort() });  // merge commit
  }
  #index(commit) {
    const g = this.#gidOf(commit);
    this.gid.set(commit.id, g);
    this.byGid.set(g, commit.id);
    return g;
  }
  #refresh() { this.frontier = frontierOf(this.dag, this.#headId); }

  /** Apply one op on this node's own current head (the only local mutator). */
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
   *  before-children). Op payload for authored, parent refs for merges, inline
   *  state for compaction commits (not recomputable from a parent). */
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
          epoch: this.epochOf.get(cid),
          state: [...c.state.entries()].map(([id, r]) => [id, r.coord, r.el]) };
      }
      return { gid: this.gid.get(cid), kind: 'merge', parents };
    });
  }

  #mergeEpoch(p0, p1) {
    const e0 = this.epochOf.get(p0), e1 = this.epochOf.get(p1);
    if (e0 !== e1) {
      throw new Error(
        `cross-epoch merge (${e0} vs ${e1}): the demo linearizes compaction ` +
        `epochs with a settled barrier; concurrent divergent compaction is the ` +
        `deferred protocol half (runtime README, embed-recoding-note section 6)`);
    }
    return e0;
  }

  /** Ingest a delta: add each missing commit, recomputing state (apply/merge3)
   *  except compaction commits (state inline, SHA-gated). The recomputed gid
   *  must equal the wire gid (content-address gate). */
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
        state = new Map(wc.state.map(([id, coord, el]) => [id, Object.freeze({ coord, el })]));
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

  /** Merge this node's head with the (now-local) commit `gid`: fast-forward if
   *  one subsumes the other, else a head-sync merge through the unique lca. */
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
   *  certificate quantifies over. In a separate-store world a replica is
   *  otherwise only known once you ingest one of its ops; the transport calls
   *  this when a peer JOINS the room, so compactStable can REFUSE for a member
   *  it has never heard from (the open-membership / not-heard-from breaker). */
  register(name) { this.registered.add(name); }

  /** The certified stable cut over the registered (rostered) replica set. */
  stableCut() { return stableCut(this.dag, this.#headId, [...this.registered], this.name); }

  /** Certified state GC (runtime.js Replica.compactStable, ported to the
   *  separate store): compact at the largest cut this node can PROVE from its
   *  frontier. Refuses (no-op) when the certificate is incomplete. Opens a new
   *  epoch. */
  compactStable(opts) {
    const { complete, meet, missing } = this.stableCut();
    if (!complete) {
      return { compacted: false, missing,
        reason: `certificate absent: not heard from ${missing.join(', ')} since the cut` };
    }
    const settledIds = insertIds(meet);
    if (settledIds.size === 0) return { compacted: false, reason: 'the certified stable cut is empty' };
    const { state, translate, stats } = this.datatype.compact(
      this.head.state, { settledIds, inflight: [] }, opts); // inflight [] discharged by the cert
    if (stats.symbolsAfter === stats.symbolsBefore) {
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

  /** Whole-state snapshot (serialize.js) and its byte size. */
  snapshot() { return encodeSnapshot(this.head.state); }
  snapshotBytes() { return this.snapshot().length; }

  /** Total live coordinate symbols (the state-size probe compaction shrinks). */
  symbolCount() { return this.datatype.symbolCount(this.head.state); }
}
