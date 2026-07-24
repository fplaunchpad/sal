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
// EPOCHS / CONCURRENT COMPACTION (task #112 phase 3; the validated + mechanized
// epoch diamond, whiteboard/epoch-protocol-note.md section 9,
// Sal/.../EmbedRGA_EpochDiamond.lean). compactStable opens a new epoch (re-coded
// coordinates), and epoch identity is the SETTLED CUT + its certificate, held in
// a CUT-INDEXED DAG (src/epoch.js), not a per-replica integer. A cross-epoch
// merge no longer THROWS: it is the certificate-determined JOIN. Two heads at
// COMPARABLE cuts (one ⊆ the other) merge by lifting the lower side UP into the
// higher (shipped, content-addressed) epoch through its recomputed map (the
// linear-epoch path, byte-identical to the never-compacted twin). Two heads at
// INCOMPARABLE (divergent) cuts merge by op-REPLAY to their common base epoch:
// the JS runtime is id-addressed (an insert carries its anchor's id, and a
// record's coordinate is re-derived from its anchor -- the H3 extension law), so
// lifting an epoch is re-applying id-addressed ops, the id-addressed analogue of
// the Lean/note coordinate-map translation (THE ONE MODELLING GAP, note §9
// "Model limits"; see #joinState). The join cut W = U ∪ V is registered in the
// cut-DAG; a subsequent certified compactStable re-codes the merged head up to a
// cut ⊇ W (compaction frames are only ever MINTED by compactStable and shipped
// content-addressed, never re-derived at merge from divergent local holdings --
// that is what keeps the frame coordination-free). Translation maps are GC'd per
// the A3 DOUBLE certificate (src/epoch.js doubleCertificate); the ack-only
// shortcut is unsound and is refused.

import { Dag } from './dag.js';
import { lca } from './lca.js';
import { runGc } from './gc.js';
import { frontierOf, stableCut, insertIds } from './frontier.js';
import { commitContentId, contentId } from './hash.js';
import { compactibleEmbedRGA } from './compact.js';
import { EpochDag, EPOCH0, cutKey, serializeCut, deserializeCut, doubleCertificate, buildInverseTranslate } from './epoch.js';

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
    this.epochDag = new EpochDag();     // cut-indexed epoch DAG (src/epoch.js)
    this.epochOf = new Map();           // local commit id -> epoch cut key
    const root = this.dag.add({ parents: [], op: null, state: datatype.init() });
    this.epochOf.set(root.id, EPOCH0);
    this.#index(root);
    this.#headId = root.id;
    this.frontier = frontierOf(this.dag, this.#headId);
  }

  get head() { return this.dag.get(this.#headId); }
  get headGid() { return this.gid.get(this.#headId); }
  /** The head's epoch DEPTH (compaction generations; 0 = uncompacted). The full
   *  epoch identity is the cut key `this.epochOf.get(this.#headId)`. */
  get epoch() { return this.epochDag.get(this.epochOf.get(this.#headId)).num; }
  /** The head's epoch cut KEY (the coordinate-addressed cut identity). */
  get epochKey() { return this.epochOf.get(this.#headId); }
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
        // A compaction commit carries its settled CUT (the certificate): the
        // receiver recomputes the epoch's translate map from parentState + cut
        // (note §9.1), never trusting a shipped map. Inline state is kept as the
        // content-address witness (gid is over its fingerprint).
        const node = this.epochDag.get(this.epochOf.get(cid));
        return { gid: this.gid.get(cid), kind: 'compact', parents,
          cut: serializeCut(node.cut), state: this.datatype.encodeState(c.state) };
      }
      return { gid: this.gid.get(cid), kind: 'merge', parents };
    });
  }

  /** Lift a state coded in `fromKey` DOWN to `toKey` (an ancestor cut) by
   *  composing the per-step INVERSE maps along the linear refinement chain
   *  (fromKey -> ... -> toKey). Coordinate translation (not op-replay) is what
   *  makes this sound: it rewrites dead-ancestor prefixes that a re-application
   *  cannot reconstruct (the anchor is dead). Returns null if the chain is not
   *  linear or an inverse map is missing. */
  #toEpoch(state, fromKey, toKey) {
    let s = state, k = fromKey;
    while (k !== toKey) {
      const n = this.epochDag.get(k);
      if (!n || n.parents.length !== 1 || n.translateInv == null) return null;
      s = this.datatype.remapState(s, n.translateInv);
      k = n.parents[0];
    }
    return s;
  }

  /** Lift a state coded in `fromKey` UP to `toKey` (a descendant cut) through the
   *  forward maps. Used ONLY for the LCA, a causal ancestor of both heads whose
   *  records the target epoch's compaction fully saw, so the forward map applies
   *  cleanly (unlike a concurrently-diverged head). Returns null if unavailable. */
  #liftState(state, fromKey, toKey) {
    const maps = this.epochDag.liftChain(fromKey, toKey);
    if (maps === null) return null;
    let s = state;
    for (const m of maps) s = this.datatype.remapState(s, m);
    return s;
  }

  /** THE CROSS-EPOCH JOIN (note §9.2). Merge heads `aId` and `bId`, returning the
   *  merged state and the epoch key it lands in. Same epoch throughout: unchanged
   *  merge3 (byte-identical). Same epoch heads over a lower LCA: lift the LCA UP,
   *  stay compact. Cross-epoch (comparable OR incomparable cuts): lift both heads
   *  DOWN to the LCA's frame through the inverse maps -- coordinate translation is
   *  the sound realization of the note's translation (a forward MAP lift of a
   *  head is unsound here: a divergently-compacted peer renumbered its OWN view,
   *  and a concurrently-minted record this side holds -- unseen by that
   *  compaction, its id possibly inside the cut's id range -- would be squeezed
   *  into a wrong ordinal). The merged head sits at the common base epoch; a later
   *  certified compactStable re-codes it up to a cut ⊇ W (the join cut W = U ∪ V,
   *  registered in the cut-DAG). Compaction frames are minted only by the shipped,
   *  content-addressed compactStable, never re-derived at merge -- that is what
   *  keeps the frame coordination-free. */
  #joinState(aId, bId) {
    const ea = this.epochOf.get(aId), eb = this.epochOf.get(bId);
    const lId = lca(this.dag, aId, bId);
    const el = this.epochOf.get(lId);
    const aState = this.dag.get(aId).state, bState = this.dag.get(bId).state;
    const lState = this.dag.get(lId).state;

    if (ea === eb && ea === el) {
      return { state: this.datatype.merge3(lState, aState, bState), epochKey: ea };
    }
    if (ea === eb) {
      // same-epoch heads, lower LCA: lift the LCA up, stay in the heads' epoch.
      const lUp = this.#liftState(lState, el, ea);
      if (lUp !== null) return { state: this.datatype.merge3(lUp, aState, bState), epochKey: ea };
    }
    // Cross-epoch: lift both heads down to the LCA's frame, merge there.
    const aE = ea === el ? aState : this.#toEpoch(aState, ea, el);
    const bE = eb === el ? bState : this.#toEpoch(bState, eb, el);
    if (aE !== null && bE !== null) {
      if (ea !== eb) this.epochDag.join(ea, eb);
      return { state: this.datatype.merge3(lState, aE, bE), epochKey: el };
    }
    // Last resort: lift everything down to the uncompacted base (epoch 0).
    const a0 = this.#toEpoch(aState, ea, EPOCH0);
    const b0 = this.#toEpoch(bState, eb, EPOCH0);
    const l0 = this.#toEpoch(lState, el, EPOCH0);
    if (a0 === null || b0 === null || l0 === null) {
      throw new Error('cross-epoch merge: an inverse epoch map is unavailable for translation');
    }
    if (ea !== eb) this.epochDag.join(ea, eb);
    return { state: this.datatype.merge3(l0, a0, b0), epochKey: EPOCH0 };
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
      let op = null, state, epochKey;
      if (wc.kind === 'op') {
        op = { replica: wc.op.replica, seq: wc.op.seq, payload: wc.payload };
        state = this.datatype.apply(this.dag.get(localParents[0]).state, wc.payload);
        epochKey = this.epochOf.get(localParents[0]);
        this.registered.add(wc.op.replica);
      } else if (wc.kind === 'compact') {
        // decode the inline state (the content-address witness), and RECOMPUTE
        // this epoch's translate map from parentState + the shipped cut -- the
        // certificate travels, the map does not (note §9.1). The gid gate below
        // confirms the recomputed compaction matches the peer's.
        state = this.datatype.decodeState(wc.state);
        const parentKey = this.epochOf.get(localParents[0]);
        const parentState = this.dag.get(localParents[0]).state;
        const cut = deserializeCut(wc.cut);
        // The INVERSE map is built directly from parentState + the decoded state
        // (always available). The FORWARD map is RECOMPUTED from parentState + cut
        // (the certificate) -- best-effort, only the LCA-up lift consults it.
        let translateInv = null, translate = null;
        try { translateInv = buildInverseTranslate(parentState, state); } catch { translateInv = null; }
        if (typeof this.datatype.compact === 'function') {
          try { translate = this.datatype.compact(parentState, cut).translate; } catch { translate = null; }
        }
        // Key by the wire content id (the frame identity, checked below).
        epochKey = this.epochDag.compaction(wc.gid, { settledIds: cut.settledIds ?? new Set(), cut, translate, translateInv, parentKey });
      } else { // merge: the cross-epoch JOIN (or the unchanged same-epoch merge3)
        const [a, b] = localParents;
        const j = this.#joinState(a, b);
        state = j.state; epochKey = j.epochKey;
      }
      const c = this.dag.add({ parents: localParents, op, state });
      this.epochOf.set(c.id, epochKey);
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
    const { state: merged, epochKey } = this.#joinState(a, b);
    const c = this.dag.add({ parents: [a, b], op: null, state: merged });
    this.epochOf.set(c.id, epochKey);
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

  /** GC epoch `key`'s translation map under the A3 DOUBLE certificate (note §9.4,
   *  src/epoch.js `doubleCertificate`; the Lean `mapDrop_sound`). BOTH halves are
   *  required and supplied by the caller (the frontier producer, as for
   *  stableCut's certificate): `everyoneAdvanced` (every registered replica past
   *  epoch e) AND `allHeardOverAckFrontier` (every pre-advance mint heard
   *  everywhere). The ack-ONLY shortcut is UNSOUND and REFUSED here -- an epoch-e
   *  straggler minted before its minter advanced can still arrive and needs the
   *  map (the Lean `a3_ack_only_unsound` FAIL). Returns { dropped, reason }. */
  dropEpochMap(key, certificate = {}) {
    const node = this.epochDag.get(key);
    if (!node) return { dropped: false, reason: `no such epoch ${key}` };
    if (node.translate == null) return { dropped: false, reason: 'no map to drop' };
    if (!doubleCertificate(certificate)) {
      return { dropped: false, reason: 'A3 double certificate incomplete: need '
        + 'everyone-advanced AND all-heard-over-the-ack-frontier (ack-only is unsound)' };
    }
    node.translate = null;
    node.mapDropped = true;
    return { dropped: true, key };
  }

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
    // The INVERSE map (this-epoch coord -> parent-epoch coord) lets a later
    // cross-epoch merge lift this state DOWN to a common frame. Buildable from
    // the pre/post coordinate correspondence; skipped for non-coord-map states.
    let translateInv = null;
    try { translateInv = buildInverseTranslate(this.head.state, state); } catch { translateInv = null; }
    const parentKey = this.epochOf.get(this.#headId);
    const cutSettled = cut.settledIds ?? settledIds;
    // Create the compaction commit, THEN key the epoch by its content id (the
    // FRAME identity). compactStable is the only minter of a compaction frame; it
    // is shipped content-addressed, so every replica that reaches the identical
    // frame (same cut AND same stragglers) shares the identical epoch key.
    const c = this.dag.add({ parents: [this.#headId], op: null, state });
    const newKey = this.#index(c);
    this.epochDag.compaction(newKey, { settledIds: cutSettled, cut, translate, translateInv, parentKey });
    this.epochOf.set(c.id, newKey);
    this.#headId = c.id;
    this.#refresh();
    return { compacted: true, head: c, stats, cutSize: settledIds.size,
      epoch: this.epochDag.get(newKey).num, epochKey: newKey };
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
