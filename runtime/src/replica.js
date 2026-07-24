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
import { mcas } from './lca.js';
import { runGc } from './gc.js';
import { frontierOf, stableCut, insertIds } from './frontier.js';
import { commitContentId, contentId } from './hash.js';
import { compactibleEmbedRGA } from './compact.js';

// A compaction CUT rides the wire as a hint (never hashed) so a peer can
// recompute the epoch's translate deterministically (Case 1). Cuts hold Set
// fields (settledIds, settledMarkMids) and plain arrays; convert Sets both ways
// datatype-agnostically. The recomputed state's fingerprint is verified against
// the compact commit before the translate is trusted, so a wrong/forged cut is
// caught, not mislifted.
export function cutToWire(cut) {
  const w = {};
  for (const [k, v] of Object.entries(cut)) w[k] = (v instanceof Set) ? { $set: [...v] } : v;
  return w;
}
export function cutFromWire(w) {
  const cut = {};
  for (const [k, v] of Object.entries(w)) cut[k] = (v && typeof v === 'object' && Array.isArray(v.$set)) ? new Set(v.$set) : v;
  return cut;
}

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
    this.authors = new Set([name]);     // replica ids that have AUTHORED a commit here
    this.epochs = [null];               // e -> translate(epoch e-1 -> e) closure
    this.epochBase = new Map();         // local id -> pruned parent's gid (epoch bases)
    this.epochOf = new Map();           // local id -> epoch number
    // CROSS-EPOCH LIFT (Case 1, #97 lazy translation): to lift an older-epoch
    // state on ingest a replica needs each epoch's translate CLOSURE, which is
    // not serializable. It is recomputed deterministically from the compact
    // commit's parent state + the CUT that produced it (shipped as a non-hashed
    // hint, verified by fingerprint). compactCut carries the cut; epochOwner
    // records which compact commit opened each epoch here, so a SECOND, DIFFERENT
    // compaction claiming the same epoch (Case 2, incomparable cuts) marks the
    // epoch CONFLICTED and any lift through it is refused rather than mislifted.
    this.compactCut = new Map();        // compact commit local id -> cut used
    this.epochOwner = new Map();        // epoch number -> the compact commit id that opened it here
    this.epochConflict = new Set();     // epochs seen opened by >1 distinct compaction (Case 2)
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

  /** Apply a BATCH of ops as ONE commit (the group-op commit the editor batches
   *  into): the whole list is applied in a single transient pass (applyBatch,
   *  proven == folding apply) and sealed under one seq. The commit's op payload
   *  IS the op array, which the content-id folds in like any payload, so `delta`
   *  ships it verbatim and `ingest` replays it via applyBatch with no wire or
   *  hash change. Zero ops: no-op. One op: a canonical single-op commit (byte-
   *  identical wire to commit()), so single ops never take the array shape. */
  commitBatch(ops) {
    if (ops.length === 0) return this.headGid;
    if (ops.length === 1) return this.commit(ops[0]);
    const state = this.#applyOps(this.head.state, ops);
    const c = this.dag.add({
      parents: [this.#headId], op: { replica: this.name, seq: this.seq++, payload: ops }, state });
    this.epochOf.set(c.id, this.epochOf.get(this.#headId));
    this.#index(c);
    this.#headId = c.id;
    this.#refresh();
    return this.gid.get(c.id);
  }

  /** Apply an op payload (single op, or an op ARRAY = a batch). applyBatch is
   *  proven == folding apply, so the state is identical whichever a peer uses;
   *  content-address determinism does not depend on the choice (authored ids
   *  hash the payload, not the state). */
  #applyOps(state, payload) {
    if (!Array.isArray(payload)) return this.datatype.apply(state, payload);
    return typeof this.datatype.applyBatch === 'function'
      ? this.datatype.applyBatch(state, payload)
      : payload.reduce((s, op) => this.datatype.apply(s, op), state);
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
      if (c.parents.length === 0 && !this.epochBase.has(cid)) continue; // root shared, never shipped
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
      const eb = this.epochBase.get(cid);
      if (c.parents.length === 1 || eb) {
        const wire = { gid: this.gid.get(cid), kind: 'compact',
          parents: eb ? [eb] : parents,
          epoch: this.epochOf.get(cid), state: this.datatype.encodeState(c.state) };
        // ship the cut so the peer can recompute this epoch's translate and
        // lift its own older-epoch edits across it (Case 1). Absent for an
        // epoch base whose parent is pruned (the peer bootstraps, never lifts).
        const cut = this.compactCut.get(cid);
        if (cut && !eb) wire.cut = cutToWire(cut);
        return wire;
      }
      return { gid: this.gid.get(cid), kind: 'merge', parents };
    });
  }

  // ---- CROSS-EPOCH LIFT (Case 1, #97 lazy translation) ---------------------
  // Merge two heads possibly at different epochs by lifting the lower-epoch
  // side (and the LCA base) into the newer epoch, record by record, through the
  // per-epoch translate maps. Identity when nobody compacted, so single-epoch
  // merges are unchanged. Refuses (throws) when a translate on the lift path is
  // missing or conflicted -- incomparable-cut compaction (Case 2) stays the
  // deferred protocol half, faithfully mirroring what #97 leaves open.

  /** On ingesting a compaction, obtain this epoch's translate so future
   *  cross-epoch merges can lift across it. Recompute compact(parentState, cut)
   *  and verify it reproduces the shipped state (a wrong/forged cut is caught
   *  by the fingerprint, never trusted). A DIFFERENT compaction already owning
   *  this epoch means incomparable cuts (Case 2): mark it CONFLICTED so any
   *  lift through it refuses. */
  #absorbEpoch(epoch, cid, parentState, wireCut, compactState) {
    const owner = this.epochOwner.get(epoch);
    if (owner === cid) return;                              // already absorbed
    if (owner !== undefined) { this.epochConflict.add(epoch); return; } // Case 2
    if (!wireCut || typeof this.datatype.compact !== 'function') return; // cannot recompute: no lift
    const cut = cutFromWire(wireCut);
    let rec;
    try { rec = this.datatype.compact(parentState, cut); } catch { return; }
    if (this.datatype.fingerprint(rec.state) !== this.datatype.fingerprint(compactState)) return;
    this.epochs[epoch] = rec.translate;
    this.epochOwner.set(epoch, cid);
    this.compactCut.set(cid, cut);
  }

  /** Lift a state coded in epoch `from` up to epoch `to` (identity if equal);
   *  null if any epoch on the path lacks a translate or is conflicted. */
  #liftState(state, from, to) {
    let s = state;
    for (let e = from + 1; e <= to; e++) {
      if (this.epochConflict.has(e) || !this.epochs[e]) return null;
      s = this.datatype.remapState(s, this.epochs[e]);
    }
    return s;
  }

  /** The merged state + epoch for heads a, b: lift the lower side and the LCA
   *  base into eT = max(epochs), then merge3. Throws if the lift is unavailable
   *  (Case 2 / a not-yet-absorbed epoch). */
  #mergeStates(a, b) {
    const eA = this.epochOf.get(a), eB = this.epochOf.get(b);
    const eT = Math.max(eA, eB);
    const base = this.#baseFor([a], b);
    const lBase = this.#liftState(base.state, base.epoch, eT);
    const lA = this.#liftState(this.dag.get(a).state, eA, eT);
    const lB = this.#liftState(this.dag.get(b).state, eB, eT);
    if (lBase === null || lA === null || lB === null) {
      throw new Error(
        `cross-epoch merge (${eA} vs ${eB}): a translate on the lift path is ` +
        `missing or conflicted; incomparable-cut compaction is the deferred ` +
        `protocol half (README, stability-vc-note section 8)`);
    }
    return { state: this.datatype.merge3(lBase, lA, lB), epoch: eT };
  }

  /** Ingest a delta: add each missing commit, recomputing state (apply/merge3)
   *  except compaction commits (state inline, datatype-decoded, SHA-gated). The
   *  recomputed gid must equal the wire gid (content-address gate). */
  ingest(wireCommits) {
    let added = 0;
    for (const wc of wireCommits) {
      if (this.byGid.has(wc.gid)) continue;
      const localParents = wc.parents.map((g) => this.byGid.get(g));
      if (localParents.some((p) => p === undefined)
          && !(wc.kind === 'compact' && wc.parents.length === 1)) {
        throw new Error(`ingest: unknown parent for ${wc.gid} (delta not ancestor-closed)`);
      }
      let op = null, state, epoch;
      if (wc.kind === 'op') {
        op = { replica: wc.op.replica, seq: wc.op.seq, payload: wc.payload };
        state = this.#applyOps(this.dag.get(localParents[0]).state, wc.payload);
        epoch = this.epochOf.get(localParents[0]);
        this.registered.add(wc.op.replica);
        this.authors.add(wc.op.replica);
      } else if (wc.kind === 'compact') {
        if (localParents[0] === undefined) {
          // EPOCH-BASE BOOTSTRAP: a compact commit whose parent was pruned
          // below a settled cut. Its content id is verifiable WITHOUT the
          // parent (hash({compact, p, fp}): p is the parent's gid STRING from
          // the wire, fp recomputes from the inline state), so the content
          // gate holds; structurally it enters as an epoch root (parents [],
          // the wire parent kept for identity/serialization). This is what
          // lets a fresh peer join a pruned history at O(document) instead
          // of replaying genesis.
          if (!Number.isInteger(wc.epoch)) throw new Error('epoch base without an epoch');
          state = this.datatype.decodeState(wc.state);
          const c = this.dag.add({ parents: [], op: null, state });
          this.epochBase.set(c.id, wc.parents[0]); // pruned parent's gid: hash + re-serialization
          this.epochOf.set(c.id, wc.epoch);
          while (this.epochs.length <= wc.epoch) this.epochs.push(null);
          const g = commitContentId({ parents: [null], op: null, state }, [wc.parents[0]],
            { fingerprint: this.datatype.fingerprint, hash: this.hash });
          if (g !== wc.gid) throw new Error(`content-address mismatch: recomputed ${g} != wire ${wc.gid}`);
          this.gid.set(c.id, g); this.byGid.set(g, c.id);
          added++;
          continue;
        }
        // compact with a PRESENT parent. Add the commit, then try to obtain
        // this epoch's translate (recomputed from the parent state + the
        // shipped cut) so future cross-epoch merges can LIFT across it (Case 1).
        state = this.datatype.decodeState(wc.state);
        epoch = this.epochOf.get(localParents[0]) + 1;
        while (this.epochs.length <= epoch) this.epochs.push(null);
        const cc = this.dag.add({ parents: localParents, op: null, state });
        this.epochOf.set(cc.id, epoch);
        const gc = this.#index(cc);
        if (gc !== wc.gid) throw new Error(`content-address mismatch: recomputed ${gc} != wire ${wc.gid}`);
        this.#absorbEpoch(epoch, cc.id, this.dag.get(localParents[0]).state, wc.cut, state);
        added++;
        continue;
      } else { // merge
        const [a, b] = localParents;
        const r = this.#mergeStates(a, b); // lifts the lower-epoch side (Case 1) or throws (Case 2)
        epoch = r.epoch; state = r.state;
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
   *  if one subsumes the other, else a head-sync merge whose LCA slot is the
   *  unique MCA, or the VIRTUAL base when the pair criss-crosses (#90). */
  mergeWithGid(gid) {
    const b = this.byGid.get(gid);
    if (b === undefined) throw new Error(`mergeWithGid: ${gid} not present (ingest first)`);
    const a = this.#headId;
    if (a === b) return this.headGid;
    // PRISTINE ADOPT: a replica that holds only the shared root (never
    // authored, never merged) may not share ancestry with a PRUNED history
    // (its chain starts at an epoch base, not the root). Nothing local can
    // be lost, so adopt the target head outright.
    const headC = this.dag.get(a);
    if (this.seq === 0 && headC.parents.length === 0 && !this.epochBase.has(a) && headC.op === null) {
      this.#headId = b; this.#refresh(); return this.headGid;
    }
    if (this.dag.isAncestor(a, b)) { this.#headId = b; this.#refresh(); return this.headGid; }
    if (this.dag.isAncestor(b, a)) return this.headGid;
    const { state: merged, epoch } = this.#mergeStates(a, b); // Case-1 lift, or throw (Case 2)
    const c = this.dag.add({ parents: [a, b], op: null, state: merged });
    this.epochOf.set(c.id, epoch);
    this.#index(c);
    this.#headId = c.id;
    this.#refresh();
    return this.headGid;
  }

  // ---- VIRTUAL LCAs (#90): the recursive-merge rule of the mechanized
  // construction (sal-mrdts.tex 14; Lean: Step3V / mca_events_cover /
  // virtualLCAState_canonical, all kernel-clean). When a head pair has
  // several maximal common ancestors (a criss-cross), the base state for
  // the LCA slot is the FOLD of the antichain: start from one member, and
  // at each step three-way-merge the accumulator with the next member over
  // the recursively resolved base of the sub-pair. The covering
  // proposition makes the fold's event set EXACTLY the head intersection,
  // and for join-lemma datatypes (all of ours) the resulting state is
  // canonical for that set, so the fold order cannot affect the result;
  // sorting by content id just fixes the computation deterministically
  // across replicas. Single-MCA shortcuts are machine-refuted
  // (t1f_pick_*_resurrects_*): picking one member resurrects deletes.
  // Scratch states are transient (never committed, never ancestors).

  /** #baseState plus the epoch its coordinates are coded in (the MCA antichain
   *  shares one epoch, enforced by #baseState's guard). The lift raises this
   *  base to the merge's target epoch. */
  #baseFor(S, w) {
    const m = S.length === 1 ? mcas(this.dag, S[0], w) : this.#mcasOfSet(S, w);
    if (m.length === 0) throw new Error(`no common ancestor of [${S}] and ${w}`);
    return { state: this.#baseState(S, w), epoch: this.epochOf.get(m[0]) };
  }

  /** Base state for the LCA slot of a merge between the union-ancestry of
   *  the id set S and the commit w: the unique MCA's state, or the virtual
   *  fold of the MCA antichain. */
  #baseState(S, w) {
    const m = S.length === 1 ? mcas(this.dag, S[0], w) : this.#mcasOfSet(S, w);
    if (m.length === 0) throw new Error(`no common ancestor of [${S}] and ${w}`);
    if (m.length === 1) return this.dag.get(m[0]).state;
    // cross-epoch antichains are not resolvable (epochs are linearized;
    // members of one epoch segment share the segment's compact base)
    const e0 = this.epochOf.get(m[0]);
    for (const x of m) {
      if (this.epochOf.get(x) !== e0) throw new Error('cross-epoch merge: virtual base spans epochs');
    }
    const sorted = [...m].sort((x, y) => (this.gid.get(x) < this.gid.get(y) ? -1 : 1));
    let acc = this.dag.get(sorted[0]).state;
    const support = [sorted[0]];
    for (let k = 1; k < sorted.length; k++) {
      const mi = sorted[k];
      acc = this.datatype.merge3(this.#baseState(support, mi), acc, this.dag.get(mi).state);
      support.push(mi);
    }
    return acc;
  }

  /** Maximal common ancestors of (union ancestry of the id set S) and w:
   *  the set form the covering proposition is stated over. */
  #mcasOfSet(S, w) {
    const A = new Set();
    for (const s of S) for (const x of this.dag.ancestorSet(s)) A.add(x);
    const B = this.dag.ancestorSet(w);
    const ca = new Set();
    for (const x of A) if (B.has(x)) ca.add(x);
    const nonMax = new Set();
    for (const c of ca) for (const p of this.dag.get(c).parents) if (ca.has(p)) nonMax.add(p);
    return [...ca].filter((c) => !nonMax.has(c));
  }

  /** Roster membership: declare `name` a member of the closed replica set the
   *  stability certificate quantifies over. In a separate-store world a replica
   *  is otherwise only known once you ingest one of its ops; the transport calls
   *  this when a peer JOINS, so compactStable can REFUSE for a member never
   *  heard from (the open-membership / not-heard-from breaker). */
  register(name) { this.registered.add(name); }

  /** Drop `name` from the roster IFF it never AUTHORED a commit here. A
   *  joined-then-left lurker holds no ops the stability cut must wait for
   *  (if it returns and writes, the epoch gate handles it); a WRITER stays
   *  registered conservatively (the GC-horizon-vs-offline-peers edge).
   *  Returns true if dropped. */
  unregister(name) {
    if (name === this.name || this.authors.has(name)) return false;
    return this.registered.delete(name);
  }

  /** FORGET `name` entirely: drop it from BOTH the roster and the authors set,
   *  even if it authored. Unlike `unregister` (which conservatively keeps
   *  writers), this LIFTS the stability-cut horizon that a departed author
   *  otherwise pins at its last-synced position -- the deliberate operator- or
   *  lease-driven answer to "an offline writer stalls the GC". SOUNDNESS: the
   *  cut (and epoch-base prune) may now settle ABOVE `name`'s evidence, so
   *  `name` must not return and merge a delta against its stale head; on
   *  return it re-bootstraps from the epoch base as a FRESH peer (pristine
   *  adopt), forfeiting any edits it authored offline and never shared. That
   *  data-loss tradeoff is the price of forgetting, and callers surface it.
   *  Returns true if the roster changed. */
  forget(name) {
    if (name === this.name) return false;
    this.authors.delete(name);
    return this.registered.delete(name);
  }

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
    const newEpoch = this.epochOf.get(this.#headId) + 1;
    this.epochs[newEpoch] = translate;
    const c = this.dag.add({ parents: [this.#headId], op: null, state });
    this.epochOf.set(c.id, newEpoch);
    this.#index(c);
    // remember the cut (for re-shipping + peers' translate recompute) and that
    // THIS compact commit owns newEpoch here (Case 2 conflict detection)
    this.compactCut.set(c.id, cut);
    this.epochOwner.set(newEpoch, c.id);
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
        this.epochBase.delete(cid);
        this.compactCut.delete(cid); // epochs[]/epochOwner stay: keyed by epoch, still valid for lifts
      }
    }
    return res;
  }

  /** What a SAVE costs: the datatype's run-table-backed probe when it has
   *  one (peritext, embed), else the snapshot JSON. The honest durable
   *  number, vs snapshotBytes' in-memory representation cost. */
  saveBytes() {
    return typeof this.datatype.saveBytes === 'function'
      ? this.datatype.saveBytes(this.head.state)
      : this.snapshotBytes();
  }

  /** PRUNE HISTORY BELOW THE NEWEST COMPACT COMMIT, turning it into an
   *  EPOCH BASE (parents [], wire parent kept for its content id). Gated on
   *  the certified condition for forgetting: the stability cut is complete
   *  AND every registered replica's evidence has reached the compact epoch,
   *  so no registered peer can ever need the dropped commits for a delta or
   *  an LCA again; fresh peers bootstrap from the base (delta ships it,
   *  ingest verifies it parent-free, a pristine replica adopts it). Returns
   *  { pruned, epoch } or { pruned: 0, reason }. */
  pruneToEpochBase() {
    let K = null, eK = -1;
    for (const cid of this.dag.ancestorSet(this.#headId)) {
      const c = this.dag.get(cid);
      const isCompact = c.op === null && (c.parents.length === 1 || this.epochBase.has(cid));
      const e = this.epochOf.get(cid);
      if (isCompact && e > eK) { K = cid; eK = e; }
    }
    if (K === null) return { pruned: 0, reason: 'no compact commit in ancestry' };
    const c = this.dag.get(K);
    if (c.parents.length === 0) return { pruned: 0, reason: 'already the epoch base' };
    const sc = this.stableCut();
    if (!sc.complete) return { pruned: 0, reason: `cut incomplete: missing ${sc.missing.join(',') || '?'}` };
    // Every REGISTERED replica's evidence must have reached the compact epoch,
    // so no registered peer can ever need the dropped commits. Quantify over
    // the roster, not the raw frontier: a FORGOTTEN author's stale evidence no
    // longer gates the prune (it will re-bootstrap from the base on return).
    // When the cut is complete, every registered non-self peer has a frontier
    // entry (that is what completeness means).
    for (const rep of this.registered) {
      if (rep === this.name) continue;
      const e = this.frontier.get(rep);
      if (e && (this.epochOf.get(e.id) ?? 0) < eK) {
        return { pruned: 0, reason: `evidence from ${rep} still below epoch ${eK}` };
      }
    }
    const below = this.dag.ancestorSet(c.parents[0]); // reflexive: everything at/under K's parent
    this.epochBase.set(K, this.gid.get(c.parents[0]));
    this.dag.sever(K);
    let pruned = 0;
    for (const cid of below) {
      if (!this.dag.has(cid)) continue;
      this.dag.remove(cid);
      const g = this.gid.get(cid);
      this.byGid.delete(g); this.gid.delete(cid); this.epochOf.delete(cid); this.epochBase.delete(cid);
      this.compactCut.delete(cid);
      pruned++;
    }
    this.#refresh();
    return { pruned, epoch: eK };
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
