// THE FIRST-CLASS DISTRIBUTED REPLICA: ONE object over ONE content-addressed
// commit store with BOTH wire sync AND certified compaction:
//   (a) local ops,
//   (b) delta gossip (ancestryGids / delta / ingest, content-address gated),
//   (c) the certified stability GC (frontier -> stableCut -> compactStable),
//   (d) the keep-set commit GC,
//   (e) SHA content addressing throughout (src/hash.js).
// The p2p demo's Node re-exports this object.
//
// DATATYPE-PARAMETRIC. Everything except state compaction is datatype-agnostic
// (init/apply/merge3/read). A datatype that also provides {compact, remapState,
// encodeState, decodeState} additionally gets the certified state GC; one that
// does not (e.g. orset) gets everything else and refuses compactStable.
//
// EPOCHS / CONCURRENT COMPACTION. compactStable opens a new epoch (re-coded
// coordinates), and epoch identity is the SETTLED CUT + its certificate, held in
// a CUT-INDEXED DAG (src/epoch.js), not a per-replica integer. A cross-epoch
// merge is the certificate-determined JOIN, not a throw. Two heads at
// COMPARABLE cuts (one ⊆ the other) merge by lifting the lower side UP into the
// higher (shipped, content-addressed) epoch through its recomputed map (the
// linear-epoch path, byte-identical to the never-compacted twin). Two heads at
// INCOMPARABLE (divergent) cuts merge by op-REPLAY to their common base epoch:
// the JS runtime is id-addressed (an insert carries its anchor's id, and a
// record's coordinate is re-derived from its anchor, the H3 extension law), so
// lifting an epoch is re-applying id-addressed ops, the id-addressed analogue of
// coordinate-map translation (THE ONE MODELLING GAP; see #joinState). The join
// cut W = U ∪ V is registered in the cut-DAG; a subsequent certified
// compactStable re-codes the merged head up to a cut ⊇ W (compaction frames are
// only ever MINTED by compactStable and shipped content-addressed, never
// re-derived at merge from divergent local holdings, which is what keeps the
// frame coordination-free). Translation maps are GC'd per the DOUBLE certificate
// (src/epoch.js doubleCertificate); the ack-only shortcut is unsound and is
// refused.

import { Dag } from './dag.js';
import { mcas, CrissCrossError } from './lca.js';
import { runGc } from './gc.js';
import { frontierOf, stableCut, insertIds } from './frontier.js';
import { commitContentId, contentId } from './hash.js';
import { compactibleEmbedRGA } from './compact.js';
import { EpochDag, EPOCH0, cutKey, serializeCut, deserializeCut, doubleCertificate, buildInverseTranslate } from './epoch.js';
import { encodeWire, decodeWire } from './wire.js';
import { LamportMint, observePayload, stampOperation } from './mint.js';

export class DistributedReplica {
  #headId;
  constructor(datatype = compactibleEmbedRGA, name = 'r0', { hash = contentId, mint = null } = {}) {
    this.datatype = datatype;
    this.name = name;
    this.hash = hash;
    this.dag = new Dag();
    this.seq = 0;
    this.mint = mint === null ? null : new LamportMint(mint);
    this.gid = new Map();               // local id -> content id (sha)
    this.byGid = new Map();             // content id -> local id
    this.registered = new Set([name]);  // replica ids heard of / rostered
    this.gcClosed = false;              // successful commit GC closes membership
    this.authors = new Set([name]);     // replica ids that have AUTHORED a commit here
    this.epochDag = new EpochDag();     // cut-indexed epoch DAG (src/epoch.js)
    this.epochOf = new Map();           // local commit id -> epoch cut key
    this.epochBase = new Map();         // local id -> pruned parent's gid (parent-free epoch bases)
    this.gcBoundary = new Set();        // certified parent-free commit-GC boundaries
    // Authenticated transport receipts: peer -> epoch key of the peer's
    // advertised current head. These are not datatype commits and do not enter
    // the causal frontier. acknowledgeFetch() accepts a receipt only when this
    // store holds that exact head and recomputes the claimed epoch from it.
    this.fetchAcks = new Map();
    const root = this.dag.add({ parents: [], op: null, state: datatype.init() });
    this.epochOf.set(root.id, EPOCH0);
    this.#index(root);
    this.rootGid = this.gid.get(root.id);
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

  /** Persisted separately from datatype state and commit history, so neither
   * state GC nor commit GC can make a restarted replica reuse an identifier. */
  exportMintState() { return this.mint?.snapshot() ?? null; }

  mintTime() {
    if (this.mint === null) throw new Error('trusted minting requires a unique persistent mint slot');
    return this.mint.next();
  }

  generate(payload) {
    if (this.mint === null) throw new Error('trusted minting requires a unique persistent mint slot');
    return stampOperation(this.mint, payload);
  }

  generateBatch(payloads) { return payloads.map((op) => this.generate(op)); }

  commitGenerated(payload) {
    const generated = this.generate(payload);
    return { gid: this.commit(generated), payload: generated };
  }

  commitGeneratedBatch(payloads) {
    const generated = this.generateBatch(payloads);
    return { gid: this.commitBatch(generated), payload: generated };
  }

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
    const prepared = typeof this.datatype.prepare === 'function'
      ? this.datatype.prepare(this.head.state, payload) : payload;
    const state = this.datatype.apply(this.head.state, prepared);
    if (this.mint !== null) observePayload(this.mint, prepared);
    const c = this.dag.add({
      parents: [this.#headId], op: { replica: this.name, seq: this.seq++, payload: prepared }, state });
    this.epochOf.set(c.id, this.epochOf.get(this.#headId));
    this.#index(c);
    this.#headId = c.id;
    this.#refresh();
    return this.gid.get(c.id);
  }

  /** Seal a whole gesture's op list as ONE group-op commit (applyBatch, proven
   *  == folding apply). The op-array payload folds into the content id opaquely,
   *  so delta/ingest and the hash are unchanged; fewer commits per keystroke ->
   *  a shallower GC horizon. */
  commitBatch(ops) {
    if (ops.length === 0) return this.headGid;
    if (ops.length === 1) return this.commit(ops[0]);
    let state, prepared;
    if (this.datatype.needsPrepare) {
      state = this.head.state;
      prepared = [];
      for (const op of ops) {
        const p = this.datatype.prepare(state, op);
        prepared.push(p);
        state = this.datatype.apply(state, p);
      }
    } else {
      prepared = ops;
      state = this.#applyOps(this.head.state, ops);
    }
    if (this.mint !== null) observePayload(this.mint, prepared);
    const c = this.dag.add({
      parents: [this.#headId], op: { replica: this.name, seq: this.seq++, payload: prepared }, state });
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

  /** The coordinate-bearing sub-state the epoch translate maps act on (the whole
   *  state for embedRGA; the text shadow for peritext). The epoch inverse-translate
   *  builder walks it; without this a peritext cross-epoch merge cannot lift and
   *  DEFERS. */
  #coord(state) { return typeof this.datatype.coordState === 'function' ? this.datatype.coordState(state) : state; }

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
      if (c.parents.length === 0 && !this.epochBase.has(cid) && !this.gcBoundary.has(cid)) continue;
      missing.push(cid);
    }
    missing.sort((x, y) => Number(x.slice(1)) - Number(y.slice(1)));
    return missing.map((cid) => {
      const c = this.dag.get(cid);
      const parents = c.parents.map((p) => this.gid.get(p));
      if (this.gcBoundary.has(cid)) {
        if (typeof this.datatype.encodeState !== 'function'
            || typeof this.datatype.fingerprint !== 'function') {
          throw new Error('GC boundary transfer requires encodeState + fingerprint');
        }
        const gid = this.gid.get(cid), epoch = this.epochOf.get(cid);
        const state = this.datatype.encodeState(c.state);
        const fp = this.datatype.fingerprint(c.state);
        const roster = [...this.registered].sort();
        const proof = contentId({ gcBoundary: true, gid, epoch, fp, roster });
        return { gid, kind: 'base', parents, epoch, fp, roster, proof, state };
      }
      if (c.op !== null) {
        return { gid: this.gid.get(cid), kind: 'op', parents,
          op: { replica: c.op.replica, seq: c.op.seq }, payload: c.op.payload };
      }
      // A compaction commit -- or an EPOCH BASE (a pruned compaction, parent-free
      // locally but shipped with its wire parent gid STRING so the content id
      // still checks) -- carries its settled CUT (the certificate): the receiver
      // recomputes the epoch's translate from parentState + cut, never trusting a
      // shipped map. Inline state is the content-address witness.
      const eb = this.epochBase.get(cid);
      if (c.parents.length === 1 || eb) {
        const node = this.epochDag.get(this.epochOf.get(cid));
        return { gid: this.gid.get(cid), kind: 'compact', parents: eb ? [eb] : parents,
          cut: serializeCut(node?.cut ?? {}), state: this.datatype.encodeState(c.state) };
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

  #mergeInFrame(l, a, b, epochKey) {
    const state = this.datatype.merge3(l, a, b);
    if (typeof this.datatype.auditMergeCoverage === 'function') {
      const evidence = this.datatype.auditMergeCoverage(l, a, b, state);
      if (!evidence.ok) {
        throw new Error(`merge coverage certificate failed: ${JSON.stringify(evidence)}`);
      }
    }
    return { state, epochKey };
  }

  /** THE CROSS-EPOCH JOIN. Merge heads `aId` and `bId`, returning the
   *  merged state and the epoch key it lands in. Same epoch throughout: unchanged
   *  merge3 (byte-identical). Same epoch heads over a lower LCA: lift the LCA UP,
   *  stay compact. Cross-epoch (comparable OR incomparable cuts): lift both heads
   *  DOWN to the LCA's frame through the inverse maps -- coordinate translation is
   *  the sound realization of the translation (a forward MAP lift of a
   *  head is unsound here: a divergently-compacted peer renumbered its OWN view,
   *  and a concurrently-minted record this side holds (unseen by that
   *  compaction, its id possibly inside the cut's id range) would be squeezed
   *  into a wrong ordinal). The merged head sits at the common base epoch; a later
   *  certified compactStable re-codes it up to a cut ⊇ W (the join cut W = U ∪ V,
   *  registered in the cut-DAG). Compaction frames are minted only by the shipped,
   *  content-addressed compactStable, never re-derived at merge, which keeps
   *  the frame coordination-free. */
  #joinState(aId, bId) {
    const ea = this.epochOf.get(aId), eb = this.epochOf.get(bId);
    const aState = this.dag.get(aId).state, bState = this.dag.get(bId).state;
    // The LCA slot is the VIRTUAL base: the unique MCA's state, or the
    // fold of the MCA antichain when the pair criss-crosses (mcas of mcas). It
    // returns the base state AND the epoch its coordinates are coded in, which
    // feeds the epoch lift below exactly as a single LCA would.
    let base;
    try {
      base = this.#baseFor([aId], bId);
    } catch (e) {
      if (!this.datatype.headOnlyMerge || !/no common ancestor/.test(e.message)) throw e;
      // Certified root-free boundaries may disconnect the compressed physical
      // DAG. Peritext's proved merge rule does not inspect LCA payload state.
      if (ea === eb) return this.#mergeInFrame(this.datatype.init(), aState, bState, ea);
      const a0 = this.#toEpoch(aState, ea, EPOCH0);
      const b0 = this.#toEpoch(bState, eb, EPOCH0);
      if (a0 === null || b0 === null) throw new CrissCrossError([aId, bId]);
      this.epochDag.join(ea, eb);
      return this.#mergeInFrame(this.datatype.init(), a0, b0, EPOCH0);
    }
    const el = base.epoch, lState = base.state;

    if (ea === eb && ea === el) {
      return this.#mergeInFrame(lState, aState, bState, ea);
    }
    if (ea === eb) {
      // same-epoch heads, lower LCA: lift the LCA up, stay in the heads' epoch.
      const lUp = this.#liftState(lState, el, ea);
      if (lUp !== null) return this.#mergeInFrame(lUp, aState, bState, ea);
    }
    // Cross-epoch: lift both heads down to the LCA's frame, merge there.
    const aE = ea === el ? aState : this.#toEpoch(aState, ea, el);
    const bE = eb === el ? bState : this.#toEpoch(bState, eb, el);
    if (aE !== null && bE !== null) {
      if (ea !== eb) this.epochDag.join(ea, eb);
      return this.#mergeInFrame(lState, aE, bE, el);
    }
    // Last resort: lift everything down to the uncompacted base (epoch 0).
    const a0 = this.#toEpoch(aState, ea, EPOCH0);
    const b0 = this.#toEpoch(bState, eb, EPOCH0);
    const l0 = this.#toEpoch(lState, el, EPOCH0);
    if (a0 === null || b0 === null || l0 === null) {
      throw new Error('cross-epoch merge: an inverse epoch map is unavailable for translation');
    }
    if (ea !== eb) this.epochDag.join(ea, eb);
    return this.#mergeInFrame(l0, a0, b0, EPOCH0);
  }

  /** Ingest a delta: add each missing commit, recomputing state (apply/merge3)
   *  except compaction commits (state inline, datatype-decoded, SHA-gated). The
   *  recomputed gid must equal the wire gid (content-address gate). */
  ingest(wireCommits) {
    let added = 0;
    let priorGid = null;
    for (const wc of wireCommits) {
      if (wc.gid !== null && this.byGid.has(wc.gid)) { priorGid = wc.gid; continue; }
      const parentGids = wc.parents.map((g) => g === null ? priorGid : g);
      if (parentGids.includes(this.rootGid) && !this.byGid.has(this.rootGid)) {
        const root = this.dag.add({ parents: [], op: null, state: this.datatype.init() });
        this.epochOf.set(root.id, EPOCH0);
        const g = this.#index(root);
        if (g !== this.rootGid) throw new Error('canonical root reconstruction mismatch');
      }
      const localParents = parentGids.map((g) => this.byGid.get(g));
      // an epoch base (a pruned compaction) arrives with its parent ABSENT; its
      // content id verifies WITHOUT the parent, so it is the one allowed exception
      // to ancestor-closure.
      const isEpochBaseWire = wc.kind === 'compact' && wc.parents.length === 1;
      if (localParents.some((p) => p === undefined) && !isEpochBaseWire) {
        throw new Error(`ingest: unknown parent for ${wc.gid} (delta not ancestor-closed)`);
      }
      let op = null, state, epochKey;
      if (wc.kind === 'base') {
        if (typeof this.datatype.decodeState !== 'function'
            || typeof this.datatype.fingerprint !== 'function') {
          throw new Error('GC boundary ingest requires decodeState + fingerprint');
        }
        state = this.datatype.decodeState(wc.state);
        const fp = this.datatype.fingerprint(state);
        if (fp !== wc.fp) throw new Error(`GC boundary fingerprint mismatch for ${wc.gid}`);
        const roster = [...(wc.roster ?? [])].sort();
        const proof = contentId({ gcBoundary: true, gid: wc.gid,
          epoch: wc.epoch, fp, roster });
        if (proof !== wc.proof) throw new Error(`GC boundary certificate mismatch for ${wc.gid}`);
        if (!this.epochDag.has(wc.epoch)) {
          throw new Error(`GC boundary epoch ${wc.epoch} is unavailable; fetch its epoch certificate first`);
        }
        const unknown = roster.filter((r) => !this.registered.has(r));
        if (this.gcClosed && unknown.length > 0) {
          throw new Error(`open-membership after commit GC: boundary introduces ${unknown.join(', ')}`);
        }
        for (const r of roster) this.registered.add(r);
        const c = this.dag.add({ parents: localParents, op: null, state });
        this.gid.set(c.id, wc.gid); this.byGid.set(wc.gid, c.id);
        this.epochOf.set(c.id, wc.epoch); this.gcBoundary.add(c.id);
        priorGid = wc.gid; added++;
        continue;
      } else if (wc.kind === 'op') {
        if (this.gcClosed && !this.registered.has(wc.op.replica)) {
          throw new Error(`open-membership after commit GC: ${wc.op.replica} is not in the closed roster`);
        }
        op = { replica: wc.op.replica, seq: wc.op.seq, payload: wc.payload };
        state = this.#applyOps(this.dag.get(localParents[0]).state, wc.payload);
        epochKey = this.epochOf.get(localParents[0]);
        this.registered.add(wc.op.replica);
        this.authors.add(wc.op.replica);
      } else if (wc.kind === 'compact' && localParents[0] === undefined) {
        // EPOCH-BASE BOOTSTRAP: the parent was pruned below a settled cut. Verify
        // the gid over the wire parent STRING + fingerprint (parent-free but
        // content-gated), enter it as a parent-free base, and register its
        // epochDag node with the shipped cut (its settledIds drive subcut/compare;
        // a pristine peer that adopts it never lifts below it, so no map needed).
        state = this.datatype.decodeState(wc.state);
        const cut = deserializeCut(wc.cut ?? {});
        const cc = this.dag.add({ parents: [], op: null, state });
        this.epochBase.set(cc.id, parentGids[0]);
        const g = commitContentId({ parents: [null], op: null, state }, [parentGids[0]],
          { fingerprint: this.datatype.fingerprint, hash: this.hash });
        if (wc.gid !== null && g !== wc.gid) throw new Error(`content-address mismatch: recomputed ${g} != wire ${wc.gid}`);
        this.gid.set(cc.id, g); this.byGid.set(g, cc.id);
        this.epochDag.compaction(g, { settledIds: cut.settledIds ?? new Set(), cut, parentKey: EPOCH0 });
        this.epochOf.set(cc.id, g);
        priorGid = g; added++;
        continue;
      } else if (wc.kind === 'compact') {
        // decode the inline state (the content-address witness), and RECOMPUTE
        // this epoch's translate map from parentState + the shipped cut: the
        // certificate travels, the map does not. The gid gate below confirms
        // the recomputed compaction matches the peer's.
        state = this.datatype.decodeState(wc.state);
        const parentKey = this.epochOf.get(localParents[0]);
        const parentState = this.dag.get(localParents[0]).state;
        const cut = deserializeCut(wc.cut);
        // The INVERSE map is built directly from parentState + the decoded state
        // (always available). The FORWARD map is RECOMPUTED from parentState + cut
        // (the certificate) -- best-effort, only the LCA-up lift consults it.
        let translateInv = null, translate = null;
        if (typeof this.datatype.inverseTranslate === 'function') {
          translateInv = this.datatype.inverseTranslate(parentState, state, cut);
        } else {
          try { translateInv = buildInverseTranslate(this.#coord(parentState), this.#coord(state)); } catch { translateInv = null; }
        }
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
      if (wc.gid !== null && g !== wc.gid) throw new Error(
        `content-address mismatch (${wc.kind ?? 'legacy'}, parents=${parentGids.join(',')}): recomputed ${g} != wire ${wc.gid}`);
      if (wc.kind === 'op' && this.mint !== null) observePayload(this.mint, wc.payload);
      priorGid = g;
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
    // PRISTINE ADOPT: a replica holding only the shared root (never authored,
    // never merged) may not share ancestry with a PRUNED history (whose chain
    // starts at an epoch base, not the root). Nothing local can be lost, so it
    // adopts the target head outright -- this is how a fresh peer bootstraps
    // from an epoch base at O(document).
    const headC = this.dag.get(a);
    if (this.seq === 0 && headC.op === null && headC.parents.length === 0 && !this.epochBase.has(a)) {
      this.#headId = b; this.#refresh(); return this.headGid;
    }
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
  register(name) {
    if (this.gcClosed && !this.registered.has(name)) {
      throw new Error(`open-membership after commit GC: ${name} must bootstrap through a certified epoch base`);
    }
    this.registered.add(name);
  }

  /** Drop `name` from the roster IFF it never AUTHORED a commit here. A
   *  joined-then-left lurker holds no ops the stability cut must wait for; a
   *  WRITER stays registered conservatively (the GC-horizon-vs-offline edge).
   *  Returns true if dropped. */
  unregister(name) {
    if (name === this.name || this.authors.has(name)) return false;
    return this.registered.delete(name);
  }

  /** FORGET `name` entirely: drop it from BOTH the roster and the authors set,
   *  even if it authored. Unlike `unregister` (which conservatively keeps
   *  writers), this LIFTS the stability-cut horizon a departed author otherwise
   *  pins at its last-synced position -- the operator-directed answer to "an
   *  offline writer stalls the GC". SOUNDNESS: the cut may now settle above
   *  `name`'s evidence, so on return `name` must re-bootstrap as a FRESH peer
   *  (forfeiting un-shared offline edits), not merge a stale-head delta. Returns
   *  true if the roster changed. */
  forget(name) {
    if (name === this.name) return false;
    this.authors.delete(name);
    this.fetchAcks.delete(name);
    return this.registered.delete(name);
  }

  /** Record that `peer` completed a fetch/head-sync round at `headGid`.
   *  The transport authenticates the peer identity. The content-address and
   *  epoch checks below bind the receipt to locally verified DAG material.
   *  Receipts advance monotonically by the epoch cut order. */
  acknowledgeFetch(peer, headGid, epochKey) {
    if (!this.registered.has(peer)) return false;
    const cid = this.byGid.get(headGid);
    if (cid === undefined || this.epochOf.get(cid) !== epochKey) return false;
    const old = this.fetchAcks.get(peer);
    if (old !== undefined && !this.epochDag.subcut(old, epochKey)) return false;
    this.fetchAcks.set(peer, epochKey);
    return true;
  }

  // ---- VIRTUAL LCAs x EPOCH LIFT: the criss-cross-resolving base.
  // The LCA slot of a merge between the union-ancestry of an id set S and a
  // commit w is the unique MCA's state, or the FOLD of the MCA antichain (sorted
  // by content id for cross-replica determinism; recursively resolved
  // sub-bases). #baseFor also returns the epoch the base is coded in, which the
  // epoch join lifts from. When the antichain SPANS EPOCHS (a criss-cross that
  // ALSO straddles a compaction) the members are lifted DOWN to a common lower
  // frame (EPOCH0, reached by the epoch inverse maps) and folded there, rather
  // than deferred -- so a returning offline peer's edits still converge.
  #baseFor(S, w) {
    const m = S.length === 1 ? mcas(this.dag, S[0], w) : this.#mcasOfSet(S, w);
    if (m.length === 0) throw new Error(`no common ancestor of [${S}] and ${w}`);
    const e0 = this.epochOf.get(m[0]);
    const target = m.every((x) => this.epochOf.get(x) === e0) ? e0 : EPOCH0;
    return { state: this.#baseState(S, w, target), epoch: target };
  }

  /** Lift `state` from epoch `from` DOWN to `target` (identity if equal). If the
   *  inverse chain is unavailable the criss-cross is genuinely unresolvable, so
   *  raise CrissCrossError to DEFER. */
  #liftDown(state, from, target, antichain) {
    if (from === target) return state;
    const lifted = this.#toEpoch(state, from, target);
    if (lifted === null) throw new CrissCrossError(antichain);
    return lifted;
  }

  #baseState(S, w, target) {
    const m = S.length === 1 ? mcas(this.dag, S[0], w) : this.#mcasOfSet(S, w);
    if (m.length === 0) throw new Error(`no common ancestor of [${S}] and ${w}`);
    if (m.length === 1) return this.#liftDown(this.dag.get(m[0]).state, this.epochOf.get(m[0]), target, m);
    const sorted = [...m].sort((x, y) => (this.gid.get(x) < this.gid.get(y) ? -1 : 1));
    let acc = this.#liftDown(this.dag.get(sorted[0]).state, this.epochOf.get(sorted[0]), target, m);
    const support = [sorted[0]];
    for (let k = 1; k < sorted.length; k++) {
      const mi = sorted[k];
      acc = this.datatype.merge3(this.#baseState(support, mi, target), acc,
        this.#liftDown(this.dag.get(mi).state, this.epochOf.get(mi), target, m));
      support.push(mi);
    }
    return acc; // coded in `target`
  }

  /** Maximal common ancestors of (union ancestry of id set S) and w. */
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

  /** The certified stable cut over the registered (rostered) replica set. */
  stableCut() { return stableCut(this.dag, this.#headId, [...this.registered], this.name); }

  /** GC epoch `key`'s translation map under the DOUBLE certificate (src/epoch.js
   *  `doubleCertificate`). BOTH halves are required and supplied by the caller
   *  (the frontier producer, as for stableCut's certificate): `everyoneAdvanced`
   *  (every registered replica past epoch e) AND `allHeardOverAckFrontier` (every
   *  pre-advance mint heard everywhere). The ack-ONLY shortcut is UNSOUND and
   *  REFUSED here: an epoch-e straggler minted before its minter advanced can
   *  still arrive and needs the map. Returns { dropped, reason }. */
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

  /** CERTIFIED STATE GC: compact at the largest cut this replica can PROVE from
   *  its frontier. Refuses (no-op) when the certificate is incomplete. Opens a
   *  new epoch. Only for datatypes that provide the compaction hooks. */
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
    if (typeof this.datatype.inverseTranslate === 'function') {
      translateInv = this.datatype.inverseTranslate(this.head.state, state, cut);
    } else {
      try { translateInv = buildInverseTranslate(this.#coord(this.head.state), this.#coord(state)); } catch { translateInv = null; }
    }
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
    // Distributed GC needs evidence from every other roster member.  The old
    // default silently omitted missing frontier entries, which treated absence
    // of evidence as permission to collect.  Match stableCut's refusal rule.
    if (headIds === undefined) {
      const missing = [...this.registered]
        .filter((rep) => rep !== this.name && !this.frontier.has(rep));
      if (missing.length > 0) {
        return { kept: this.dag.size, dropped: 0, refused: true, missing,
          reason: `frontier evidence absent: not heard from ${missing.join(', ')}` };
      }
    }
    const heads = headIds ?? [this.#headId, ...[...this.frontier.values()].map((e) => e.id)];
    const formerParentCount = new Map([...this.dag.values()]
      .map((c) => [c.id, c.parents.length]));
    const res = runGc(this.dag, heads);
    for (const c of this.dag.values()) {
      const oldCount = formerParentCount.get(c.id) ?? 0;
      if (c.parents.length < oldCount && !this.epochBase.has(c.id)) {
        this.gcBoundary.add(c.id);
      }
    }
    if (res.dropped > 0) this.gcClosed = true;
    for (const cid of [...this.gid.keys()]) {
      if (!this.dag.has(cid)) {
        this.byGid.delete(this.gid.get(cid));
        this.gid.delete(cid);
        this.epochOf.delete(cid);
        this.epochBase.delete(cid);
        this.gcBoundary.delete(cid);
      }
    }
    return { ...res, refused: false, missing: [] };
  }

  /** PRUNE HISTORY BELOW THE NEWEST SETTLED COMPACTION, turning it into a
   *  parent-free EPOCH BASE. Its content id is preserved without the parent:
   *  the compaction hash covers the parent's gid STRING + the state fingerprint
   *  (commitContentId), so `ingest` verifies it parent-free. Gated on the
   *  certified condition for forgetting: the stability cut is complete AND every
   *  registered replica's evidence has ADVANCED PAST the compaction's cut
   *  (epochDag.subcut), so no registered peer can need the dropped commits
   *  for a delta or a cross-epoch lift (a returning FORGOTTEN peer re-bootstraps
   *  from the base). Soundness is the model-independent "a settled cut licenses
   *  forgetting" (the stability VC): pruning removes only history BELOW the base;
   *  every future merge lifts down to at most the base. Returns { pruned, epoch }
   *  or { pruned: 0, reason }. */
  pruneToEpochBase() {
    let K = null, kNum = -1;
    for (const cid of this.dag.ancestorSet(this.#headId)) {
      const c = this.dag.get(cid);
      const isCompact = c.op === null && (c.parents.length === 1 || this.epochBase.has(cid));
      if (!isCompact) continue;
      const n = this.epochDag.get(this.epochOf.get(cid));
      if (n && n.num > kNum) { K = cid; kNum = n.num; }
    }
    if (K === null) return { pruned: 0, reason: 'no compaction in ancestry' };
    const c = this.dag.get(K);
    if (c.parents.length === 0) return { pruned: 0, reason: 'already the epoch base' };
    const kKey = this.epochOf.get(K);
    const sc = this.stableCut();
    if (!sc.complete) return { pruned: 0, reason: `cut incomplete: missing ${sc.missing.join(',') || '?'}` };
    // every REGISTERED replica's evidence must have advanced past K's cut, so
    // no registered peer holds a below-K head that would need the pruned history
    for (const rep of this.registered) {
      if (rep === this.name) continue;
      const e = this.frontier.get(rep);
      const authoredPastCut = e && this.epochDag.subcut(kKey, this.epochOf.get(e.id));
      const fetchPastCut = this.fetchAcks.has(rep)
        && this.epochDag.subcut(kKey, this.fetchAcks.get(rep));
      if (!authoredPastCut && !fetchPastCut) {
        return { pruned: 0, reason: `evidence from ${rep} has not reached the compaction cut` };
      }
    }
    const below = this.dag.ancestorSet(c.parents[0]); // reflexive: at/under K's parent
    this.epochBase.set(K, this.gid.get(c.parents[0]));
    this.dag.sever(K); // K becomes parent-free; its STORED gid is left untouched
    let pruned = 0;
    for (const cid of below) {
      if (!this.dag.has(cid)) continue;
      this.dag.remove(cid);
      const g = this.gid.get(cid);
      this.byGid.delete(g); this.gid.delete(cid); this.epochOf.delete(cid); this.epochBase.delete(cid);
      pruned++;
    }
    this.#refresh();
    return { pruned, epoch: kNum };
  }

  /** What a SAVE costs: the datatype's run-table-backed probe when it has one
   *  (peritext, embed), else the snapshot JSON. The honest durable number, vs
   *  snapshotBytes' in-memory representation cost. */
  saveBytes() {
    return typeof this.datatype.saveBytes === 'function'
      ? this.datatype.saveBytes(this.head.state)
      : this.snapshotBytes();
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
  b.ingest(decodeWire(encodeWire({ t: 'delta', c: toB })).c);
  a.ingest(decodeWire(encodeWire({ t: 'delta', c: toA })).c);
  b.mergeWithGid(aHead); a.mergeWithGid(bHead);
  // The successful bidirectional round returns each peer's current advertised
  // head. Record a transport receipt even when the peer authored no new op.
  // acknowledgeFetch validates the head and epoch against local DAG material.
  a.acknowledgeFetch(b.name, b.headGid, b.epochKey);
  b.acknowledgeFetch(a.name, a.headGid, a.epochKey);
}
