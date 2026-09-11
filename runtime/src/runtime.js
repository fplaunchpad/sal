// Replica runtime enforcing the HEAD-SYNC DISCIPLINE by construction.
//
// The only mutating operations the API exposes are:
//   replica.commit(payload)  -- apply an op on YOUR OWN current head;
//   replica.sync(other)      -- join the two CURRENT heads: fast-forward if
//                               one subsumes the other, else a merge commit
//                               via datatype.merge3(lcaState, aState, bState)
//                               with the unique LCA (CrissCrossError gate in
//                               src/lca.js otherwise). After sync BOTH
//                               replicas point at the join.
//
// No API lets a replica commit on, or merge with, anything but a current
// head; that is the gc_safety hypothesis (see src/gc.js) made structural.
//
// A datatype is { init, apply(state, op), merge3(l, a, b), read(state) },
// all pure: apply/merge3 must return fresh states (commits keep old states
// alive forever, or until gc).
//
// STATE GC: a datatype may additionally provide
//   compact(state, cut)        -> { state, translate, stats }
//   remapState(state, translate) -> state
// (src/compact.js provides both for the embed RGA). replica.compact(cut)
// then re-codes the replica's head under the SETTLED-CUT CONTRACT
// documented in src/compact.js: sound only when the cut is settled at the
// compacting replica (heard from everyone since the cut); the caller asserts
// it. Each compaction opens a new EPOCH with a translate function from the
// previous epoch's coordinates; merges lift the lower-epoch side (and the
// LCA payload) into the newer epoch record by record, the lazy stable-prefix
// translation on ingest. This runtime LINEARIZES epochs (a compaction is
// refused unless the compactor's head already sits at the newest epoch);
// concurrent divergent compactions are out of scope here.

import { Dag } from './dag.js';
import { lca } from './lca.js';
import { runGc } from './gc.js';
import { frontierOf, stableCut, insertIds } from './frontier.js';

export class Runtime {
  constructor(datatype) {
    this.datatype = datatype;
    this.dag = new Dag();
    this.root = this.dag.add({ parents: [], op: null, state: datatype.init() });
    this.replicas = [];
    // State-GC epochs: epochs[e] (e >= 1) translates epoch e-1 coordinates
    // to epoch e; epochOf maps commit id -> the epoch its state is coded in.
    this.epochs = [null];
    this.epochOf = new Map([[this.root.id, 0]]);
  }

  /** Lift a state coded in epoch `from` to epoch `to` (identity if equal). */
  liftState(state, from, to) {
    let s = state;
    for (let e = from + 1; e <= to; e++) {
      s = this.datatype.remapState(s, this.epochs[e]);
    }
    return s;
  }

  /** Register a replica. Closed membership: registration is refused once gc
   *  has pruned the root (the keep-set was computed without this replica;
   *  see the open-membership caveat in src/gc.js). */
  replica(name) {
    if (!this.dag.has(this.root.id)) {
      throw new Error(
        'cannot register a replica after gc pruned the root: the keep-set ' +
        'was computed against the then-current replica set (open-membership caveat)'
      );
    }
    const r = new Replica(this, name ?? `r${this.replicas.length}`);
    this.replicas.push(r);
    return r;
  }

  /** Run the commit GC against the CURRENT heads of the registered replicas.
   *  ONE FRONTIER, read from above: the keep-set retains the upward closure
   *  of the pairwise meets of these heads, while the stability producer
   *  (replica.compactStable) reads the same head/frontier data from below to
   *  find what is settled (src/frontier.js). Both consume the current-heads
   *  knowledge; neither invents a fact the other cannot see. */
  gc() {
    return runGc(this.dag, this.replicas.map((r) => r.head.id));
  }

  /** The registered replica names, closed at call time (open-membership
   *  caveat: registration is refused once gc prunes the root). The certified
   *  cut quantifies over exactly this set. */
  registeredNames() { return this.replicas.map((r) => r.name); }
}

export class Replica {
  #head;

  constructor(runtime, name) {
    this.runtime = runtime;
    this.name = name;
    this.#head = runtime.root;
    this.seq = 0;
    // THE FRONTIER: replicaName -> { id, seq } = the latest commit of that
    // replica this head has absorbed (its evidence commit). Rebuilt from
    // ancestry on every commit/sync (commit-shaped, never gated on
    // event-subsumption: a no-new-events pull still advances it).
    this.frontier = frontierOf(runtime.dag, this.#head.id);
  }

  /** Current head commit (read-only; there is no way to set it from outside). */
  get head() { return this.#head; }

  #refreshFrontier() { this.frontier = frontierOf(this.runtime.dag, this.#head.id); }

  /** Apply an op payload on this replica's own current head. */
  commit(payload) {
    const dt = this.runtime.datatype;
    const prepared = typeof dt.prepare === 'function'
      ? dt.prepare(this.#head.state, payload) : payload;
    const state = dt.apply(this.#head.state, prepared);
    const epoch = this.runtime.epochOf.get(this.#head.id);
    this.#head = this.runtime.dag.add({
      parents: [this.#head.id],
      op: { replica: this.name, seq: this.seq++, payload: prepared },
      state,
    });
    this.runtime.epochOf.set(this.#head.id, epoch);
    this.#refreshFrontier();
    return this.#head;
  }

  /** State GC: re-code this replica's head over a SETTLED cut (contract in
   *  src/compact.js; the caller asserts settledness). Opens a new epoch whose
   *  translate function lifts older-epoch states on ingest. opts is passed
   *  through to datatype.compact (the unguardedRenumber negative-control knob
   *  lives there; never set it in production). */
  compact(cut, opts) {
    const rt = this.runtime;
    const dt = rt.datatype;
    if (typeof dt.compact !== 'function' || typeof dt.remapState !== 'function') {
      throw new Error('datatype does not support state compaction (needs compact + remapState)');
    }
    const e = rt.epochOf.get(this.#head.id);
    if (e !== rt.epochs.length - 1) {
      throw new Error(
        'stale-epoch compaction refused: v1 linearizes compaction epochs; ' +
        'sync to the newest epoch first (concurrent compaction is the ' +
        'deferred protocol half)'
      );
    }
    const { state, translate, stats } = dt.compact(this.#head.state, cut, opts);
    rt.epochs.push(translate);
    const c = rt.dag.add({ parents: [this.#head.id], op: null, state });
    rt.epochOf.set(c.id, e + 1);
    this.#head = c;
    this.#refreshFrontier(); // unauthored commit: same authored set, new head id
    return { head: c, stats };
  }

  /** Join this replica's and other's CURRENT heads; both move to the join. */
  sync(other) {
    if (other.runtime !== this.runtime) {
      throw new Error('sync across different runtimes is not supported');
    }
    const dag = this.runtime.dag;
    const a = this.#head, b = other.#head;
    if (a.id === b.id) return a;
    if (dag.isAncestor(a.id, b.id)) {           // fast-forward: b subsumes a
      this.#head = b;
      this.#refreshFrontier();                  // advance on ancestry (commit-shaped)
      return b;
    }
    if (dag.isAncestor(b.id, a.id)) {           // fast-forward: a subsumes b
      other.#head = a;
      other.#refreshFrontier();
      return a;
    }
    const l = lca(dag, a.id, b.id);             // unique LCA or CrissCrossError
    const dt = this.runtime.datatype;
    const rt = this.runtime;
    // Epoch lifting (state GC): merge in the NEWEST epoch of the two heads;
    // the LCA payload and the lower-epoch head are translated on ingest
    // (lazy stable-prefix translation). All identity when nobody compacted.
    const eA = rt.epochOf.get(a.id), eB = rt.epochOf.get(b.id);
    const eT = Math.max(eA, eB);
    const lState = rt.liftState(dag.get(l).state, rt.epochOf.get(l), eT);
    const merged = dt.merge3(
      lState, rt.liftState(a.state, eA, eT), rt.liftState(b.state, eB, eT));
    const c = dag.add({ parents: [a.id, b.id], op: null, state: merged });
    rt.epochOf.set(c.id, eT);
    this.#head = c;
    other.#head = c;
    this.#refreshFrontier();
    other.#refreshFrontier();
    return c;
  }

  /** THE CERTIFIED STABLE CUT this replica can prove from its frontier: the
   *  meet of the event sets of every other registered replica's evidence
   *  commit (src/frontier.js). Returns { complete, meet, missing, ... };
   *  complete === false names the replicas not yet heard from since the cut. */
  stableCut() {
    return stableCut(
      this.runtime.dag, this.#head.id, this.runtime.registeredNames(), this.name);
  }

  /** THE EVIDENCE PRODUCER: state-GC at the largest cut this replica can
   *  CERTIFY from its frontier, in place of the ASSERTED settledness of
   *  replica.compact. The correspondence to the formal target:
   *
   *    frontier (per replica evidence commits c_j)  ==  AllHeardSince C v S
   *    stableCut = meet of E(c_j)                    ==  the maximal such S
   *    certificate present (complete)                ==  the hypothesis hAll
   *    reads preserved by the resulting compaction   ==  the stability VC
   *
   *  The certificate is CHECKED: if any registered replica has not been heard
   *  from since the cut (its evidence commit is absent), compaction is
   *  REFUSED (a no-op returning { compacted: false, missing }). This is the
   *  runtime witness of the not-heard breaker.
   *
   *  THE IN-FLIGHT DISCHARGE. cut.inflight is the crutch for asserted
   *  settledness: an in-flight op concurrent with the cut, whose frozen delta a
   *  dense renumber could flip. Under a CERTIFIED cut no such op exists: every
   *  op concurrent with the cut is already delivered (SettledAt condition 2),
   *  so it is an at-rest member that compact.js's own per-group stability gate
   *  refuses to renumber; every UNdelivered op is Lamport-fresh future work
   *  that sorts past the compacted block and translates verbatim. So we pass
   *  inflight: [] and it is sufficient, not asserted. */
  compactStable(opts) {
    const rt = this.runtime;
    const e = rt.epochOf.get(this.#head.id);
    if (e !== rt.epochs.length - 1) {
      return { compacted: false, reason: 'stale epoch; sync to the newest epoch first' };
    }
    const { complete, meet, missing } = this.stableCut();
    if (!complete) {
      return { compacted: false, missing,
        reason: `certificate absent: not heard from ${missing.join(', ')} since the cut` };
    }
    const settledIds = insertIds(meet);
    if (settledIds.size === 0) {
      return { compacted: false, reason: 'the certified stable cut is empty' };
    }
    // inflight: [] is discharged by the certificate (see the doc above).
    const { head, stats } = this.compact({ settledIds, inflight: [] }, opts);
    return { compacted: true, head, stats, cutSize: settledIds.size };
  }

  /** Datatype read of the current head state. */
  read() {
    return this.runtime.datatype.read(this.#head.state);
  }
}
