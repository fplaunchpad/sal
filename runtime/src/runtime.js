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
// STATE GC (task #97): a datatype may additionally provide
//   compact(state, cut)        -> { state, translate, stats }
//   remapState(state, translate) -> state
// (src/compact.js provides both for the embed RGA). replica.compact(cut)
// then re-codes the replica's head under the SETTLED-CUT CONTRACT
// documented in src/compact.js: sound only when the cut is settled at the
// compacting replica (heard from everyone since the cut,
// whiteboard/stability-vc-note.md section 2); in v1 the caller asserts it.
// Each compaction opens a new EPOCH with a translate function from the
// previous epoch's coordinates; merges lift the lower-epoch side (and the
// LCA payload) into the newer epoch record by record -- the lazy
// stable-prefix translation on ingest. v1 restriction: epochs are
// LINEARIZED per runtime (a compaction is refused unless the compactor's
// head already sits at the newest epoch); concurrent divergent compactions
// are the deferred protocol half (whiteboard/embed-recoding-note.md
// section 6).

import { Dag } from './dag.js';
import { lca } from './lca.js';
import { runGc } from './gc.js';

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

  /** Run the commit GC against the CURRENT heads of the registered replicas. */
  gc() {
    return runGc(this.dag, this.replicas.map((r) => r.head.id));
  }
}

export class Replica {
  #head;

  constructor(runtime, name) {
    this.runtime = runtime;
    this.name = name;
    this.#head = runtime.root;
    this.seq = 0;
  }

  /** Current head commit (read-only; there is no way to set it from outside). */
  get head() { return this.#head; }

  /** Apply an op payload on this replica's own current head. */
  commit(payload) {
    const dt = this.runtime.datatype;
    const state = dt.apply(this.#head.state, payload);
    const epoch = this.runtime.epochOf.get(this.#head.id);
    this.#head = this.runtime.dag.add({
      parents: [this.#head.id],
      op: { replica: this.name, seq: this.seq++, payload },
      state,
    });
    this.runtime.epochOf.set(this.#head.id, epoch);
    return this.#head;
  }

  /** State GC: re-code this replica's head over a SETTLED cut (contract in
   *  src/compact.js; the caller asserts settledness in v1). Opens a new
   *  epoch whose translate function lifts older-epoch states on ingest.
   *  opts is passed through to datatype.compact (the unguardedRenumber
   *  negative-control knob lives there; never set it in production). */
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
        'deferred protocol half, embed-recoding-note section 6)'
      );
    }
    const { state, translate, stats } = dt.compact(this.#head.state, cut, opts);
    rt.epochs.push(translate);
    const c = rt.dag.add({ parents: [this.#head.id], op: null, state });
    rt.epochOf.set(c.id, e + 1);
    this.#head = c;
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
      return b;
    }
    if (dag.isAncestor(b.id, a.id)) {           // fast-forward: a subsumes b
      other.#head = a;
      return a;
    }
    const l = lca(dag, a.id, b.id);             // unique LCA or CrissCrossError (#90 gate)
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
    return c;
  }

  /** Datatype read of the current head state. */
  read() {
    return this.runtime.datatype.read(this.#head.state);
  }
}
