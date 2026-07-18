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

import { Dag } from './dag.js';
import { lca } from './lca.js';
import { runGc } from './gc.js';

export class Runtime {
  constructor(datatype) {
    this.datatype = datatype;
    this.dag = new Dag();
    this.root = this.dag.add({ parents: [], op: null, state: datatype.init() });
    this.replicas = [];
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
    this.#head = this.runtime.dag.add({
      parents: [this.#head.id],
      op: { replica: this.name, seq: this.seq++, payload },
      state,
    });
    return this.#head;
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
    const merged = dt.merge3(dag.get(l).state, a.state, b.state);
    const c = dag.add({ parents: [a.id, b.id], op: null, state: merged });
    this.#head = c;
    other.#head = c;
    return c;
  }

  /** Datatype read of the current head state. */
  read() {
    return this.runtime.datatype.read(this.#head.state);
  }
}
