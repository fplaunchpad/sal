// Commit store: a git-like DAG of immutable commits.
//
// A commit = { id, parents: [ids], op, state } where
//   op    = { replica, seq, payload } for an operation commit, or null for a
//           merge commit (and for the root),
//   state = the datatype state AT this commit (materialized, immutable).
//
// The event set of a commit is implicit in the ancestry: the events of a
// commit are the ops along its reflexive ancestor closure (see events()).
//
// After GC (src/gc.js) a surviving commit may reference pruned parents; all
// traversals here skip parent ids that are no longer in the store, i.e. the
// ancestry is truncated at the GC horizon. This is sound for the runtime's
// own LCA queries because the keep-set retains every pairwise MCA of the
// current heads together with its full descendant cone (see src/gc.js).

export class Dag {
  #commits = new Map();
  #nextId = 0;

  /** Append a commit. Parents must already be in the store. */
  /** Replace a commit with a PARENTLESS clone keeping the same id (epoch-
   *  base severing after certified pruning). State/op/id untouched. */
  sever(id) {
    const c = this.#commits.get(id);
    if (!c) throw new Error(`sever: unknown commit ${id}`);
    this.#commits.set(id, Object.freeze({ id: c.id, parents: Object.freeze([]), op: c.op, state: c.state }));
  }

  add({ parents = [], op = null, state }) {
    for (const p of parents) {
      if (!this.#commits.has(p)) throw new Error(`unknown parent commit: ${p}`);
    }
    const id = 'c' + this.#nextId++;
    const commit = Object.freeze({ id, parents: Object.freeze([...parents]), op, state });
    this.#commits.set(id, commit);
    return commit;
  }

  get(id) {
    const c = this.#commits.get(id);
    if (!c) throw new Error(`no such commit: ${id} (pruned by gc, or never added)`);
    return c;
  }

  has(id) { return this.#commits.has(id); }
  get size() { return this.#commits.size; }
  ids() { return [...this.#commits.keys()]; }
  values() { return this.#commits.values(); }

  /** Remove a commit (gc only). */
  remove(id) { this.#commits.delete(id); }

  /** Remove parent references that leave `keep`.  This is the graph half of
   * commit GC: payload deletion alone leaves an unbounded list of dangling
   * historical ids in surviving commits.  `keepSet` is upward closed from its
   * MCA seeds, so every path between two kept commits already stays in `keep`;
   * filtering boundary edges therefore preserves all retained-node ancestry
   * and LCA answers while making retained seeds genuine parent-free bases. */
  restrictParents(keep) {
    for (const [id, c] of this.#commits) {
      if (!keep.has(id)) continue;
      const parents = c.parents.filter((p) => keep.has(p));
      if (parents.length === c.parents.length) continue;
      this.#commits.set(id, Object.freeze({
        id: c.id, parents: Object.freeze(parents), op: c.op, state: c.state
      }));
    }
  }

  /** Reflexive ancestor closure of id, as a Set of commit ids.
   *  Missing parents (pruned by gc) are skipped. */
  ancestorSet(id) {
    this.get(id); // must exist
    const seen = new Set([id]);
    const stack = [id];
    while (stack.length > 0) {
      const c = this.#commits.get(stack.pop());
      if (!c) continue; // pruned parent: ancestry truncated at the gc horizon
      for (const p of c.parents) {
        if (!seen.has(p) && this.#commits.has(p)) { seen.add(p); stack.push(p); }
      }
    }
    return seen;
  }

  /** Subsumption check: is `anc` a reflexive ancestor of `desc`?
   *  (anc's implicit event set is then subsumed by desc's.)
   *  Upward BFS from desc with early exit: O(|ancestors(desc)|) worst case,
   *  no full closure materialized. */
  isAncestor(anc, desc) {
    this.get(anc); this.get(desc);
    if (anc === desc) return true;
    const seen = new Set([desc]);
    const stack = [desc];
    while (stack.length > 0) {
      const c = this.#commits.get(stack.pop());
      if (!c) continue;
      for (const p of c.parents) {
        if (p === anc) return true;
        if (!seen.has(p) && this.#commits.has(p)) { seen.add(p); stack.push(p); }
      }
    }
    return false;
  }

  /** The implicit event set: all ops along the reflexive ancestor closure.
   *  Returned as an array in no particular order (it denotes a SET). */
  events(id) {
    const out = [];
    for (const a of this.ancestorSet(id)) {
      const { op } = this.get(a);
      if (op !== null) out.push(op);
    }
    return out;
  }

  /** Map from commit id to array of child ids (used by gc's upward closure). */
  childrenIndex() {
    const idx = new Map();
    for (const c of this.#commits.values()) {
      for (const p of c.parents) {
        if (!this.#commits.has(p)) continue;
        if (!idx.has(p)) idx.set(p, []);
        idx.get(p).push(c.id);
      }
    }
    return idx;
  }
}
