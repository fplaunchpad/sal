// OR-set (observed-remove set): the second datatype, here to prove the
// runtime is pluggable. UNVERIFIED transliteration of the standard MRDT
// OR-set semantics:
//   - add mints a fresh uniquely-tagged INSTANCE of the element;
//   - remove kills exactly the instances it has OBSERVED;
//   - merge is the same ternary live-set rule on instance tags:
//       (A ∩ B) ∪ (A ∖ L) ∪ (B ∖ L)
//     so a concurrent add always survives a concurrent remove (add-wins).
//
// Ops:  { type: 'add', tag, el }        tag globally unique
//       { type: 'rm', tags: [tag...] }  the observed instances to kill
//
// read = the SET of elements with at least one live instance, sorted for
// deterministic comparison.

export const orset = {
  /** state: Map tag -> el (immutable; apply/merge3 copy) */
  init() { return new Map(); },

  apply(state, op) {
    const s = new Map(state);
    if (op.type === 'add') {
      if (s.has(op.tag)) throw new Error(`duplicate instance tag ${op.tag}`);
      s.set(op.tag, op.el);
    } else if (op.type === 'rm') {
      for (const t of op.tags) s.delete(t); // absent tag: no-op
    } else {
      throw new Error(`unknown orset op type: ${op.type}`);
    }
    return s;
  },

  read(state) {
    return [...new Set(state.values())].sort((x, y) => (x < y ? -1 : x > y ? 1 : 0));
  },

  /** Tags currently carrying el (helper for building honest rm ops). */
  observe(state, el) {
    return [...state.entries()].filter(([, e]) => e === el).map(([t]) => t);
  },

  merge3(l, a, b) {
    const s = new Map();
    for (const [t, e] of a) if (b.has(t) || !l.has(t)) s.set(t, e);
    for (const [t, e] of b) if (!l.has(t) && !s.has(t)) s.set(t, e);
    return s;
  },

  /** Canonical serialization (twin-comparison helper for tests). */
  fingerprint(state) {
    return JSON.stringify([...state.entries()].sort(([x], [y]) => (x < y ? -1 : 1)));
  },
};
