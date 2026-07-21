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

import { PMap, isPMap, eachEntry } from '../pmap.js';

const addTag = (state, op) => {
  if (state.has(op.tag)) throw new Error(`duplicate instance tag ${op.tag}`);
  return op.el;
};

export const orset = {
  /** state: PMap tag -> el (persistent: apply/merge3 return new maps with
   *  structural sharing, O(log n) per op). Legacy plain-Map states are
   *  accepted read-only and copied on write. */
  init() { return PMap.empty(); },

  apply(state, op) {
    const p = isPMap(state);
    if (op.type === 'add') {
      const el = addTag(state, op);
      return p ? state.set(op.tag, el) : new Map(state).set(op.tag, el);
    }
    if (op.type === 'rm') {
      if (p) {
        let s = state;
        for (const t of op.tags) s = s.delete(t); // absent tag: no-op
        return s;
      }
      const s = new Map(state);
      for (const t of op.tags) s.delete(t);
      return s;
    }
    throw new Error(`unknown orset op type: ${op.type}`);
  },

  /** Batch apply in ONE transient pass (identical to folding apply). */
  applyBatch(state, ops) {
    const t = (isPMap(state) ? state : PMap.from(state)).begin();
    for (const op of ops) {
      if (op.type === 'add') t.set(op.tag, addTag(t, op));
      else if (op.type === 'rm') { for (const tag of op.tags) t.delete(tag); }
      else throw new Error(`unknown orset op type: ${op.type}`);
    }
    return t.freeze();
  },

  read(state) {
    return [...new Set(state.values())].sort((x, y) => (x < y ? -1 : x > y ? 1 : 0));
  },

  /** Tags currently carrying el (helper for building honest rm ops).
   *  Sorted-key iteration: the tag list is deterministic in the state. */
  observe(state, el) {
    return [...state.entries()].filter(([, e]) => e === el).map(([t]) => t);
  },

  /** Delta merge from A on PMap states -- A ∖ (L ∖ B) ∪ (B ∖ L), touching
   *  only the tags B removed or added, structural sharing for the rest.
   *  Hash-order scans are safe: the output is a content-canonical set. */
  merge3(l, a, b) {
    if (isPMap(a)) {
      const s = a.begin();
      eachEntry(l, (t) => { if (!b.has(t)) s.delete(t); });
      eachEntry(b, (t, e) => { if (!a.has(t) && !l.has(t)) s.set(t, e); });
      return s.freeze();
    }
    // legacy plain-Map inputs: rebuild into one transient
    const s = PMap.empty().begin();
    eachEntry(a, (t, e) => { if (b.has(t) || !l.has(t)) s.set(t, e); });
    eachEntry(b, (t, e) => { if (!l.has(t) && !s.has(t)) s.set(t, e); });
    return s.freeze();
  },

  /** Canonical serialization (twin-comparison helper for tests). */
  fingerprint(state) {
    return JSON.stringify([...state.entries()].sort(([x], [y]) => (x < y ? -1 : 1)));
  },
};
