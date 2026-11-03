/**
 * Tiny list specifications for the witness tests. A state is an array of
 * { id, ch, deleted }; the view is the string of visible characters, or the
 * array of visible { id, ch } with `withIds`.
 *
 *   rgaList   ins { id, ch, after } lands immediately after `after` (the head
 *             when null), so a later sibling lands nearer its anchor;
 *             del { id } marks the character deleted.
 *   gapList   ins { id, ch, after, before } lands anywhere strictly between
 *             `after` and `before` (relational), with target-directed
 *             placements for targets that carry identities.
 */

const at = (state, id) => (id === null ? -1 : state.findIndex((c) => c.id === id));
const has = (state, id) => state.some((c) => c.id === id);
const insertAt = (state, i, op) => [...state.slice(0, i), { id: op.id, ch: op.ch, deleted: false }, ...state.slice(i)];

const common = {
  init: () => [],
  view: (state) => state.filter((c) => !c.deleted).map((c) => c.ch).join(''),
  serialise: (state) => JSON.stringify(state),
  viewKey: (v) => (typeof v === 'string' ? v : v.map((c) => c.ch).join('')),
};

function del(state, op) {
  if (!has(state, op.id)) return null;
  return state.map((c) => (c.id === op.id ? { ...c, deleted: true } : c));
}

export const rgaList = {
  ...common,
  apply(state, op) {
    if (op.kind === 'del') return del(state, op);
    if (has(state, op.id)) return null;
    const o = at(state, op.after);
    if (op.after !== null && o === -1) return null;
    return insertAt(state, o + 1, op);
  },
};

function gapBounds(state, op) {
  if (has(state, op.id)) return null;
  const o = at(state, op.after ?? null);
  if (op.after != null && o === -1) return null;
  let hi = state.length;
  if (op.before != null) {
    hi = at(state, op.before);
    if (hi === -1 || hi < o + 1) return null;
  }
  return [o + 1, hi];
}

function gapAll(state, op, lo, hi) {
  const out = [];
  for (let i = lo; i <= hi; i++) out.push(insertAt(state, i, op));
  return out;
}

export const gapList = {
  ...common,
  apply(state, op) {
    return this.applyAll(state, op)[0] ?? null;
  },
  applyAll(state, op) {
    if (op.kind === 'del') {
      const n = del(state, op);
      return n ? [n] : [];
    }
    const b = gapBounds(state, op);
    return b ? gapAll(state, op, b[0], b[1]) : [];
  },
  directs: (target) => Array.isArray(target) && target.length > 0 && target[0].id !== undefined,
  applyDirected(state, op, target) {
    if (op.kind === 'del') return this.applyAll(state, op);
    const b = gapBounds(state, op);
    if (!b) return [];
    let [lo, hi] = b;
    const pos = new Map(target.map((c, i) => [c.id, i]));
    const mine = pos.get(op.id);
    if (mine !== undefined)
      state.forEach((c, i) => {
        const p = pos.get(c.id);
        if (p === undefined) return;
        if (p < mine) lo = Math.max(lo, i + 1);
        else hi = Math.min(hi, i);
      });
    return gapAll(state, op, lo, hi);
  },
};
