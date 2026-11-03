/**
 * Sequential specification of styled text with persistent anchored marks:
 * the 'persistent' reading.
 *
 * A state is { items, marks }. `items` is an immutable list of characters
 *   { t: 'c', id: [peer, counter], ch, deleted }
 * and anchors
 *   { t: 'a', mark: markKey, side: 'start' | 'end' }.
 * `marks` maps a mark's key ("peer:counter") to { key, value, seq }, seq
 * being its position in application order. A character's attributes are not
 * stored: for each style key, a character takes the value of the
 * last-applied mark of that key whose start anchor precedes it and whose end
 * anchor follows it (none when that value is null, or no such mark).
 *
 * Operations (from `interpret` in spec.js, with the identities below):
 *   insert { id, ch, origin, rightOrigin, attrs, knownMarks }: the character
 *     lands anywhere strictly between its recorded neighbours, among
 *     characters and anchors alike (the gap rule), at a position where the
 *     marks its issuer had integrated (`knownMarks`) give it exactly `attrs`,
 *     the attributes it was issued with. Relative to anchors of marks its
 *     issuer did not know, it may land on either side.
 *   delete { ids }: marks characters deleted; anchors stay.
 *   mark { mid, left, right, outerLeft, outerRight, key, value }: the start
 *     anchor lands anywhere after `outerLeft` (or the head) and before `left`,
 *     the end anchor anywhere after `right` and before `outerRight` (or the
 *     end); the mark is applied last so far.
 * The expand configuration enters only through `attrs`, which is what the
 * issuer's own placement gave the insertion: a mark is a range between two
 * list elements, and expansion is a property of local insertion.
 *
 * Self-contained apart from the shared helpers in spec.js.
 */
import { idKey, idEq, normaliseAttrs, viewKey, normaliseView, localEdit, EXPAND } from './spec.js';

export function initial() {
  return { items: [], marks: {} };
}

const isChar = (it) => it.t === 'c';

function indexOfChar(items, id) {
  for (let i = 0; i < items.length; i++) if (isChar(items[i]) && idEq(items[i].id, id)) return i;
  return -1;
}

/** Canonical string of a state. */
export function serialise(state) {
  const items = state.items.map((it) => (isChar(it) ? [idKey(it.id), it.ch, it.deleted] : [it.mark, it.side]));
  const marks = Object.keys(state.marks)
    .sort()
    .map((k) => [k, state.marks[k].key, state.marks[k].value, state.marks[k].seq]);
  return JSON.stringify([items, marks]);
}

/** Attributes of every item position from the marks enclosing it, restricted to `only` when given. */
function attrsAlong(state, only = null) {
  const open = new Set();
  const out = [];
  for (const it of state.items) {
    if (!isChar(it)) {
      if (only && !only.has(it.mark)) {
        out.push(null);
        continue;
      }
      if (it.side === 'start') open.add(it.mark);
      else open.delete(it.mark);
      out.push(null);
      continue;
    }
    const best = {};
    for (const m of open) {
      const mk = state.marks[m];
      if (!best[mk.key] || best[mk.key].seq < mk.seq) best[mk.key] = mk;
    }
    const attrs = {};
    for (const [k, mk] of Object.entries(best)) if (mk.value !== null && mk.value !== undefined) attrs[k] = mk.value;
    out.push(normaliseAttrs(attrs));
  }
  return out;
}

/** Visible characters as `[ { id, ch, attrs } ]`. */
export function viewWithIds(state) {
  const attrs = attrsAlong(state);
  return state.items.map((it, i) => [it, attrs[i]]).filter(([it]) => isChar(it) && !it.deleted).map(([it, a]) => ({ id: it.id, ch: it.ch, attrs: a }));
}

/** Visible characters as `[ { ch, attrs } ]`. */
export function view(state) {
  return normaliseView(viewWithIds(state));
}

const sameAttrs = (a, b) => JSON.stringify(normaliseAttrs(a)) === JSON.stringify(normaliseAttrs(b));

/** The insertion bounds [lo, hi] of an insert, or null. */
function gapOf(items, op) {
  let lo = 0;
  if (op.origin !== null && op.origin !== undefined) {
    const o = indexOfChar(items, op.origin);
    if (o === -1) return null;
    lo = o + 1;
  }
  let hi = items.length;
  if (op.rightOrigin !== null && op.rightOrigin !== undefined) {
    const r = indexOfChar(items, op.rightOrigin);
    if (r === -1 || r < lo) return null;
    hi = r;
  }
  return [lo, hi];
}

/** Narrows [lo, hi] to the positions that keep the order a target view gives (as in spec.applyPlaced). */
function narrow(items, op, lo, hi, placed) {
  if (!placed) return [lo, hi];
  const mine = placed.get(idKey(op.id));
  if (mine === undefined) return [lo, hi];
  for (let i = 0; i < items.length; i++) {
    if (!isChar(items[i])) continue;
    const p = placed.get(idKey(items[i].id));
    if (p === undefined) continue;
    if (p < mine) lo = Math.max(lo, i + 1);
    else hi = Math.min(hi, i);
  }
  return [lo, hi];
}

/** Every state an operation may lead to; `placed` (a target's id positions) directs insert placement. */
export function applyAll(state, op, placed = null) {
  const items = state.items;
  switch (op.kind) {
    case 'insert': {
      if (indexOfChar(items, op.id) !== -1) return [];
      const g = gapOf(items, op);
      if (g === null) return [];
      const [lo, hi] = narrow(items, op, g[0], g[1], placed);
      const known = new Set(op.knownMarks ?? []);
      const out = [];
      for (let at = lo; at <= hi; at++) {
        const next = { items: [...items.slice(0, at), { t: 'c', id: op.id, ch: op.ch, deleted: false }, ...items.slice(at)], marks: state.marks };
        if (sameAttrs(attrsAlong(next, known)[at], op.attrs)) out.push(next);
      }
      return out;
    }
    case 'delete': {
      const pos = new Set();
      for (const id of op.ids) {
        const i = indexOfChar(items, id);
        if (i === -1) return [];
        pos.add(i);
      }
      return [{ items: items.map((it, i) => (pos.has(i) ? { ...it, deleted: true } : it)), marks: state.marks }];
    }
    case 'mark': {
      if (state.marks[op.mid]) return [];
      const l = indexOfChar(items, op.left);
      const r = indexOfChar(items, op.right);
      if (l === -1 || r === -1 || l > r) return [];
      const ol = op.outerLeft === null || op.outerLeft === undefined ? -1 : indexOfChar(items, op.outerLeft);
      const or = op.outerRight === null || op.outerRight === undefined ? items.length : indexOfChar(items, op.outerRight);
      if ((ol === -1 && op.outerLeft) || or === -1 || ol > l || or < r) return [];
      const marks = { ...state.marks, [op.mid]: { key: op.key, value: op.value, seq: Object.keys(state.marks).length } };
      const out = [];
      for (let s = ol + 1; s <= l; s++)
        for (let e = r + 1; e <= or; e++) {
          // positions in the original list; the end anchor goes in first so s stays valid
          const withEnd = [...items.slice(0, e), { t: 'a', mark: op.mid, side: 'end' }, ...items.slice(e)];
          out.push({ items: [...withEnd.slice(0, s), { t: 'a', mark: op.mid, side: 'start' }, ...withEnd.slice(s)], marks });
        }
      return out;
    }
    default:
      throw new Error('unknown operation kind: ' + op.kind);
  }
}

/** The 'persistent' reading as an ra-pbt specification object (gap rule; relational). */
export function anchoredSpec({ expand = EXPAND } = {}) {
  const placements = new WeakMap();
  const placedOf = (target) => {
    let p = placements.get(target);
    if (!p) {
      p = new Map();
      target.forEach((e, i) => e.id !== undefined && p.set(idKey(e.id), i));
      placements.set(target, p);
    }
    return p;
  };
  return {
    rule: 'gap',
    attrsMode: 'persistent',
    expand,
    init: initial,
    view,
    serialise,
    viewKey,
    normalise: normaliseView,
    localEdit: (v, request) => localEdit(v, request, expand),
    apply: (state, op) => applyAll(state, op)[0] ?? null,
    applyAll: (state, op) => applyAll(state, op),
    applyDirected: (state, op, target) => applyAll(state, op, placedOf(target)),
    directs: (target) => target !== null && target.length > 0 && target[0].id !== undefined,
  };
}
