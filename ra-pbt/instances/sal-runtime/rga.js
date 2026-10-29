// The Sal runtime RGA as a law-checking target.
//
// State, merge and read are the runtime's: a grow-only map of insertion
// records `id -> { anchorId, el }` and a grow-only grave set, merged by
// union. The raw `do` is total, as in the paper: an operation the runtime
// accepts goes through the runtime's `apply`; otherwise an insertion adds its
// record (if absent) and a deletion adds its id to the grave. The runtime
// rejects such operations only at issuance, and honest generation never
// issues them.

import { rga as runtimeRga, rgaApplicable } from '../../../runtime/src/datatypes/rga.js';

const ELEMENTS = ['x', 'y', 'z'];

function rawEffect(s, op) {
  if (op.type === 'ins') {
    if (s.adds.has(op.id)) return s;
    return Object.freeze({ adds: s.adds.set(op.id, Object.freeze({ anchorId: op.anchorId ?? null, el: op.el })), grave: s.grave, order: null });
  }
  if (op.type === 'del') return s.grave.has(op.id) ? s : Object.freeze({ adds: s.adds, grave: s.grave.add(op.id), order: null });
  throw new Error(`unknown op ${op.type}`);
}

export const rgaDatatype = {
  name: 'rga',
  init: () => runtimeRga.init(),
  apply: (s, op) => (rgaApplicable(s, op) ? runtimeRga.apply(s, op) : rawEffect(s, op)),
  merge3: (l, a, b) => runtimeRga.merge3(l, a, b),
  read: (s) => runtimeRga.read(s),
  serialise(s) {
    const adds = [...s.adds.entries()].map(([id, r]) => [id, r.anchorId, r.el]).sort((x, y) => x[0] - y[0]);
    return JSON.stringify({ adds, grave: [...s.grave].sort((x, y) => x - y) });
  },
};

/** The identified-list specification: state (B, I) with B the live id list
 *  and I the allocated ids. ins(t, a) is admitted when t is fresh and the
 *  anchor a is the root or live, and places t immediately after a; del(x)
 *  removes x from B and is always admitted. Observed as B. */
export const listSpec = {
  init: () => ({ B: [], I: [] }),
  step(phi, op) {
    if (op.type === 'ins') {
      const a = op.anchorId ?? null;
      if (!(op.id > 0) || phi.I.includes(op.id) || (a !== null && !phi.B.includes(a))) return undefined;
      const i = a === null ? 0 : phi.B.indexOf(a) + 1;
      return { B: [...phi.B.slice(0, i), op.id, ...phi.B.slice(i)], I: [...phi.I, op.id] };
    }
    if (op.type === 'del') return { B: phi.B.filter((x) => x !== op.id), I: phi.I };
    return undefined;
  },
  observe: (phi) => phi.B,
};

/** Commutativity in the list specification: two insertions commute unless
 *  they share an anchor or one anchors at the other; an insertion and a
 *  deletion commute unless the deletion targets the insertion or its anchor;
 *  deletions commute. */
export function listSpecCommutes(o1, o2) {
  const anc = (o) => o.anchorId ?? null;
  if (o1.type === 'ins' && o2.type === 'ins') return !(anc(o1) === anc(o2) || anc(o1) === o2.id || anc(o2) === o1.id);
  if (o1.type === 'del' && o2.type === 'del') return true;
  const [i, d] = o1.type === 'ins' ? [o1, o2] : [o2, o1];
  return !(d.id === i.id || (anc(i) !== null && d.id === anc(i)));
}

export function genRgaEvent(rnd, live, ctx, elements = ELEMENTS) {
  if (!live.length || rnd() < 0.65) {
    const anchorId = live.length && rnd() < 0.7 ? live[Math.floor(rnd() * live.length)] : null;
    return { type: 'ins', id: ctx.fresh(), el: elements[Math.floor(rnd() * elements.length)], anchorId };
  }
  return { type: 'del', id: live[Math.floor(rnd() * live.length)] };
}

/** rc = ∅: the grow-only effects commute. Insertions sort before deletions
 *  in the specification witness, and insertions by ascending id. */
export const rgaInstance = {
  name: 'rga',
  genEvent: (rnd, state, ctx) => genRgaEvent(rnd, runtimeRga.readIds(state), ctx),
  specCommutes: listSpecCommutes,
  spec: listSpec,
  observe: (s) => runtimeRga.readIds(s),
  witnessOrder(a, b) {
    const rank = (e) => (e.op.type === 'ins' ? 0 : 1);
    return rank(a) - rank(b) || a.op.id - b.op.id;
  },
};

/** An rc that orders an insertion after x before a deletion of x, and
 *  insertions after the same anchor by ascending id. */
export const rgaOrderingRcInstance = {
  ...rgaInstance,
  name: 'rga-ordering-rc',
  rc(o1, o2) {
    const anc = (o) => o.anchorId ?? null;
    if (o1.type === 'ins' && o2.type === 'del') return anc(o1) !== null && anc(o1) === o2.id;
    if (o1.type === 'ins' && o2.type === 'ins') return anc(o1) === anc(o2) && o1.id < o2.id;
    return false;
  },
};

// Negative control: a list RGA that orders siblings by element (ascending)
// instead of by id, with equal elements placed in arrival order (the newer
// arrival first). Insertion and merge share this placement rule; merge
// replays the second branch's missing insertions into the first branch.

function subtreeOf(recs, k, s) {
  for (let x = k; x !== null && x !== undefined; x = recs.get(x)?.anchorId) if (x === s) return true;
  return false;
}

function placeInsert(list, recs, op) {
  const a = op.anchorId ?? null;
  let i = a === null ? 0 : list.indexOf(a) + 1;
  if (a !== null && i === 0) i = list.length;
  while (i < list.length) {
    const sib = list[i], r = recs.get(sib);
    if (r.anchorId !== a || !(r.el < op.el)) break;
    i++;
    while (i < list.length && subtreeOf(recs, list[i], sib)) i++;
  }
  return [...list.slice(0, i), op.id, ...list.slice(i)];
}

function insertRecord(s, op) {
  if (s.recs.has(op.id)) return s;
  const recs = new Map(s.recs).set(op.id, { anchorId: op.anchorId ?? null, el: op.el });
  return { list: placeInsert(s.list, recs, op), recs, grave: s.grave };
}

export const brokenRgaDatatype = {
  name: 'broken-rga',
  init: () => ({ list: [], recs: new Map(), grave: new Set() }),
  apply(s, op) {
    if (op.type === 'ins') return insertRecord(s, op);
    if (op.type === 'del') return { ...s, grave: new Set(s.grave).add(op.id) };
    throw new Error(`unknown op ${op.type}`);
  },
  merge3(_l, a, b) {
    let s = a;
    for (const id of b.list) if (!s.recs.has(id)) s = insertRecord(s, { id, ...b.recs.get(id) });
    return { ...s, grave: new Set([...s.grave, ...b.grave]) };
  },
  read: (s) => s.list.filter((id) => !s.grave.has(id)).map((id) => s.recs.get(id).el),
};

/** rc = ∅ as for the RGA. Declared non-commuting pairs are the dependent
 *  ones (an insertion and an insertion anchored at it, an insertion and a
 *  deletion of it), so linear extensions respect anchors; concurrent
 *  sibling insertions are declared commuting. */
export const brokenRgaInstance = {
  name: 'broken-rga',
  commutes(o1, o2) {
    const dependsOn = (x, y) => (x.type === 'ins' && (x.anchorId ?? null) === y.id && y.type === 'ins')
      || (x.type === 'del' && y.type === 'ins' && x.id === y.id);
    return !(dependsOn(o1, o2) || dependsOn(o2, o1));
  },
  genEvent: (rnd, state, ctx) => genRgaEvent(rnd, state.list.filter((id) => !state.grave.has(id)), ctx, ['a', 'b']),
};
