// Plain tombstone RGA. This mirrors the proved state in
// RGA_WithTombstones.lean: a grow-only insertion relation plus a grow-only
// grave set. The optimized representation indexes insertions by their unique
// timestamp/id and derives the Lean fold's order with one tree traversal.

import { PMap, PSet, eachEntry, isPMap, isPSet } from '../pmap.js';

const ROOT = null;
const record = (anchorId, el) => Object.freeze({ anchorId, el });

const members = (s) => isPSet(s) ? s : PSet.from(s);
const entries = (m) => isPMap(m) ? m : PMap.from(m);

function checkInsert(adds, grave, op) {
  if (!Number.isInteger(op.id) || op.id < 1) throw new Error(`bad fresh id ${op.id}`);
  if (adds.has(op.id)) throw new Error(`duplicate id/timestamp ${op.id}`);
  if (grave.has(op.id)) throw new Error(`resurrection of ${op.id}`);
  const anchorId = op.anchorId ?? ROOT;
  if (anchorId !== ROOT) {
    if (!adds.has(anchorId)) throw new Error(`anchor ${anchorId} not known`);
    if (anchorId >= op.id) throw new Error(`anchor ${anchorId} must precede ${op.id}`);
  }
  return anchorId;
}

function checkDelete(adds, grave, op) {
  if (!adds.has(op.id)) throw new Error(`remove ${op.id} before insertion`);
  if (grave.has(op.id)) throw new Error(`remove ${op.id} is not live`);
}

/** The Lean rgaApplicable guard, specialized to id = insertion timestamp. */
export function rgaApplicable(s, op) {
  try {
    if (op.type === 'ins') checkInsert(s.adds, s.grave, op);
    else if (op.type === 'del') checkDelete(s.adds, s.grave, op);
    else return false;
    return true;
  } catch { return false; }
}

function orderedIds(adds) {
  const children = new Map();
  eachEntry(adds, (id, r) => {
    let xs = children.get(r.anchorId);
    if (!xs) { xs = []; children.set(r.anchorId, xs); }
    xs.push(id);
  });
  // The Lean spec processes timestamps in ascending order and inserts each
  // child immediately after its anchor. Therefore siblings display newest
  // first. Anchor closure makes the resulting relation a rooted tree.
  for (const xs of children.values()) xs.sort((a, b) => b - a);
  const out = [], visiting = new Set();
  const walk = (anchor) => {
    for (const id of children.get(anchor) ?? []) {
      if (visiting.has(id)) throw new Error(`RGA anchor cycle at ${id}`);
      visiting.add(id); out.push(id); walk(id); visiting.delete(id);
    }
  };
  walk(ROOT);
  if (out.length !== adds.size) throw new Error('RGA state contains an unreachable anchor');
  return out;
}

function mergeAdds(a, b) {
  const x = entries(a), t = x.begin();
  eachEntry(b, (id, rb) => {
    const ra = x.get(id);
    if (ra && (ra.anchorId !== rb.anchorId || ra.el !== rb.el))
      throw new Error(`RGA insertion divergence at ${id}`);
    if (!ra) t.set(id, rb);
  });
  return t.freeze();
}

function mergeGrave(a, b) {
  const t = members(a).begin();
  for (const id of members(b)) t.add(id);
  return t.freeze();
}

export const rga = {
  name: 'rga', needsPrepare: true,
  init: () => Object.freeze({ adds: PMap.empty(), grave: PSet.empty(), order: null }),
  prepare(s, op) {
    if (op.type === 'ins') {
      const anchorId = checkInsert(s.adds, s.grave, op);
      return Object.freeze({ ...op, anchorId });
    }
    if (op.type === 'del') { checkDelete(s.adds, s.grave, op); return op; }
    throw new Error(`unknown RGA op ${op.type}`);
  },
  apply(s, raw) {
    const op = this.prepare(s, raw);
    if (op.type === 'ins') return Object.freeze({
      adds: s.adds.set(op.id, record(op.anchorId, op.el)), grave: s.grave, order: null,
    });
    return Object.freeze({ adds: s.adds, grave: s.grave.add(op.id), order: s.order });
  },
  applyBatch(s, ops) {
    const adds = s.adds.begin(), grave = s.grave.begin();
    for (const op of ops) {
      if (op.type === 'ins') {
        const anchorId = checkInsert(adds, grave, op);
        adds.set(op.id, record(anchorId, op.el));
      } else if (op.type === 'del') {
        checkDelete(adds, grave, op); grave.add(op.id);
      } else throw new Error(`unknown RGA op ${op.type}`);
    }
    return Object.freeze({ adds: adds.freeze(), grave: grave.freeze(), order: null });
  },
  merge3(_l, a, b) {
    return Object.freeze({ adds: mergeAdds(a.adds, b.adds),
      grave: mergeGrave(a.grave, b.grave), order: null });
  },
  readEntries(s) {
    const order = s.order ?? orderedIds(s.adds), out = [];
    for (const id of order) if (!s.grave.has(id)) out.push([id, s.adds.get(id)]);
    return out;
  },
  readIds(s) { return this.readEntries(s).map(([id]) => id); },
  read(s) { return this.readEntries(s).map(([, r]) => r.el); },
  has(s, id) { return s.adds.has(id) && !s.grave.has(id); },
  encodeState(s) {
    return { v: 1, adds: [...s.adds.entries()].map(([id, r]) => [id, r.anchorId, r.el]),
      grave: [...s.grave] };
  },
  decodeState(enc) {
    if (!enc || enc.v !== 1) throw new Error('unsupported RGA snapshot version');
    const adds = PMap.from(enc.adds.map(([id, anchorId, el]) => [id, record(anchorId, el)]));
    const grave = PSet.from(enc.grave);
    // Validate the trusted snapshot boundary before accepting it.
    orderedIds(adds);
    for (const id of grave) if (!adds.has(id)) throw new Error(`RGA tombstone ${id} has no insertion`);
    return Object.freeze({ adds, grave, order: null });
  },
  fingerprint(s) { return JSON.stringify(this.encodeState(s)); },
  symbolCount(s) { return s.adds.size + s.grave.size; },
  liveCount(s) { return s.adds.size - s.grave.size; },
};

export const RGA = rga;
