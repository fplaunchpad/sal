// Compact Fugue representation following the machine-checked LiveGap
// observation in SidedRGA_FuguePolicyGC.lean. Retained birth records carry
// one gap summary; coordinate chains are shared anonymous path nodes. A dead
// successor keeps an id only when some retained gap names it.

import { PMap, eachEntry } from '../pmap.js';
import { eliasDeltaCode } from './embedRGA.js';
import { sharedSidedEmbedRGAExperimental as snapshotOracle } from './sidedEmbedRGA.js';

const R = 'R', L = 'L';
const chainNode = (parent, side, delta) => Object.freeze({ parent, side, delta });
const gap0 = Object.freeze({ hasR: false, succId: null, succChain: null });
const gap = (hasR, succId, succChain) => Object.freeze({ hasR, succId, succChain });
const rec = (chain, el, gapValue) => Object.freeze({ chain, el, gap: gapValue });
const block = (side, delta, code) => {
  let out = '';
  for (const b of code.enc(delta)) out += side === R
    ? (b === '1' ? '2' : '1') : (b === '1' ? '4' : '5');
  return out;
};
const coord = (chain, code) => {
  const xs = [];
  for (let p = chain; p; p = p.parent) xs.push(p);
  let out = '';
  for (let i = xs.length - 1; i >= 0; i--) out += block(xs[i].side, xs[i].delta, code);
  return out;
};
const keyCmp = (a, b) => {
  const x = a + '3', y = b + '3'; return x < y ? -1 : x > y ? 1 : 0;
};
const b64 = (u8) => {
  let s = '';
  for (let i = 0; i < u8.length; i += 0x8000)
    s += String.fromCharCode(...u8.subarray(i, i + 0x8000));
  return btoa(s);
};

export function makeLiveGapSidedEmbedRGA({ code = eliasDeltaCode } = {}) {
  const init = () => Object.freeze({ records: PMap.empty(), rootGap: gap0, order: null });
  const anchorGap = (s, id) => id === null ? s.rootGap : s.records.get(id)?.gap;
  const anchorChain = (s, id) => id === null ? null : s.records.get(id)?.chain;
  const parentChain = (s, id, g) => {
    if (id === null) return null;
    const direct = s.records.get(id)?.chain;
    if (direct) return direct;
    if (g?.succId === id) return g.succChain;
    throw new Error(`policy parent chain ${id} missing`);
  };

  const prepare = (s, op) => {
    if (op.type !== 'ins' || (op.side && 'parentId' in op)) return op;
    if (!Number.isInteger(op.id) || op.id < 1 || s.records.has(op.id))
      throw new Error(`bad fresh id ${op.id}`);
    const anchorId = op.anchorId ?? null, g = anchorGap(s, anchorId);
    if (!g) throw new Error(`anchor ${anchorId} not retained`);
    const side = g.hasR && g.succId !== null ? L : R;
    const parentId = side === L ? g.succId : anchorId;
    if (op.id <= (parentId ?? 0)) throw new Error('non-positive delta');
    return Object.freeze({ ...op, anchorId, side, parentId });
  };

  const apply = (s, raw) => {
    if (raw.type === 'del') {
      if (!s.records.has(raw.id)) return s;
      return Object.freeze({ records: s.records.delete(raw.id), rootGap: s.rootGap, order: null });
    }
    if (raw.type !== 'ins') throw new Error(`unknown LiveGap sided op ${raw.type}`);
    const op = prepare(s, raw), anchorId = op.anchorId ?? null;
    const g = anchorGap(s, anchorId);
    const expected = op.side === L ? g.succId : anchorId;
    if ((op.parentId ?? null) !== expected) throw new Error('Fugue parent mismatch');
    const pc = parentChain(s, op.parentId ?? null, g);
    const ch = chainNode(pc, op.side, op.id - (op.parentId ?? 0));
    const updatedGap = gap(true, op.id, ch);
    const t = s.records.begin();
    if (anchorId !== null) {
      const a = s.records.get(anchorId); t.set(anchorId, rec(a.chain, a.el, updatedGap));
    }
    t.set(op.id, rec(ch, op.el, gap(false, g.succId, g.succChain)));
    return Object.freeze({ records: t.freeze(),
      rootGap: anchorId === null ? updatedGap : s.rootGap, order: null });
  };

  const allChains = (s) => {
    const seen = new Set(), stack = [];
    const add = (ch) => { if (ch) stack.push(ch); };
    add(s.rootGap.succChain);
    eachEntry(s.records, (_id, r) => { add(r.chain); add(r.gap.succChain); });
    while (stack.length) {
      const ch = stack.pop(); if (seen.has(ch)) continue;
      seen.add(ch); add(ch.parent);
    }
    return seen;
  };

  const policyOrder = (s) => {
    const chains = allChains(s), children = new Map(), at = new Map();
    eachEntry(s.records, (id, r) => at.set(r.chain, [id, r]));
    for (const ch of chains) {
      let xs = children.get(ch.parent); if (!xs) children.set(ch.parent, xs = []);
      xs.push(ch);
    }
    for (const xs of children.values()) xs.sort((a, b) =>
      -keyCmp(block(a.side, a.delta, code), block(b.side, b.delta, code)));
    const out = [], roots = children.get(null) ?? [], stack = [];
    for (let i = roots.length - 1; i >= 0; i--) stack.push({ ch: roots[i], emit: false });
    while (stack.length) {
      const x = stack.pop();
      if (x.emit) { const r = at.get(x.ch); if (r) out.push(r); continue; }
      const kids = children.get(x.ch) ?? [], ls = kids.filter((c) => c.side === L),
        rs = kids.filter((c) => c.side === R);
      for (let i = rs.length - 1; i >= 0; i--) stack.push({ ch: rs[i], emit: false });
      stack.push({ ch: x.ch, emit: true });
      for (let i = ls.length - 1; i >= 0; i--) stack.push({ ch: ls[i], emit: false });
    }
    return out;
  };
  const readEntries = (s) => s.order
    ? s.order.map((id) => [id, s.records.get(id)]).filter(([, r]) => r !== undefined)
    : policyOrder(s);

  const maxSucc = (a, b) => {
    if (a.succId === null) return b;
    if (b.succId === null) return a;
    return keyCmp(coord(a.succChain, code), coord(b.succChain, code)) < 0 ? b : a;
  };
  const mergeGap = (a, b) => {
    if (a === b) return a;
    const winner = maxSucc(a, b);
    return gap(a.hasR || b.hasR, winner.succId, winner.succChain);
  };
  const merge3 = (l, a, b) => {
    const ids = new Set();
    eachEntry(a.records, (id) => ids.add(id)); eachEntry(b.records, (id) => ids.add(id));
    const t = PMap.empty().begin();
    for (const id of ids) {
      const ra = a.records.get(id), rb = b.records.get(id), rl = l.records.get(id);
      let keep;
      if (ra && rb) keep = rec(ra.chain, ra.el, mergeGap(ra.gap, rb.gap));
      else if (!rl) keep = ra ?? rb; // concurrent insertion
      else keep = null;              // deletion from either branch
      if (keep) t.set(id, keep);
    }
    return Object.freeze({ records: t.freeze(), rootGap: mergeGap(a.rootGap, b.rootGap), order: null });
  };

  // Remove settled Peritext birth records after its marks layer has selected
  // retention roots. Their chain nodes survive anonymously when another
  // record or LiveGap still references them.
  const dropRecords = (s, ids) => {
    const t = s.records.begin();
    for (const id of ids) t.delete(id);
    return Object.freeze({ records: t.freeze(), rootGap: s.rootGap, order: null });
  };

  const materialize = (s) => {
    const full = new Map(), byId = new Map();
    const ensure = (ch) => {
      if (!ch) return null;
      if (full.has(ch)) return full.get(ch);
      const missing = [];
      for (let p = ch; p && !full.has(p); p = p.parent) missing.push(p);
      let parent = missing.at(-1)?.parent ? full.get(missing.at(-1).parent) : null;
      for (let i = missing.length - 1; i >= 0; i--) {
        const p = missing[i], id = (parent?.id ?? 0) + p.delta;
        const f = Object.freeze({ parent, side: p.side, delta: p.delta, id });
        full.set(p, f); byId.set(id, { chain: f, el: undefined, gap: null }); parent = f;
      }
      return full.get(ch);
    };
    for (const ch of allChains(s)) ensure(ch);
    eachEntry(s.records, (id, r) => byId.set(id, {
      chain: ensure(r.chain), el: r.el,
      gap: { hasR: r.gap.hasR, succId: r.gap.succId },
    }));
    return { nodes: PMap.from(byId), rootGap: {
      hasR: s.rootGap.hasR, succId: s.rootGap.succId,
    } };
  };
  const encodeState = (s) => {
    const m = materialize(s);
    return [...snapshotOracle.encodeSnapshot(null,
      { unifiedNodes: m.nodes, unifiedRootGap: m.rootGap })];
  };
  const decodeState = (enc) => snapshotOracle.decodeSnapshot(Uint8Array.from(enc), {
    build: ({ chains, live, gaps, order }) => {
      const anon = new Map();
      const make = (ch) => {
        if (!ch) return null;
        if (anon.has(ch)) return anon.get(ch);
        const missing = [];
        for (let p = ch; p && !anon.has(p); p = p.parent) missing.push(p);
        let parent = missing.at(-1)?.parent ? anon.get(missing.at(-1).parent) : null;
        for (let i = missing.length - 1; i >= 0; i--) {
          const p = missing[i], a = chainNode(parent, p.side, p.delta);
          anon.set(p, a); parent = a;
        }
        return anon.get(ch);
      };
      const records = PMap.empty().begin();
      for (const [id, r] of live) {
        const g = gaps.get(id), sc = g.succId === null ? null : chains.get(g.succId);
        records.set(id, rec(make(r.chain), r.el, gap(g.hasR, g.succId, make(sc))));
      }
      const rg = gaps.get('@root'), rsc = rg.succId === null ? null : chains.get(rg.succId);
      return Object.freeze({ records: records.freeze(),
        rootGap: gap(rg.hasR, rg.succId, make(rsc)), order });
    },
  });

  return {
    name: 'sided-fugue-live-gap', needsPrepare: true,
    init, prepare, apply, merge3,
    has: (s, id) => s.records.has(id), readEntries,
    read: (s) => readEntries(s).map(([, r]) => r.el),
    readIds: (s) => readEntries(s).map(([id]) => id),
    applyBatch(s, ops) { for (const op of ops) s = apply(s, op); return s; },
    dropRecords,
    nodeCount: (s) => allChains(s).size,
    recordCount: (s) => s.records.size,
    encodeState, decodeState,
    fingerprint: (s) => b64(Uint8Array.from(encodeState(s))),
  };
}

export const liveGapSidedEmbedRGA = makeLiveGapSidedEmbedRGA();
