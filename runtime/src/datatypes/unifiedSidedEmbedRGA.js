// Experimental one-HAMT representation of the shared sided/Fugue kernel.
// A node record co-locates immutable chain provenance, optional live content,
// and the live-anchor gap observation. The split-map implementation remains
// the oracle and production-default candidate.

import { PMap, eachEntry } from '../pmap.js';
import { eliasDeltaCode } from './embedRGA.js';
import { sharedSidedEmbedRGAExperimental as split } from './sidedEmbedRGA.js';

const R = 'R', L = 'L';
const rootGap0 = Object.freeze({ hasR: false, succId: null });
const live = (n) => n?.el !== undefined;
const node = (chain, el, gap) => Object.freeze({ chain, el, gap });
const chainNode = (parent, side, delta, id) => Object.freeze({ parent, side, delta, id });

const block = (side, delta, code) => {
  let out = '';
  for (const b of code.enc(delta)) out += side === R
    ? (b === '1' ? '2' : '1') : (b === '1' ? '4' : '5');
  return out;
};
const coord = (chain, code) => {
  const xs = [];
  for (let n = chain; n; n = n.parent) xs.push(n);
  let out = '';
  for (let i = xs.length - 1; i >= 0; i--) out += block(xs[i].side, xs[i].delta, code);
  return out;
};
const keyCmp = (a, b) => {
  const x = a + '3', y = b + '3'; return x < y ? -1 : x > y ? 1 : 0;
};

export function makeUnifiedSidedEmbedRGA({ code = eliasDeltaCode } = {}) {
  const init = () => Object.freeze({ nodes: PMap.empty(), rootGap: rootGap0, order: null });
  const gap = (s, id) => id === null ? s.rootGap : s.nodes.get(id)?.gap;
  const chain = (s, id) => id === null ? null : s.nodes.get(id)?.chain;

  const prepare = (s, op) => {
    if (op.type !== 'ins' || (op.side && 'parentId' in op)) return op;
    if (!Number.isInteger(op.id) || op.id < 1 || s.nodes.has(op.id)) throw new Error(`bad fresh id ${op.id}`);
    const anchorId = op.anchorId ?? null;
    if (anchorId !== null && !live(s.nodes.get(anchorId))) throw new Error(`anchor ${anchorId} not live`);
    const g = gap(s, anchorId); if (!g) throw new Error(`gap ${anchorId} missing`);
    const side = g.hasR && g.succId !== null ? L : R;
    const parentId = side === L ? g.succId : anchorId;
    if (parentId !== null && !chain(s, parentId)) throw new Error(`parent chain ${parentId} missing`);
    if (op.id <= (parentId ?? 0)) throw new Error('non-positive delta');
    return Object.freeze({ ...op, anchorId, side, parentId });
  };

  const apply = (s, raw) => {
    const op = raw.type === 'ins' ? prepare(s, raw) : raw;
    if (op.type === 'ins') {
      const anchorId = op.anchorId ?? null, g = gap(s, anchorId);
      const expected = op.side === L ? g.succId : anchorId;
      if ((op.parentId ?? null) !== expected) throw new Error('Fugue parent mismatch');
      const ch = chainNode(chain(s, op.parentId ?? null), op.side,
        op.id - (op.parentId ?? 0), op.id);
      const t = s.nodes.begin();
      if (anchorId !== null) {
        const a = s.nodes.get(anchorId);
        t.set(anchorId, node(a.chain, a.el, Object.freeze({ hasR: true, succId: op.id })));
      }
      t.set(op.id, node(ch, op.el, Object.freeze({ hasR: false, succId: g.succId })));
      return Object.freeze({ nodes: t.freeze(),
        rootGap: anchorId === null ? Object.freeze({ hasR: true, succId: op.id }) : s.rootGap,
        order: null });
    }
    if (op.type === 'del') {
      const n = s.nodes.get(op.id); if (!live(n)) return s;
      return Object.freeze({ nodes: s.nodes.set(op.id, node(n.chain, undefined, null)),
        rootGap: s.rootGap, order: null });
    }
    throw new Error(`unknown unified sided op ${op.type}`);
  };

  const policyOrder = (nodes) => {
    const children = new Map();
    eachEntry(nodes, (_id, n) => {
      const p = n.chain.parent?.id ?? null;
      let b = children.get(p); if (!b) { b = { L: [], R: [] }; children.set(p, b); }
      b[n.chain.side].push(n.chain);
    });
    const sort = (xs) => xs.sort((a, b) => {
      const c = keyCmp(block(a.side, a.delta, code), block(b.side, b.delta, code));
      return c === 0 ? a.id - b.id : -c;
    });
    for (const b of children.values()) { sort(b.L); sort(b.R); }
    const out = [], walk = (n) => {
      const b = children.get(n.id); for (const x of b?.L ?? []) walk(x);
      out.push(n.id); for (const x of b?.R ?? []) walk(x);
    };
    for (const n of children.get(null)?.L ?? []) walk(n);
    for (const n of children.get(null)?.R ?? []) walk(n);
    return out;
  };

  const readEntries = (s) => (s.order ?? policyOrder(s.nodes)).flatMap((id) => {
    const n = s.nodes.get(id); return live(n) ? [[id, { chain: n.chain, el: n.el }]] : [];
  });

  const mergeGap = (ga, gb, nodes) => {
    if (ga === gb) return ga;
    const cs = [ga?.succId, gb?.succId].filter((x) => x !== null && x !== undefined);
    let succId = null;
    for (const id of cs) if (succId === null || keyCmp(coord(nodes.get(succId).chain, code),
      coord(nodes.get(id).chain, code)) < 0) succId = id;
    return Object.freeze({ hasR: !!(ga?.hasR || gb?.hasR), succId });
  };

  const merge3 = (l, a, b) => {
    const t = a.nodes.begin();
    eachEntry(b.nodes, (id, nb) => {
      const na = a.nodes.get(id), nl = l.nodes.get(id);
      if (!na) { t.set(id, nb); return; }
      if (na.chain !== nb.chain && coord(na.chain, code) !== coord(nb.chain, code))
        throw new Error(`chain divergence ${id}`);
      const isLive = (live(na) && live(nb)) || (live(na) && !live(nl)) || (live(nb) && !live(nl));
      const el = isLive ? (live(na) ? na.el : nb.el) : undefined;
      const g = isLive ? mergeGap(na.gap, nb.gap, { get: (x) => a.nodes.get(x) ?? b.nodes.get(x) }) : null;
      if (el !== na.el || g !== na.gap) t.set(id, node(na.chain, el, g));
    });
    eachEntry(l.nodes, (id, nl) => {
      if (b.nodes.has(id) || !a.nodes.has(id)) return;
      const na = a.nodes.get(id);
      if (live(nl) && live(na)) t.set(id, node(na.chain, undefined, null));
    });
    return Object.freeze({ nodes: t.freeze(), rootGap: mergeGap(a.rootGap, b.rootGap,
      { get: (x) => a.nodes.get(x) ?? b.nodes.get(x) }), order: null });
  };

  const toSplit = (s) => {
    const lt = PMap.empty().begin(), gt = PMap.empty().begin(), ct = PMap.empty().begin();
    gt.set('@root', s.rootGap);
    eachEntry(s.nodes, (id, n) => {
      ct.set(id, n.chain);
      if (live(n)) { lt.set(id, Object.freeze({ chain: n.chain, coord: null, el: n.el })); gt.set(id, n.gap); }
    });
    return Object.freeze({ live: lt.freeze(), gaps: gt.freeze(), chains: ct.freeze(), order: s.order });
  };
  const fromSplit = (s) => {
    const t = PMap.empty().begin();
    eachEntry(s.chains, (id, ch) => {
      const r = s.live.get(id); t.set(id, node(ch, r?.el, r ? s.gaps.get(id) : null));
    });
    return Object.freeze({ nodes: t.freeze(), rootGap: s.gaps.get('@root'), order: s.order });
  };

  return {
    name: 'sided-fugue-unified-experimental', experimental: true, needsPrepare: true,
    init, prepare, apply, merge3, has: (s, id) => live(s.nodes.get(id)), readEntries,
    read: (s) => readEntries(s).map(([, r]) => r.el),
    readIds: (s) => readEntries(s).map(([id]) => id),
    applyBatch(s, ops) { for (const op of ops) s = apply(s, op); return s; },
    encodeSnapshot: (s, opts) => split.encodeSnapshot(toSplit(s), opts),
    decodeSnapshot: (bytes) => fromSplit(split.decodeSnapshot(bytes)),
    fingerprint: (s) => split.fingerprint(toSplit(s)),
    liveCount: (s) => readEntries(s).length,
  };
}

export const unifiedSidedEmbedRGAExperimental = makeUnifiedSidedEmbedRGA();
