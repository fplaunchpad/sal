// Experimental sided EmbedRGA under the plain Fugue mint policy.
//
// This module deliberately does not replace embedRGA. It provides absolute
// and prefix-shared variants for differential testing and cost measurement.
// Local `prepare` freezes the generation-time decision into each insert:
//   { anchorId, side, parentId }
// The parent may be a deleted successor. Its chain is retained in the causal
// parent state (and protected by the policy-summary GC); shipping the whole
// chain per operation would make deep editing histories quadratic.

import { PMap, isPMap, eachEntry } from '../pmap.js';
import { eliasDeltaCode } from './embedRGA.js';

const ROOT = '@root';
const R = 'R', L = 'L';
const rootGap = Object.freeze({ hasR: false, succId: null });

const freezeChain = (xs) => Object.freeze(xs.map(([side, delta]) =>
  Object.freeze([side, delta])));

const chainArray = (chain, shared) => {
  if (!shared) return chain;
  const out = [];
  for (let n = chain; n; n = n.parent) out.push([n.side, n.delta]);
  out.reverse();
  return out;
};

const extendChain = (parent, side, delta, id, shared) => shared
  ? Object.freeze({ parent, side, delta, id })
  : freezeChain([...parent, [side, delta]]);

const encodeChain = (chain, code, shared) => {
  let out = '';
  for (const [side, delta] of chainArray(chain, shared)) {
    const bits = code.enc(delta);
    if (side === R) for (const b of bits) out += b === '1' ? '2' : '1';
    else for (const b of bits) out += b === '1' ? '4' : '5';
  }
  return out;
};

const cmpKey = (a, b) => {
  const x = a + '3', y = b + '3';
  return x < y ? -1 : x > y ? 1 : 0;
};

const asPMap = (m) => isPMap(m) ? m : PMap.from(m);
const put = (m, k, v) => isPMap(m) ? m.set(k, v) : new Map(m).set(k, v);
const drop = (m, k) => {
  if (isPMap(m)) return m.delete(k);
  const n = new Map(m); n.delete(k); return n;
};

function makeState(live = PMap.empty(), gaps = PMap.empty().set(ROOT, rootGap),
    chains = PMap.empty()) {
  return Object.freeze({ live, gaps, chains });
}

function liveIds3(l, a, b) {
  const ids = new Set();
  eachEntry(a.live, (id) => {
    if (b.live.has(id) || !l.live.has(id)) ids.add(id);
  });
  eachEntry(b.live, (id) => { if (!l.live.has(id)) ids.add(id); });
  return ids;
}

export function makeSidedEmbedRGA({ code = eliasDeltaCode, shared = false } = {}) {
  const chainEq = (x, y) => JSON.stringify(chainArray(x, shared)) ===
    JSON.stringify(chainArray(y, shared));

  const chainFor = (state, id) => id === null ? (shared ? null : []) : state.chains.get(id);
  const gapFor = (state, anchorId) => state.gaps.get(anchorId ?? ROOT);

  const prepare = (state, op) => {
    if (op.type !== 'ins' || (op.side && 'parentId' in op)) return op;
    if (!Number.isInteger(op.id) || op.id < 1) throw new Error('sided insert id must be positive integer');
    if (state.live.has(op.id) || state.chains.has(op.id)) throw new Error(`duplicate insert id ${op.id}`);
    if (op.anchorId !== null && op.anchorId !== undefined && !state.live.has(op.anchorId))
      throw new Error(`anchor ${op.anchorId} not live`);
    const anchorId = op.anchorId ?? null, gap = gapFor(state, anchorId);
    if (!gap) throw new Error(`missing Fugue gap for anchor ${anchorId}`);
    const side = gap.hasR && gap.succId !== null ? L : R;
    const parentId = side === L ? gap.succId : anchorId;
    const parentChain = chainFor(state, parentId);
    if (parentId !== null && parentChain === undefined)
      throw new Error(`missing retained Fugue chain for parent ${parentId}`);
    const parentTs = parentId ?? 0, delta = op.id - parentTs;
    if (!Number.isInteger(delta) || delta < 1)
      throw new Error(`delta must be positive, got ${delta}`);
    return Object.freeze({ ...op, anchorId, side, parentId });
  };

  const apply = (state, raw) => {
    const op = raw.type === 'ins' ? prepare(state, raw) : raw;
    if (op.type === 'ins') {
      if (state.live.has(op.id) || state.chains.has(op.id)) throw new Error(`duplicate insert id ${op.id}`);
      if (op.side !== R && op.side !== L) throw new Error(`invalid side ${op.side}`);
      const anchorId = op.anchorId ?? null, anchorKey = anchorId ?? ROOT;
      if (anchorId !== null && !state.live.has(anchorId)) throw new Error(`anchor ${anchorId} not live`);
      const old = state.gaps.get(anchorKey);
      if (!old) throw new Error(`missing Fugue gap for anchor ${anchorId}`);
      const parentChain = chainFor(state, op.parentId ?? null);
      const expectedParent = op.side === L ? old.succId : anchorId;
      if ((op.parentId ?? null) !== expectedParent)
        throw new Error(`Fugue parent mismatch: expected ${expectedParent}, got ${op.parentId}`);
      const delta = op.id - (op.parentId ?? 0);
      const storedChain = shared
        ? extendChain(parentChain, op.side, delta, op.id, true)
        : freezeChain([...parentChain, [op.side, delta]]);
      // Prefix-shared mode does not materialize the whole coordinate on every
      // insert. It derives keys at observation/serialization boundaries.
      const coord = shared ? null : encodeChain(storedChain, code, false);
      const rec = Object.freeze({ chain: storedChain, coord, el: op.el });
      return makeState(
        put(state.live, op.id, rec),
        put(put(state.gaps, anchorKey, Object.freeze({ hasR: true, succId: op.id })),
          op.id, Object.freeze({ hasR: false, succId: old.succId })),
        put(state.chains, op.id, storedChain));
    }
    if (op.type === 'del') {
      // Generation policy is tombstone-aware. Deletion removes the visible
      // record and its now-unusable anchor gap, but chain reclamation belongs
      // to the certified policy-summary GC; scanning the whole document on
      // every keystroke would make deletion linear.
      return makeState(drop(state.live, op.id), drop(state.gaps, op.id), state.chains);
    }
    throw new Error(`unknown sidedEmbedRGA op type: ${op.type}`);
  };

  return {
    name: shared ? 'sided-fugue-shared-experimental' : 'sided-fugue-absolute-experimental',
    code, experimental: true, needsPrepare: true, prepare,
    init: () => makeState(), apply,
    has(state, id) { return state.live.has(id); },
    applyBatch(state, ops) {
      let s = state;
      for (const op of ops) s = apply(s, op);
      return s;
    },
    readEntries(state) {
      return [...state.live.entries()].map(([id, r]) =>
        [id, r, r.coord ?? encodeChain(r.chain, code, true)]).sort(([ia, a, ka], [ib, b, kb]) => {
        const c = cmpKey(ka, kb);
        return c === 0 ? ia - ib : -c;
      }).map(([id, r]) => [id, r]);
    },
    read(state) { return this.readEntries(state).map(([, r]) => r.el); },
    readIds(state) { return this.readEntries(state).map(([id]) => id); },
    merge3(l, a, b) {
      // Delta merge from A, as in the production EmbedRGA: preserve A's HAMT
      // and touch only B's deletions/fresh births. Policy maps use the same
      // strategy; scanning for changed observations is allocation-free.
      const live = a.live.begin();
      eachEntry(l.live, (id) => { if (!b.live.has(id)) live.delete(id); });
      eachEntry(b.live, (id, rb) => {
        const ra = a.live.get(id);
        if (ra && (shared ? (ra.chain !== rb.chain && !chainEq(ra.chain, rb.chain)) : ra.coord !== rb.coord))
          throw new Error(`coordinate divergence at id ${id}`);
        else if (!ra && !l.live.has(id)) live.set(id, rb);
      });
      const mergedLive = (id) => live.has(id);
      const chains = a.chains.begin();
      const retainChain = (id) => {
        if (id === null || chains.has(id)) return;
        const ch = b.chains.get(id) ?? l.chains.get(id);
        if (ch === undefined) throw new Error(`missing retained chain ${id}`);
        chains.set(id, ch);
      };
      eachEntry(b.live, (id) => { if (mergedLive(id)) retainChain(id); });
      const gaps = a.gaps.begin();
      eachEntry(l.live, (id) => { if (!mergedLive(id)) gaps.delete(id); });
      eachEntry(b.gaps, (anchorKey, gb) => {
        if (anchorKey !== ROOT && !mergedLive(anchorKey)) return;
        const ga = a.gaps.get(anchorKey);
        if (ga === gb) return;
        if (!ga && !gb) throw new Error(`missing merged Fugue gap ${anchorKey}`);
        const candidates = [ga?.succId, gb?.succId].filter((x) => x !== null && x !== undefined);
        for (const id of candidates) retainChain(id);
        let succId = null;
        for (const id of candidates) {
          if (succId === null || cmpKey(encodeChain(chains.get(succId), code, shared),
              encodeChain(chains.get(id), code, shared)) < 0) succId = id;
        }
        const hasR = !!(ga?.hasR || gb?.hasR);
        if (!ga || ga.hasR !== hasR || ga.succId !== succId)
          gaps.set(anchorKey, Object.freeze({ hasR, succId }));
      });
      return makeState(live.freeze(), gaps.freeze(), chains.freeze());
    },
    symbolCount(state) {
      let n = 0;
      eachEntry(state.live, (_id, r) => { n += r.coord.length; });
      return n;
    },
    policyEntryCount(state) { return state.gaps.size; },
    retainedChainCount(state) { return state.chains.size; },
    encodeState(state) {
      let encodedChains;
      if (shared) {
        const nodes = new Map();
        eachEntry(state.chains, (_id, leaf) => {
          for (let n = leaf; n; n = n.parent) if (!nodes.has(n.id)) nodes.set(n.id, n);
        });
        encodedChains = [...nodes].sort(([x], [y]) => x - y)
          .map(([id, n]) => [id, n.parent?.id ?? null, n.side, n.delta]);
      } else {
        encodedChains = [...state.chains.entries()].map(([id, ch]) => [id, chainArray(ch, false)]);
      }
      return {
        live: [...state.live.entries()].map(([id, r]) =>
          [id, shared ? null : r.coord, r.el]),
        gaps: [...state.gaps.entries()].map(([id, g]) => [id, g.hasR, g.succId]),
        chains: encodedChains,
      };
    },
    decodeState(enc) {
      let chains = PMap.empty();
      for (const row of enc.chains) {
        const id = row[0];
        if (shared) {
          const [, parentId, side, delta] = row;
          const parent = parentId === null ? null : chains.get(parentId);
          if (parentId !== null && parent === undefined) throw new Error(`snapshot parent ${parentId} missing`);
          chains = chains.set(id, extendChain(parent, side, delta, id, true));
        } else {
          let ch = [];
          for (const [side, delta] of row[1]) ch = extendChain(ch, side, delta, id, false);
          chains = chains.set(id, ch);
        }
      }
      const live = PMap.from(enc.live.map(([id, coord, el]) =>
        [id, Object.freeze({ chain: chains.get(id), coord, el })]));
      const gaps = PMap.from(enc.gaps.map(([id, hasR, succId]) =>
        [id, Object.freeze({ hasR, succId })]));
      return makeState(live, gaps, chains);
    },
    fingerprint(state) {
      return JSON.stringify({
        live: [...state.live.entries()].sort(([x], [y]) => x - y)
          .map(([id, r]) => [id, r.coord ?? encodeChain(r.chain, code, true), r.el]),
        gaps: [...state.gaps.entries()].sort(([x], [y]) => String(x).localeCompare(String(y))),
      });
    },
  };
}

export const sidedEmbedRGAExperimental = makeSidedEmbedRGA();
export const sharedSidedEmbedRGAExperimental = makeSidedEmbedRGA({ shared: true });
