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
const utf8 = new TextEncoder(), unutf8 = new TextDecoder();

const putVar = (out, n) => {
  if (!Number.isSafeInteger(n) || n < 0) throw new Error(`invalid varint ${n}`);
  while (n >= 128) { out.push((n % 128) | 128); n = Math.floor(n / 128); }
  out.push(n);
};
const getVar = (u8, c) => {
  let n = 0, mul = 1;
  for (;;) {
    if (c.i >= u8.length || mul > 2 ** 49) throw new Error('damaged sided snapshot varint');
    const b = u8[c.i++]; n += (b & 127) * mul;
    if (!(b & 128)) return n;
    mul *= 128;
  }
};

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
const encodeBlock = (side, delta, code) => {
  let out = '';
  for (const b of code.enc(delta)) out += side === R
    ? (b === '1' ? '2' : '1') : (b === '1' ? '4' : '5');
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
    chains = PMap.empty(), order = null) {
  return Object.freeze({ live, gaps, chains, order });
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
  const policyOrder = (leaves) => {
    const closure = new Map();
    for (const leaf of leaves) for (let n = leaf; n; n = n.parent) {
      if (closure.has(n.id)) break;
      closure.set(n.id, n);
    }
    const children = new Map();
    for (const n of closure.values()) {
      const p = n.parent?.id ?? null;
      let bands = children.get(p);
      if (!bands) { bands = { L: [], R: [] }; children.set(p, bands); }
      bands[n.side].push(n);
    }
    const order = (xs) => xs.sort((a, b) => {
      const c = cmpKey(encodeBlock(a.side, a.delta, code), encodeBlock(b.side, b.delta, code));
      return c === 0 ? a.id - b.id : -c;
    });
    for (const bands of children.values()) { order(bands.L); order(bands.R); }
    const out = [], walk = (n) => {
      const bands = children.get(n.id);
      for (const x of bands?.L ?? []) walk(x);
      out.push(n);
      for (const x of bands?.R ?? []) walk(x);
    };
    for (const n of children.get(null)?.L ?? []) walk(n);
    for (const n of children.get(null)?.R ?? []) walk(n);
    return out;
  };

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
      if (shared) {
        if (state.order) return state.order.flatMap((id) => {
          const rec = state.live.get(id); return rec ? [[id, rec]] : [];
        });
        return policyOrder(state.chains.values()).flatMap((n) => {
          const rec = state.live.get(n.id); return rec ? [[n.id, rec]] : [];
        });
      }
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
        const roots = new Set(state.live.keys());
        eachEntry(state.gaps, (_id, g) => { if (g.succId !== null) roots.add(g.succId); });
        for (const id of roots) {
          const leaf = state.chains.get(id);
          if (!leaf) throw new Error(`retained snapshot chain ${id} missing`);
          for (let n = leaf; n; n = n.parent) {
            if (nodes.has(n.id)) break;
            nodes.set(n.id, n);
          }
        }
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
    /** Compact lossless candidate snapshot. Shared mode stores every retained
     * policy node once as a parent link; it never repeats whole coordinates. */
    encodeSnapshot(state, { validate = false } = {}) {
      if (!shared) return utf8.encode(JSON.stringify(this.encodeState(state)));
      const nodes = new Map(), roots = new Set(), liveById = new Map(), gapsById = new Map();
      eachEntry(state.live, (id, rec) => { roots.add(id); liveById.set(id, rec); });
      eachEntry(state.gaps, (id, g) => {
        gapsById.set(id, g); if (g.succId !== null) roots.add(g.succId);
      });
      for (const id of roots) {
        const leaf = state.chains.get(id);
        if (!leaf) throw new Error(`retained snapshot chain ${id} missing`);
        for (let n = leaf; n; n = n.parent) {
          if (nodes.has(n.id)) break;
          nodes.set(n.id, n);
        }
      }
      const ns = [...nodes].sort(([x], [y]) => x - y), out = [2];
      putVar(out, ns.length);
      let prev = 0;
      for (const [id] of ns) { putVar(out, id - prev); prev = id; }
      const tags = [];
      for (let i = 0; i < ns.length; i += 4) {
        let byte = 0;
        for (let j = 0; j < 4 && i + j < ns.length; j++) {
          const [id, n] = ns[i + j], parentId = n.parent?.id ?? 0;
          const tag = (n.side === L ? 1 : 0) | (parentId !== id - 1 ? 2 : 0);
          byte |= tag << (2 * j);
        }
        tags.push(byte);
      }
      out.push(...tags);
      for (const [id, n] of ns) {
        const parentId = n.parent?.id ?? 0;
        if (parentId !== id - 1) putVar(out, id - parentId);
      }
      const live = ns.filter(([id]) => liveById.has(id));
      const liveBits = [];
      for (let i = 0; i < ns.length; i += 8) {
        let byte = 0;
        for (let j = 0; j < 8 && i + j < ns.length; j++)
          if (liveById.has(ns[i + j][0])) byte |= 1 << j;
        liveBits.push(byte);
      }
      out.push(...liveBits);
      const texts = live.map(([id]) => {
        const el = liveById.get(id).el, c = el.length === 1 ? el.charCodeAt(0) : 128;
        return c < 128 ? Uint8Array.of(c) : utf8.encode(el);
      }), lenBits = [];
      for (let i = 0; i < texts.length; i += 8) {
        let byte = 0;
        for (let j = 0; j < 8 && i + j < texts.length; j++)
          if (texts[i + j].length !== 1) byte |= 1 << j;
        lenBits.push(byte);
      }
      out.push(...lenBits);
      for (const bytes of texts) if (bytes.length !== 1) putVar(out, bytes.length);
      for (const bytes of texts) out.push(...bytes);
      // Successors are the immediate next retained policy node. Store only
      // hasR. Tests use `validate` to check this derivation against the full
      // semantic summary; production encoding need not recompute it twice.
      let ordered, pos;
      if (validate) {
        ordered = policyOrder(ns.map(([, n]) => n));
        pos = new Map(ordered.map((n, i) => [n.id, i]));
      }
      const anchors = [ROOT, ...live.map(([id]) => id)], bits = [];
      for (let i = 0; i < anchors.length; i += 8) {
        let byte = 0;
        for (let j = 0; j < 8 && i + j < anchors.length; j++) {
          const id = anchors[i + j], g = gapsById.get(id);
          if (!g) throw new Error(`snapshot gap ${id} missing`);
          if (validate) {
            const successor = id === ROOT ? (ordered[0]?.id ?? null)
              : (ordered[(pos.get(id) ?? -1) + 1]?.id ?? null);
            if (successor !== g.succId)
              throw new Error(`derived successor mismatch at ${id}: ${successor} != ${g.succId}`);
          }
          if (g.hasR) byte |= 1 << j;
        }
        bits.push(byte);
      }
      putVar(out, bits.length); out.push(...bits);
      return Uint8Array.from(out);
    },
    decodeSnapshot(u8) {
      if (!shared) return this.decodeState(JSON.parse(unutf8.decode(u8)));
      const c = { i: 0 };
      if (u8[c.i++] !== 2) throw new Error('unsupported sided snapshot version');
      const nn = getVar(u8, c), all = new Map(), ids = []; let prev = 0;
      for (let k = 0; k < nn; k++) { const id = prev + getVar(u8, c); ids.push(id); prev = id; }
      const tags = u8.subarray(c.i, c.i + Math.ceil(nn / 4)); c.i += tags.length;
      for (let k = 0; k < nn; k++) {
        const id = ids[k], tag = (tags[k >> 2] >> (2 * (k & 3))) & 3;
        const parentId = tag & 2 ? id - getVar(u8, c) : id - 1;
        const side = tag & 1 ? L : R, delta = id - parentId;
        const parent = parentId === 0 ? null : all.get(parentId);
        if (parentId !== 0 && !parent) throw new Error(`snapshot parent ${parentId} missing`);
        all.set(id, extendChain(parent, side, delta, id, true));
      }
      const liveMapBits = u8.subarray(c.i, c.i + Math.ceil(nn / 8)); c.i += liveMapBits.length;
      const liveIds = ids.filter((_id, i) => liveMapBits[i >> 3] & (1 << (i & 7)));
      const lenBits = u8.subarray(c.i, c.i + Math.ceil(liveIds.length / 8)); c.i += lenBits.length;
      const lens = liveIds.map((_id, i) => lenBits[i >> 3] & (1 << (i & 7)) ? getVar(u8, c) : 1);
      const liveT = PMap.empty().begin();
      for (let k = 0; k < liveIds.length; k++) {
        const id = liveIds[k], len = lens[k], el = unutf8.decode(u8.subarray(c.i, c.i + len)); c.i += len;
        liveT.set(id, Object.freeze({ chain: all.get(id), coord: null, el }));
      }
      const bitLen = getVar(u8, c), bits = u8.subarray(c.i, c.i + bitLen); c.i += bitLen;
      if (bitLen !== Math.ceil((liveIds.length + 1) / 8)) throw new Error('bad sided gap bitset');
      const ordered = policyOrder(all.values()), pos = new Map(ordered.map((n, i) => [n.id, i]));
      const anchors = [ROOT, ...liveIds], gapsT = PMap.empty().begin();
      for (let i = 0; i < anchors.length; i++) {
        const id = anchors[i], successor = id === ROOT ? (ordered[0]?.id ?? null)
          : (ordered[(pos.get(id) ?? -1) + 1]?.id ?? null);
        gapsT.set(id, Object.freeze({ hasR: !!(bits[i >> 3] & (1 << (i & 7))), succId: successor }));
      }
      if (c.i !== u8.length) throw new Error('trailing sided snapshot bytes');
      return makeState(liveT.freeze(), gapsT.freeze(), PMap.from(all), ordered.map((n) => n.id));
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
