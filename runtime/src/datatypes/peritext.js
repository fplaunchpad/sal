// PERITEXT: the verified DOCUMENT-ORDER rich-text mark model as a runtime
// datatype. This is the bridge from the verified read model to the editor: it
// plugs into DistributedReplica over the SAME {init, apply, merge3, read}
// contract as embedRGA and orset, so rich text gets delta gossip + content
// addressing + commit GC for free, with no Peritext-specific runtime code.
//
// STATE = { text: { shadow, deleted }, marks }
//   * text.shadow : an embedRGA state holding EVERY inserted character (birth
//     order + reading order). We reuse embedRGA for insert / reading order /
//     merge. It is INSERT-ONLY: characters are never removed from it.
//   * text.deleted : a grow-only Set of logically-deleted character ids.
//   * marks : Map mid -> { mtype, value, startId, endId, startSide, endSide,
//     ts, removed }. removed=true is a removeMark (a negative mark); LWW per
//     (char, mtype) by mid resolves add-vs-remove at READ time.
//
// WHY A SHADOW + deleted SET, not embedRGA's native (pure-removal) delete:
// the document-order resolver rehomes a DEAD boundary anchor to its nearest
// surviving neighbour IN READING ORDER, which needs the dead anchor's birth
// position. embedRGA.del erases the record (and its coordinate), destroying
// exactly that. So this is DocD: births are kept, a separate deleted set marks
// the survivors. live = birth order minus deleted (P3, the same identity
// embedRGA.merge preserves). This is ALSO why state compaction is (correctly)
// refused here: pruning a dead anchor's coordinate would break mark rehoming
// (see the note at the bottom).

import { embedRGA } from './embedRGA.js';
import { sidedEmbedRGAReleaseCandidate } from './unifiedSidedEmbedRGA.js';
import { PMap, PSet, isPMap, isPSet, eachEntry } from '../pmap.js';

// Members of a PSet (hash order) or a legacy plain Set (insertion order):
// order-insensitive scans only (unions into content-canonical containers).
const eachMember = (s, fn) => {
  if (isPSet(s)) s.forEachRaw(fn);
  else for (const x of s) fn(x);
};

// ---------------------------------------------------------------- resolver ctx
// One pass over the shadow builds everything the resolver reads.
function buildCtx(state, textRGA) {
  const entries = textRGA.readEntries(state.text.shadow); // reading order
  const birth = entries.map(([id]) => id);                 // all ids, in order
  const cp = new Map(entries.map(([id, r]) => [id, r.el])); // id -> codepoint
  const deleted = state.text.deleted;
  const live = birth.filter((c) => !deleted.has(c));       // survivors, in order
  const pos = new Map(live.map((c, i) => [c, i]));          // live id -> live idx
  const bpos = new Map(birth.map((c, i) => [c, i]));        // birth id -> birth idx
  const hasBirth = (id) => typeof textRGA.has === 'function'
    ? textRGA.has(state.text.shadow, id) : state.text.shadow.has(id);
  return { birth, live, cp, deleted, pos, bpos, shadow: state.text.shadow, hasBirth };
}

const isLive = (ctx, a) => ctx.hasBirth(a) && !ctx.deleted.has(a);

// Nearest live id strictly one `step` away from birth index `i` (or null).
function scan(birth, deleted, i, step) {
  let j = i + step;
  while (j >= 0 && j < birth.length) {
    if (!deleted.has(birth[j])) return birth[j];
    j += step;
  }
  return null;
}

// First covered live index (null = the span collapsed). Growth compares
// char id > mark.ts ("newer than the mark"), the RGA opId tiebreak (ts
// defaults to mid).
function startIndex(m, ctx) {
  const { live, birth, pos, bpos, deleted } = ctx;
  let a = m.startId;
  if (!isLive(ctx, a)) {
    a = scan(birth, deleted, bpos.get(a), m.startSide === 'before' ? +1 : -1);
    if (a === null) return m.startSide === 'before' ? null : 0;
  }
  const i = pos.get(a);
  if (m.startSide === 'before') return i;      // inner start: stable, no left growth
  let first = i + 1;                           // outer start: skip the newer-than-mark run
  while (first < live.length && live[first] > m.ts) first += 1;
  return first;
}

// Last covered live index INCLUSIVE (null = collapse). endSide=after GROWS
// right; before does not.
function endIndex(m, ctx) {
  const { live, birth, pos, bpos, deleted } = ctx;
  const n = live.length;
  let a = m.endId;
  if (!isLive(ctx, a)) {
    a = scan(birth, deleted, bpos.get(a), m.endSide === 'after' ? -1 : +1);
    if (a === null) return m.endSide === 'after' ? null : n - 1;
  }
  const i = pos.get(a);
  if (m.endSide === 'after') {
    let last = i;
    while (last + 1 < n && live[last + 1] > m.ts) last += 1;
    return last;
  }
  let last = i - 1;                            // outer end: step back over the newer run
  while (last >= 0 && live[last] > m.ts) last -= 1;
  return last;
}

// The live ids a single mark covers (the inclusive interval slice).
function coveredIds(m, ctx) {
  const first = startIndex(m, ctx);
  const last = endIndex(m, ctx);
  if (first === null || last === null || first > last) return [];
  return ctx.live.slice(first, last + 1);
}

// The full document-order render: per live char, its ACTIVE mark set. Per
// (char, mtype) the covering mark with the highest mid wins (LWW); an active
// mark is one whose winner is not a removeMark.
function renderDoc(state, textRGA) {
  const ctx = buildCtx(state, textRGA);
  const best = new Map();                      // live id -> Map(mtype -> {mid, removed, value})
  for (const c of ctx.live) best.set(c, new Map());
  for (const m of state.marks.values()) {
    for (const c of coveredIds(m, ctx)) {
      const bc = best.get(c);
      const cur = bc.get(m.mtype);
      if (cur === undefined || m.mid > cur.mid) {
        bc.set(m.mtype, { mid: m.mid, removed: m.removed, value: m.value });
      }
    }
  }
  return ctx.live.map((c) => {
    const active = [];
    for (const [mtype, w] of best.get(c)) if (!w.removed) active.push({ mtype, value: w.value });
    active.sort((x, y) => (x.mtype < y.mtype ? -1 : x.mtype > y.mtype ? 1 : 0));
    return { id: c, char: ctx.cp.get(c), marks: active };
  });
}

const frozenMark = (op) => Object.freeze({
  mid: op.mid, mtype: op.mtype, value: op.value ?? null,
  startId: op.startId, endId: op.endId,
  startSide: op.startSide ?? 'before', endSide: op.endSide ?? 'after',
  ts: op.ts ?? op.mid, removed: op.type === 'removeMark',
});

/** Build the same Peritext semantics over any insertion-order kernel exposing
 * the EmbedRGA contract. This makes the prefix-sharing representation a
 * representation choice, rather than a second rich-text semantics. */
export function makePeritext(textRGA = embedRGA) {
return {
  needsPrepare: !!textRGA.needsPrepare,
  /** state: { text: { shadow: PMap (via embedRGA), deleted: PSet }, marks:
   *  PMap } -- persistent containers: apply is O(log n), no live-set copy.
   *  Legacy Set/Map sub-states are accepted read-only and copied on write. */
  init() {
    return { text: { shadow: textRGA.init(), deleted: PSet.empty() }, marks: PMap.empty() };
  },

  prepare(state, op) {
    if (op.type !== 'ins' || typeof textRGA.prepare !== 'function') return op;
    return textRGA.prepare(state.text.shadow, op);
  },

  apply(state, op) {
    if (op.type === 'ins') {
      const shadow = textRGA.apply(state.text.shadow, op);
      return { text: { shadow, deleted: state.text.deleted }, marks: state.marks };
    }
    if (op.type === 'del') {
      // logical delete (birth kept in shadow)
      const deleted = isPSet(state.text.deleted)
        ? state.text.deleted.add(op.id)
        : new Set(state.text.deleted).add(op.id);
      return { text: { shadow: state.text.shadow, deleted }, marks: state.marks };
    }
    if (op.type === 'addMark' || op.type === 'removeMark') {
      // mid is globally unique (add-only map)
      const marks = isPMap(state.marks)
        ? state.marks.set(op.mid, frozenMark(op))
        : new Map(state.marks).set(op.mid, frozenMark(op));
      return { text: state.text, marks };
    }
    throw new Error(`unknown peritext op type: ${op.type}`);
  },

  /** Batch apply in ONE transient pass per component (identical to folding
   *  apply: ins/del/mark ops touch disjoint components, and each component
   *  sees its own ops in order). */
  applyBatch(state, ops) {
    const insOps = [];
    const deleted = (isPSet(state.text.deleted)
      ? state.text.deleted : PSet.from(state.text.deleted)).begin();
    const marks = (isPMap(state.marks) ? state.marks : PMap.from(state.marks)).begin();
    for (const op of ops) {
      if (op.type === 'ins') insOps.push(op);
      else if (op.type === 'del') deleted.add(op.id);
      else if (op.type === 'addMark' || op.type === 'removeMark') marks.set(op.mid, frozenMark(op));
      else throw new Error(`unknown peritext op type: ${op.type}`);
    }
    const shadow = insOps.length ? textRGA.applyBatch(state.text.shadow, insOps) : state.text.shadow;
    return { text: { shadow, deleted: deleted.freeze() }, marks: marks.freeze() };
  },

  // Text: births by embedRGA.merge3 (union of insert-only shadows); deletes by
  // union (grow-only, delete-wins); marks by union on mid (grow-only G-map).
  // Unions extend A's containers in a transient (structural sharing; adding
  // an already-present member is an allocation-free no-op). mid is globally
  // unique, so a mark present under one mid is the same mark everywhere and
  // is never overwritten. Hash-order scans: content-canonical outputs.
  merge3(l, a, b) {
    const shadow = textRGA.merge3(l.text.shadow, a.text.shadow, b.text.shadow);
    const ad = a.text.deleted;
    const deleted = (isPSet(ad) ? ad : PSet.from(ad)).begin();
    eachMember(l.text.deleted, (x) => deleted.add(x));
    eachMember(b.text.deleted, (x) => deleted.add(x));
    const marks = (isPMap(a.marks) ? a.marks : PMap.from(a.marks)).begin();
    eachEntry(l.marks, (mid, m) => { if (!marks.has(mid)) marks.set(mid, m); });
    eachEntry(b.marks, (mid, m) => { if (!marks.has(mid)) marks.set(mid, m); });
    return { text: { shadow, deleted: deleted.freeze() }, marks: marks.freeze() };
  },

  // The DOCUMENT-ORDER rich-text read: [{ id, char, marks:[{mtype,value}] }].
  read(state) { return renderDoc(state, textRGA); },

  // Flag projection [(char, isMtype)], the rendered flag view. A pure
  // projection of read(), not a re-derivation.
  flags(state, mtype) {
    return renderDoc(state, textRGA).map((e) => [e.char, e.marks.some((m) => m.mtype === mtype)]);
  },

  // The covered live ids of one mark (debug / test helper).
  coveredIds(state, mark) { return coveredIds(mark, buildCtx(state, textRGA)); },

  // Serialization (snapshot bytes / any inline-state wire commit). Lossless
  // round-trip; no compaction commits are emitted so decodeState is only a
  // snapshot path, but providing both keeps the datatype whole.
  encodeState(state) {
    if (typeof state.text.shadow.entries !== 'function') {
      return {
        text: { kernel: textRGA.encodeState(state.text.shadow), deleted: [...state.text.deleted] },
        marks: [...state.marks.entries()].map(([, m]) => m),
      };
    }
    return {
      text: {
        shadow: [...state.text.shadow.entries()].map(([id, r]) => [id, r.coord, r.el]),
        deleted: [...state.text.deleted],
      },
      marks: [...state.marks.entries()].map(([, m]) => m),
    };
  },
  decodeState(enc) {
    if ('kernel' in enc.text) {
      return {
        text: { shadow: textRGA.decodeState(enc.text.kernel), deleted: PSet.from(enc.text.deleted) },
        marks: PMap.from(enc.marks.map((m) => [m.mid, Object.freeze(m)])),
      };
    }
    return {
      text: {
        shadow: PMap.from(enc.text.shadow.map(([id, coord, el]) => [id, Object.freeze({ coord, el })])),
        deleted: PSet.from(enc.text.deleted),
      },
      marks: PMap.from(enc.marks.map((m) => [m.mid, Object.freeze(m)])),
    };
  },

  // Canonical serialization (twin-comparison / content-address helper).
  fingerprint(state) {
    const shadow = typeof state.text.shadow.entries === 'function'
      ? [...state.text.shadow.entries()].sort(([x], [y]) => (x < y ? -1 : 1))
        .map(([id, r]) => [id, r.coord, r.el])
      : textRGA.fingerprint(state.text.shadow);
    return JSON.stringify({
      shadow,
      deleted: [...state.text.deleted].sort((x, y) => x - y),
      marks: [...state.marks.entries()].sort(([x], [y]) => x - y)
        .map(([, m]) => [m.mid, m.mtype, m.value, m.startId, m.endId, m.startSide, m.endSide, m.ts, m.removed]),
    });
  },

  // NO compact / remapState HERE: on this plain object compactStable refuses
  // (the orset path). The marks-layer GC lives in ../compact-peritext.js
  // (`compactiblePeritext`): the keep-set retains live ids UNION mark
  // boundary anchors UNION declared in-flight anchors, so pruning never
  // destroys a birth position the resolver needs (buildCtx.birth), the
  // retention-roots design. Blind pruning WOULD flip reads; that negative
  // control is kept executable as opts.noRetention in compact-peritext.js.
};
}

/** Peritext over the one-sided tombstone-free EmbedRGA kernel. */
export const peritextEmbedRGA = makePeritext(embedRGA);

/** Peritext over the unified sided/Fugue EmbedRGA kernel. */
export const peritextSidedEmbedRGA = makePeritext(sidedEmbedRGAReleaseCandidate);

/** Production default. */
export const peritext = peritextSidedEmbedRGA;
