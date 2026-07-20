// PERITEXT: the verified DOCUMENT-ORDER rich-text mark model as a runtime
// datatype (task #55 -> #107). This is the bridge from the Lean-verified read
// model to the editor: it plugs into DistributedReplica over the SAME
// {init, apply, merge3, read} contract as embedRGA and orset, so rich text gets
// delta gossip + content addressing + commit GC "for free" -- no Peritext-
// specific runtime code (the parametricity payoff, test/peritext.test.js).
//
// PORTED FROM (read-side matched precisely):
//   * whiteboard/litmus/peritext_read_model.py -- DocumentOrderResolver, the
//     Ex1-8 renders, gravity, leak, trilemma (the executable reference).
//   * Sal/ConditionedMRDTs/MRDT_Instances/Peritext_Embed/PeritextEmbed_MarkIntent.lean
//     -- DocD (shadow + deleted), startIncl/endExcl, renderMarksDoc,
//     doc_no_backward_leak, doc_delete_can_respan (the verified spec).
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
// exactly that. So this is DocD from the verified spec: births are kept, a
// separate deleted set marks the survivors. live = birth order minus deleted
// (the embed capstone's P3, the same identity embedRGA.merge preserves). This
// is ALSO why state compaction is (correctly) refused: pruning a dead anchor's
// coordinate would break mark rehoming (see the note at the bottom).

import { embedRGA } from './embedRGA.js';

// ---------------------------------------------------------------- resolver ctx
// One pass over the shadow builds everything the resolver reads.
function buildCtx(state) {
  const entries = embedRGA.readEntries(state.text.shadow); // reading order
  const birth = entries.map(([id]) => id);                 // all ids, in order
  const cp = new Map(entries.map(([id, r]) => [id, r.el])); // id -> codepoint
  const deleted = state.text.deleted;
  const live = birth.filter((c) => !deleted.has(c));       // survivors, in order
  const pos = new Map(live.map((c, i) => [c, i]));          // live id -> live idx
  const bpos = new Map(birth.map((c, i) => [c, i]));        // birth id -> birth idx
  return { birth, live, cp, deleted, pos, bpos, shadow: state.text.shadow };
}

const isLive = (ctx, a) => ctx.shadow.has(a) && !ctx.deleted.has(a);

// Nearest live id strictly one `step` away from birth index `i` (or null).
function scan(birth, deleted, i, step) {
  let j = i + step;
  while (j >= 0 && j < birth.length) {
    if (!deleted.has(birth[j])) return birth[j];
    j += step;
  }
  return null;
}

// First covered live index (null = the span collapsed). Mirrors Python
// DocumentOrderResolver._start_index. Growth compares char id > mark.ts
// ("newer than the mark"), the RGA opId tiebreak (ts defaults to mid).
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

// Last covered live index INCLUSIVE (null = collapse). Mirrors Python
// DocumentOrderResolver._end_index. endSide=after GROWS right; before does not.
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
// mark is one whose winner is not a removeMark. Mirrors Python render().
function renderDoc(state) {
  const ctx = buildCtx(state);
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

export const peritext = {
  init() {
    return { text: { shadow: embedRGA.init(), deleted: new Set() }, marks: new Map() };
  },

  apply(state, op) {
    if (op.type === 'ins') {
      const shadow = embedRGA.apply(state.text.shadow,
        { type: 'ins', id: op.id, el: op.el, anchorId: op.anchorId });
      return { text: { shadow, deleted: state.text.deleted }, marks: state.marks };
    }
    if (op.type === 'del') {
      const deleted = new Set(state.text.deleted);
      deleted.add(op.id);                      // logical delete (birth kept in shadow)
      return { text: { shadow: state.text.shadow, deleted }, marks: state.marks };
    }
    if (op.type === 'addMark' || op.type === 'removeMark') {
      const marks = new Map(state.marks);
      marks.set(op.mid, frozenMark(op));       // mid is globally unique (add-only map)
      return { text: state.text, marks };
    }
    throw new Error(`unknown peritext op type: ${op.type}`);
  },

  // Text: births by embedRGA.merge3 (union of insert-only shadows); deletes by
  // union (grow-only, delete-wins); marks by union on mid (grow-only G-map).
  merge3(l, a, b) {
    const shadow = embedRGA.merge3(l.text.shadow, a.text.shadow, b.text.shadow);
    const deleted = new Set([...l.text.deleted, ...a.text.deleted, ...b.text.deleted]);
    const marks = new Map();
    for (const src of [l.marks, a.marks, b.marks]) for (const [mid, m] of src) marks.set(mid, m);
    return { text: { shadow, deleted }, marks };
  },

  // The DOCUMENT-ORDER rich-text read: [{ id, char, marks:[{mtype,value}] }].
  read(state) { return renderDoc(state); },

  // Flag projection [(char, isMtype)] -- the paper's rendered view (Python
  // render_flags). A pure projection of read(), not a re-derivation.
  flags(state, mtype) {
    return renderDoc(state).map((e) => [e.char, e.marks.some((m) => m.mtype === mtype)]);
  },

  // The covered live ids of one mark (debug / test helper).
  coveredIds(state, mark) { return coveredIds(mark, buildCtx(state)); },

  // Serialization (snapshot bytes / any inline-state wire commit). Lossless
  // round-trip; no compaction commits are emitted so decodeState is only a
  // snapshot path, but providing both keeps the datatype whole.
  encodeState(state) {
    return {
      text: {
        shadow: [...state.text.shadow.entries()].map(([id, r]) => [id, r.coord, r.el]),
        deleted: [...state.text.deleted],
      },
      marks: [...state.marks.entries()].map(([, m]) => m),
    };
  },
  decodeState(enc) {
    return {
      text: {
        shadow: new Map(enc.text.shadow.map(([id, coord, el]) => [id, Object.freeze({ coord, el })])),
        deleted: new Set(enc.text.deleted),
      },
      marks: new Map(enc.marks.map((m) => [m.mid, Object.freeze(m)])),
    };
  },

  // Canonical serialization (twin-comparison / content-address helper).
  fingerprint(state) {
    return JSON.stringify({
      shadow: [...state.text.shadow.entries()].sort(([x], [y]) => (x < y ? -1 : 1))
        .map(([id, r]) => [id, r.coord, r.el]),
      deleted: [...state.text.deleted].sort((x, y) => x - y),
      marks: [...state.marks.entries()].sort(([x], [y]) => x - y)
        .map(([, m]) => [m.mid, m.mtype, m.value, m.startId, m.endId, m.startSide, m.endSide, m.ts, m.removed]),
    });
  },

  // NO compact / remapState: state compaction is deliberately NOT supported.
  // Pruning a dead anchor's coordinate would destroy the birth position a mark
  // needs to rehome (buildCtx.birth), so compactStable MUST refuse for this
  // datatype (it returns { compacted:false, reason:'does not support...' }, the
  // orset path). The text still gets the run-table SERIALIZER cost via
  // encodeState; epoch compaction is the wrong tool here by construction.
};
