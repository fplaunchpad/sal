// MARKS-LAYER STATE GC for Peritext (task #110 phase 2): the VALIDATED
// retention-roots compaction (attack H-A) plus the A3 guarded pair-drop,
// transliterated from the Python reference semantics
// whiteboard/litmus/marks_gc_check.py (build_cut / a3_pairs /
// apply_compaction; design + verdicts in whiteboard/marks-gc-note.md
// sections 3-7: H-A VALIDATED 2000/2000 PBT trials, A3 VALIDATED 600/600
// with 44 drops fired, NONE = the old refusal's justification, 351/600
// trials flipped).
//
// THE KEEP-SET (note section 3, H-A). Peritext keeps text deletes LOGICAL
// (shadow of every birth + a grow-only deleted set) because the mark
// resolver rehomes a DEAD boundary anchor to its nearest surviving
// neighbour in reading order, which needs the dead anchor's birth position;
// that is why compactStable used to refuse for peritext (pruning a dead
// anchor's record flips reads -- note D6, the NONE negative control, kept
// here as opts.noRetention). The sound compaction keeps
//
//   keep = live ids  UNION  boundary anchor ids of every present mark
//          (add and remove records both)  UNION  declared in-flight anchors
//
// and drops every settled-dead record outside it, exactly as the plain
// embed-RGA compaction drops dead ranges. Retained dead anchors survive as
// dead records with RE-CODED coordinates and stay listed in `deleted`;
// marks reference IDS, which re-coding never rewrites, so the marks map
// itself needs no rewriting. The re-coding, the order-preserving
// rank-renumbering, and the in-flight skipped-group guard are compact.js's
// compactEliasDelta, reused verbatim over the kept shadow (a declared
// in-flight insert freezes its anchor's child group via
// cut.frozenAnchorCoords -- the harness's frozen_parents, exact in every
// epoch).
//
// A3 GUARDED PAIR-DROP (note section 5.5 / O4): an (add m, remove r) pair
// with equal boundary tuples (ids AND sides), same mtype, r.mid > m.mid
// resolves identically forever, and r beats m wherever both apply, so the
// pair is render-neutral and droppable -- freeing its retention roots --
// ONLY under three guards (each with a machine-checked countermodel):
//   (i)   the removal is settled at the cut (alpha corner: an in-flight
//         same-mtype add between the mids is resurrected by the drop);
//         declared in-flight marks of the mtype predating r also refuse;
//   (ii)  no OTHER same-mtype mark with mid < r.mid exists (LWW shadowing:
//         spans move under edits, so a no-overlap check now does not
//         persist);
//   (iii) no char id lies strictly inside the growth window (m.mid, r.mid)
//         among present-or-declared ids (beta corner, a phase-1 FINDING:
//         such a char is grabbed by the add's end-growth but not the
//         remove's). Future mints are Lamport-fresh (> r.mid), so the
//         check at the cut is sufficient.
//
// THE SETTLED-CUT CONTRACT is compact.js's, with one peritext refinement:
// because deletes are logical, a record may be dropped only when its DELETE
// is settled too (cut.settledDelIds), not merely its insert -- an id whose
// delete is still propagating is live somewhere and may yet be marked or
// anchored on. Under DistributedReplica's certified cut both sets (and the
// settled mark mids guard (i) needs) are extracted from the meet by
// peritextCutFromMeet, and every in-flight field is EMPTY, discharged by
// the certificate exactly as for the text layer.
//
// cut = {
//   settledIds:      Set of char ids whose INSERT is settled,
//   settledDelIds:   Set of char ids whose DELETE is settled,
//   settledMarkMids: Set of mids of settled addMark/removeMark ops,
//   inflightIns:     [{ id, anchorId }] declared in-flight inserts
//                    (anchorId null = root),
//   inflightMarks:   [{ mid, mtype, startId, endId, ... }] declared
//                    in-flight marks,
// }
// opts = { pairDrop: false            -- disable A3 (plain H-A),
//          unguardedPairDrop: true    -- NEGATIVE CONTROL ONLY (D7 flips),
//          noRetention: true          -- NEGATIVE CONTROL ONLY (D6/NONE),
//          ...rest passed to compactEliasDelta (unguardedRenumber etc.) }
//
// Returns { state, translate, stats }: stats extends compactEliasDelta's
// with { recordsBefore, recordsAfter, recordsDropped, settledDead,
// retainedForMarks, markRecords, markPairsDropped }. Cost claim (note
// section 7, measured): retainedForMarks <= 2 * markRecords, structural
// (a mark has two boundaries).

import { peritext } from './datatypes/peritext.js';
import { embedRGA } from './datatypes/embedRGA.js';
import { compactEliasDelta, remapState } from './compact.js';
import { encode as encodeRunTable, decode as decodeRunTable, buildRunTable } from './serialize.js';
import { PMap, PSet, isPMap, eachEntry } from './pmap.js';

// ---- the v2 SNAPSHOT ENCODING: run-table shadow + id sidecar ---------------
// encodeState v1 (the plain datatype's) writes every record's ABSOLUTE
// coordinate as a '0'/'1' string: one byte per bit, the whole ancestor chain
// repeated per record -- Theta(depth^2) JSON for a typing run. v2 sends the
// shadow through the SHIPPED run-table serializer (task #104) instead, plus
// an ID SIDECAR: record ids in the serializer's deterministic element order
// (entries in table order, members in order), zigzag-varint gap-coded. The
// sidecar is required because ids are NOT recoverable as delta sums after a
// compaction epoch (rank renumbering forgets time -- the RunTable.lean
// correction), and the marks/deleted layers anchor on real ids. The
// fingerprint is untouched, so compact-commit content ids do not move; only
// the stored/wire snapshot bytes change.

const b64encode = (u8) => {
  let s = '';
  for (let i = 0; i < u8.length; i += 0x8000) s += String.fromCharCode(...u8.subarray(i, i + 0x8000));
  return btoa(s);
};
const b64decode = (str) => Uint8Array.from(atob(str), (ch) => ch.charCodeAt(0));

const zig = (n) => (n < 0 ? -2 * n - 1 : 2 * n);
const unzig = (z) => (z % 2 ? -(z + 1) / 2 : z / 2);
const writeVar = (arr, n) => { while (n >= 128) { arr.push((n & 127) | 128); n = Math.floor(n / 128); } arr.push(n); };

/** Ids in the serializer's element order, gap-coded. */
function idSidecar(shadow) {
  const bytes = [];
  let prev = 0;
  for (const e of buildRunTable(shadow).entries) {
    if (!e.live) continue;
    for (const m of e.members) { writeVar(bytes, zig(m.rid - prev)); prev = m.rid; }
  }
  return b64encode(Uint8Array.from(bytes));
}

/** Rebuild the true-id shadow from decode()'s fresh-sequential-id state (its
 *  keys 1..n are assigned in exactly the element order the sidecar uses; PMap
 *  iterates key-sorted, so the orders align). */
function rekeyShadow(decoded, sidecarB64) {
  const u8 = b64decode(sidecarB64);
  const ids = [];
  let i = 0, prev = 0;
  while (i < u8.length) {
    let n = 0, s = 0, b;
    do { b = u8[i++]; n += (b & 127) * 2 ** s; s += 7; } while (b & 128);
    prev += unzig(n); ids.push(prev);
  }
  const out = PMap.empty().begin();
  let k = 0;
  for (const [, rec] of decoded.entries()) out.set(ids[k++], rec);
  if (k !== ids.length) throw new Error(`id sidecar mismatch: ${ids.length} ids for ${k} records`);
  return out.freeze();
}

// Members of a PSet (hash order) or a legacy plain Set (insertion order).
const eachMember = (s, fn) => {
  if (s instanceof PSet) s.forEachRaw(fn);
  else for (const x of s) fn(x);
};

const anchorsOf = (m) => [m.startId, m.endId].filter((a) => Number.isInteger(a));

/** A3 pair enumeration (marks_gc_check.py a3_pairs, transliterated). A pair
 *  is (add m, remove r): same mtype, same boundary ids AND sides,
 *  r.mid > m.mid. With `unguarded` (negative control) every syntactic pair
 *  is returned; otherwise the three guards above all apply. */
export function a3Pairs(marks, shadow, inflightIns, inflightMarks,
  settledMarkMids, unguarded = false) {
  const pairs = [];
  for (const r of marks) {
    if (!r.removed) continue;
    for (const m of marks) {
      if (m.removed || m.mtype !== r.mtype || m.mid >= r.mid
          || m.startId !== r.startId || m.endId !== r.endId
          || m.startSide !== r.startSide || m.endSide !== r.endSide) continue;
      if (!unguarded) {
        if (!settledMarkMids.has(r.mid)) continue;                 // (i) removal settled
        if (marks.some((o) => o.mtype === r.mtype && o.mid < r.mid
                              && o.mid !== m.mid)) continue;       // (ii) LWW shadowing
        if (inflightMarks.some((o) => o.mtype === r.mtype
                                      && o.mid < r.mid)) continue; // (i) in-flight mark
        let windowHit = false;                                     // (iii) growth window
        eachEntry(shadow, (id) => { if (m.mid < id && id < r.mid) windowHit = true; });
        if (windowHit) continue;
        if (inflightIns.some((x) => m.mid < x.id && x.id < r.mid)) continue;
      }
      pairs.push([m, r]);
    }
  }
  return pairs;
}

export function compactPeritext(state, cut, opts = {}) {
  const settledIds = cut?.settledIds ?? new Set();
  const settledDelIds = cut?.settledDelIds ?? new Set();
  const settledMarkMids = cut?.settledMarkMids ?? new Set();
  const inflightIns = cut?.inflightIns ?? [];
  const inflightMarks = cut?.inflightMarks ?? [];
  const noRetention = opts.noRetention === true;             // NEGATIVE CONTROL (D6/NONE)
  const unguardedPairDrop = opts.unguardedPairDrop === true; // NEGATIVE CONTROL (D7)
  const pairDrop = opts.pairDrop !== false && !noRetention;  // A3, on by default

  const shadow = state.text.shadow;
  const deleted = state.text.deleted;
  const allMarks = [...state.marks.values()];

  // --- A3 guarded pair-drop FIRST: freed roots then leave the keep-set.
  let marksOut = isPMap(state.marks) ? state.marks : PMap.from(state.marks);
  let markPairsDropped = 0;
  if (pairDrop) {
    const pairs = a3Pairs(allMarks, shadow, inflightIns, inflightMarks,
      settledMarkMids, unguardedPairDrop);
    if (pairs.length > 0) {
      const t = marksOut.begin();
      for (const [m, r] of pairs) {
        if (t.has(m.mid) && t.has(r.mid)) {
          t.delete(m.mid);
          t.delete(r.mid);
          markPairsDropped++;
        }
      }
      marksOut = t.freeze();
    }
  }

  // --- the keep-set (note section 3, H-A): live UNION mark boundary
  // anchors (surviving records AND declared in-flight marks) UNION declared
  // in-flight insert anchors. Under noRetention (the NONE control) only the
  // declared anchors are kept, which is the harness's NONE keep-set.
  const inflAnchor = new Set();
  for (const { anchorId } of inflightIns) {
    if (anchorId !== null && anchorId !== undefined) inflAnchor.add(anchorId);
  }
  for (const m of inflightMarks) for (const a of anchorsOf(m)) inflAnchor.add(a);
  const markAnchors = new Set();
  if (!noRetention) {
    marksOut.forEach((m) => { for (const a of anchorsOf(m)) markAnchors.add(a); });
    for (const m of inflightMarks) for (const a of anchorsOf(m)) markAnchors.add(a);
  }

  // --- drop rule (harness apply_compaction): a record vanishes iff its
  // insert AND its delete are settled at the cut and no retention root
  // claims it. Live and unsettled records are always kept.
  const keepShadow = new Map();
  let symbolsBeforeFull = 0, recordsBefore = 0, recordsDropped = 0;
  let settledDead = 0, retainedForMarks = 0;
  eachEntry(shadow, (id, rec) => {
    recordsBefore++;
    symbolsBeforeFull += rec.coord.length;
    if (deleted.has(id) && settledDelIds.has(id) && settledIds.has(id)) {
      settledDead++;
      if (!markAnchors.has(id) && !inflAnchor.has(id)) { recordsDropped++; return; }
      if (markAnchors.has(id) && !inflAnchor.has(id)) retainedForMarks++;
    }
    keepShadow.set(id, rec);
  });

  // --- declared in-flight inserts freeze their anchor's child group by the
  // anchor's CURRENT-epoch coordinate (harness frozen_parents; '' = root).
  const frozenAnchorCoords = [];
  for (const { id, anchorId } of inflightIns) {
    if (anchorId === null || anchorId === undefined) { frozenAnchorCoords.push(''); continue; }
    const a = keepShadow.get(anchorId);
    if (!a) {
      throw new Error(
        `declared in-flight insert ${id}: anchor ${anchorId} has no kept record`);
    }
    frozenAnchorCoords.push(a.coord);
  }

  // --- re-code the kept shadow via the shared text-layer machinery.
  const inner = compactEliasDelta(keepShadow,
    { settledIds, inflight: [], frozenAnchorCoords }, opts);

  // --- rebuild the state: re-coded shadow; `deleted` restricted to kept
  // records (retained dead anchors STAY listed); marks untouched by
  // re-coding (they reference ids, never coordinates).
  const dt = PSet.empty().begin();
  eachMember(deleted, (x) => { if (inner.state.has(x)) dt.add(x); });
  const out = {
    text: { shadow: inner.state, deleted: dt.freeze() },
    marks: marksOut,
  };
  const stats = {
    ...inner.stats,
    symbolsBefore: symbolsBeforeFull,
    recordsBefore,
    recordsAfter: recordsBefore - recordsDropped,
    recordsDropped,
    settledDead,
    retainedForMarks,
    markRecords: marksOut.size,
    markPairsDropped,
  };
  return { state: out, translate: inner.translate, stats };
}

/** Record-wise coordinate translation (the epoch-lifting hook): shadow
 *  coordinates re-mapped, deleted set and marks carried unchanged (ids are
 *  never rewritten). */
export function remapPeritextState(state, translate) {
  return {
    text: { shadow: remapState(state.text.shadow, translate), deleted: state.text.deleted },
    marks: state.marks,
  };
}

/** The peritext cut from a CERTIFIED meet (src/frontier.js stableCut): the
 *  settled insert ids, the settled delete ids (drop eligibility -- a
 *  logical delete still propagating must not free its record), and the
 *  settled mark mids (A3 guard (i)). Every in-flight field is empty,
 *  discharged by the certificate exactly as for the text layer. */
export function peritextCutFromMeet(meet) {
  const settledIds = new Set(), settledDelIds = new Set(), settledMarkMids = new Set();
  for (const op of meet.values()) {
    // op.payload is a single op, or an op ARRAY for a group-op (batch) commit.
    const ps = Array.isArray(op.payload) ? op.payload : op.payload ? [op.payload] : [];
    for (const p of ps) {
      if (p.type === 'ins') settledIds.add(p.id);
      else if (p.type === 'del') settledDelIds.add(p.id);
      else if (p.type === 'addMark' || p.type === 'removeMark') settledMarkMids.add(p.mid);
    }
  }
  return { settledIds, settledDelIds, settledMarkMids, inflightIns: [], inflightMarks: [] };
}

/** Peritext with the state-GC hooks the runtime looks for: compactStable
 *  now FIRES (with the certificate) instead of refusing -- the marks-layer
 *  GC of task #110. encodeState/decodeState come from the datatype itself
 *  (they already carry compaction commits losslessly). */
export const compactiblePeritext = {
  ...peritext,
  compact: compactPeritext,
  remapState: remapPeritextState,
  cutFromMeet: peritextCutFromMeet,
  // v2 snapshot: run-table shadow + id sidecar (above); decode accepts the
  // plain datatype's legacy v1 shape too (previously persisted records)
  encodeState(state) {
    return {
      v: 2,
      rt: b64encode(encodeRunTable(state.text.shadow)),
      ids: idSidecar(state.text.shadow),
      deleted: [...state.text.deleted].sort((x, y) => x - y),
      marks: [...state.marks.entries()].sort(([x], [y]) => x - y).map(([, m]) => m),
    };
  },
  decodeState(enc) {
    if (!enc || enc.v !== 2) return peritext.decodeState(enc); // legacy v1
    return {
      text: {
        shadow: rekeyShadow(decodeRunTable(b64decode(enc.rt)), enc.ids),
        deleted: PSet.from(enc.deleted),
      },
      marks: PMap.from(enc.marks.map((m) => [m.mid, Object.freeze({ ...m })])),
    };
  },
  // the coordinate-cost probe compaction shrinks: the text shadow IS an
  // embedRGA state, so its symbol count is the peritext coordinate cost
  symbolCount: (state) => embedRGA.symbolCount(state.text.shadow),
  // what a SAVE costs (task #104's run-table serializer, the representation
  // lever of the design doc's storage layer): the shadow's run-table bytes
  // plus a compact JSON of the deleted set and mark records. This is the
  // honest durable-cost number; the in-memory coordinate JSON (encodeState)
  // is orders of magnitude above it on chain-heavy docs.
  saveBytes(state) {
    const shadow = encodeRunTable(state.text.shadow).length;
    const aux = JSON.stringify([
      [...state.text.deleted].sort((x, y) => x - y),
      [...state.marks.entries()].sort(([x], [y]) => x - y)
        .map(([, m]) => [m.mid, m.mtype, m.value, m.startId, m.endId, m.startSide, m.endSide, m.ts, m.removed]),
    ]);
    return shadow + new TextEncoder().encode(aux).length;
  },
};
