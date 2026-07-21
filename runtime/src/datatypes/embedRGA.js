// Embedded-chain RGA, ported from the Python model
// whiteboard/litmus/embed_tree.py (EmbedTree / EmbedTreeCode / EmbedTreeCodeD).
//
// UNVERIFIED TRANSLITERATION: the Lean-verified artifact is the embed
// kernel; this port is pinned to the model's semantics by fixtures
// extracted by RUNNING the Python model (see test/embed.test.js) and, for
// the delta code, by the kernel-checked example values in
// Sal/MRDTs/RGA_Embed/Embed_Code_EliasDelta.lean (see test/code.test.js).
//
// Representation (a deliberate, equivalence-preserving deviation from the
// Python file, documented in ../../README.md): the model stores
// parent-relative Fraction intervals and refolds on delete (isometric
// fold) and on merge. By the model's own P3 the ABSOLUTE coordinate of a
// record is a birth constant, so we store it directly: every record
// carries its full immutable chain coordinate, a bit-string
//
//   coord(x anchored at a) = coord(a) ++ code.enc(ts(x) - ts(a))
//   (root anchor: coord = code.enc(ts))
//
// under a pluggable ORDER-PRESERVING PREFIX-FREE DELTA CODE. Then:
//   - delete   = pure record removal (the fold becomes a no-op on absolutes);
//   - merge    = live-set rule on record ids, coordinates carried UNCHANGED;
//   - display  = descending lexicographic coordinate order with an anchor
//     sorting ABOVE its descendants: realized by comparing coord ++ '2'
//     ('2' > '1' > '0'), so a prefix (the anchor) wins over its extensions
//     and siblings/cousins are decided at the first differing bit.
//     Newest (larger delta) sits highest, the RGA convention.
//
// CODE-PARAMETRICITY: the comparator only needs the code to be monotone
// (d < e => enc d <lex enc e) and prefix-free (so unequal codewords are
// decided at a real first difference, never by one running out). Every
// read is therefore identical under any such code -- the Lean theorems
// are parametric in the OrderedPrefixCode structure; test/code.test.js
// checks the invariance executably. The '2' sentinel is NOT part of any
// codeword: it is the comparator's end-of-coordinate mark, ranking an
// anchor above the extensions that prefix-freeness keeps comparable.
//
// SYMBOL-ALPHABET MAPPING (Lean -> JS): the Lean codewords are List Bool
// with bitLt = lexicographic on Bool (false < true). Here a codeword is a
// string over {'0','1'} with false -> '0', true -> '1', MSB first; string
// order on {'0','1'} coincides with bitLt, and '2' sits above both.
//
// Dead-ancestor prefixes are the point: a record's coordinate keeps its
// dead anchor's coordinate as a prefix forever (P4, "the credential
// persists"), which is what the sibling-splice fooling-pair worlds pin.
//
// Ops:  { type: 'ins', id, el, anchorId }   anchorId null = root anchor
//       { type: 'del', id }
// ids are integer timestamps: globally unique, and id > anchorId (you
// insert after something you have seen: Lamport-style minting).
//
// PRECONDITION (honesty / applicability): 'ins' requires the anchor to be
// LIVE in the state the op is applied to. The Python model silently
// malfunctions on a dead anchor (the record becomes unreachable, merge
// KeyErrors); its PBT harness only ever anchors on the current read. The
// port makes the precondition explicit and throws.

import { PMap, isPMap, eachEntry } from '../pmap.js';

/** Unary code: enc(d) = '1'^d '0'. Kept for readability in examples and
 *  for the code-invariance tests; its cost is LINEAR in the delta, and
 *  cross-replica Lamport deltas grow with the GLOBAL op count, so it is
 *  not the design's measured point (see the cost-gap test). */
export const unaryCode = {
  name: 'unary',
  enc: (d) => '1'.repeat(d) + '0',
};

// --- The flipped Elias-delta code, transliterated from the Lean instance
// --- `eliasDeltaCode` in Sal/MRDTs/RGA_Embed/Embed_Code_EliasDelta.lean
// --- (header `binEnc` from Embed_Code_Binary.lean). For d >= 1,
// --- d.toString(2) is d's bits MSB-first, so
// ---   Nat.size d         = b.length     (bit-length)
// ---   bitsW (size-1) d   = b.slice(1)   (low size-1 bits MSB first
// ---                                      = d minus its always-1 leading bit)

/** Lean `binEnc d = replicate (size d - 1) true ++ false :: bitsW (size d - 1) d`:
 *  the flipped-gamma header, |binEnc d| = 2*size d - 1. */
export const binEnc = (d) => {
  const b = d.toString(2);
  return '1'.repeat(b.length - 1) + '0' + b.slice(1);
};

/** Lean `dEnc d = binEnc d.size ++ bitsW (d.size - 1) d`: binEnc on the
 *  bit-length, then the payload. |dEnc d| = size d + 2*size(size d) - 2
 *  = log2 d + O(log log d). */
export const dEnc = (d) => {
  const b = d.toString(2);
  return binEnc(b.length) + b.slice(1);
};

/** The DEFAULT code: the flipped Elias-delta, matching the verified Lean
 *  instance exactly (its kernel-checked values are pinned in test/code.test.js). */
export const eliasDeltaCode = {
  name: 'eliasDelta',
  enc: dEnc,
};

// Display key: descending lex with prefix-above-extension via the '2' sentinel.
const key = (coord) => coord + '2';

/** Build the embed RGA datatype over a delta code { name, enc }. */
export function makeEmbedRGA(code = eliasDeltaCode) {
  const enc = (d) => {
    if (!Number.isInteger(d) || d < 1) {
      throw new Error(`delta must be a positive integer (id > anchorId), got ${d}`);
    }
    return code.enc(d);
  };

  // The record an insert op mints in `state` (validation included). Pure:
  // reads the state through get/has only, so it serves the persistent
  // apply, the transient applyBatch, and legacy plain-Map states alike.
  const insRecord = (state, op) => {
    const { id, el, anchorId } = op;
    if (state.has(id)) throw new Error(`duplicate insert id ${id}`);
    let coord;
    if (anchorId === null || anchorId === undefined) {
      coord = enc(id); // root anchor sits at ts 0
    } else {
      const a = state.get(anchorId);
      if (!a) {
        throw new Error(
          `anchor ${anchorId} not live: honest inserts anchor on the ` +
          `current read (the applicability precondition)`
        );
      }
      coord = a.coord + enc(id - anchorId);
    }
    return Object.freeze({ coord, el });
  };

  return {
    code,

    /** state: PMap id -> { coord, el } (persistent: apply/merge3 return new
     *  maps with structural sharing -- O(log n) per op, no live-set copy).
     *  Legacy plain-Map states (tests, tools) are still accepted read-only
     *  and copied on write. */
    init() { return PMap.empty(); },

    apply(state, op) {
      const p = isPMap(state);
      if (op.type === 'ins') {
        const rec = insRecord(state, op);
        return p ? state.set(op.id, rec) : new Map(state).set(op.id, rec);
      }
      if (op.type === 'del') {
        // pure removal; absent id is a no-op (model: `if d in s`)
        if (p) return state.delete(op.id);
        const s = new Map(state);
        s.delete(op.id);
        return s;
      }
      throw new Error(`unknown embedRGA op type: ${op.type}`);
    },

    /** Batch apply in ONE transient pass (op-for-op identical to folding
     *  apply, frozen at the end): for burst ingestion outside the DAG's
     *  one-op-per-commit granularity. */
    applyBatch(state, ops) {
      const t = (isPMap(state) ? state : PMap.from(state)).begin();
      for (const op of ops) {
        if (op.type === 'ins') t.set(op.id, insRecord(t, op));
        else if (op.type === 'del') t.delete(op.id);
        else throw new Error(`unknown embedRGA op type: ${op.type}`);
      }
      return t.freeze();
    },

    /** Elements in display order: descending lexicographic coordinate keys. */
    read(state) {
      return this.readEntries(state).map(([, r]) => r.el);
    },

    /** [id, record] pairs in display order (test/debug helper). */
    readEntries(state) {
      return [...state.entries()].sort(([ia, a], [ib, b]) => {
        const ka = key(a.coord), kb = key(b.coord);
        if (ka !== kb) return ka > kb ? -1 : 1; // descending
        return ia < ib ? -1 : 1;                // unreachable: coords are injective
      });
    },

    readIds(state) { return this.readEntries(state).map(([id]) => id); },

    /** Ternary merge: live ids = (A ∩ B) ∪ (A ∖ L) ∪ (B ∖ L); records
     *  (coordinates) carried unchanged: they are birth constants. On PMap
     *  states this is a DELTA MERGE from A -- equivalently
     *  A ∖ (L ∖ B) ∪ (B ∖ L) -- touching only the ids B deleted or added,
     *  with structural sharing of A's untouched trie; a∩b coordinate
     *  agreement is checked exactly as before. Hash-order scans are safe:
     *  the output is a content-canonical set, insertion order unobservable. */
    merge3(l, a, b) {
      const chk = (id, ra, rb) => {
        if (ra.coord !== rb.coord) {
          throw new Error(`coordinate divergence at id ${id}: birth constants must agree`);
        }
      };
      if (isPMap(a)) {
        const t = a.begin();
        eachEntry(l, (id) => { if (!b.has(id)) t.delete(id); }); // dropped by B (or never in A: no-op)
        eachEntry(b, (id, rb) => {
          const ra = a.get(id);
          if (ra !== undefined) chk(id, ra, rb);                 // a∩b: birth-constant gate
          else if (!l.has(id)) t.set(id, rb);                    // B's fresh mints
        });
        return t.freeze();
      }
      // legacy plain-Map inputs: rebuild into one transient
      const t = PMap.empty().begin();
      eachEntry(a, (id, ra) => {
        const rb = b.get(id);
        if (rb !== undefined) { chk(id, ra, rb); t.set(id, ra); }
        else if (!l.has(id)) t.set(id, ra);
      });
      eachEntry(b, (id, rb) => { if (!l.has(id) && !t.has(id)) t.set(id, rb); });
      return t.freeze();
    },

    /** Total coordinate symbol count over the live records (cost probe). */
    symbolCount(state) {
      let n = 0;
      eachEntry(state, (_id, r) => { n += r.coord.length; });
      return n;
    },

    /** Canonical serialization (twin-comparison helper for tests). */
    fingerprint(state) {
      return JSON.stringify(
        [...state.entries()]
          .sort(([x], [y]) => (x < y ? -1 : 1))
          .map(([id, r]) => [id, r.coord, r.el])
      );
    },
  };
}

/** The default instance: flipped Elias-delta, the verified design's code. */
export const embedRGA = makeEmbedRGA(eliasDeltaCode);
