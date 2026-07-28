// THE CUT-INDEXED EPOCH DAG. Epoch identity is the SETTLED CUT plus its
// certificate (the coordinate-addressed cut = the settled insert ids, the
// declared set, the heard frontiers), NOT a per-replica integer. The epochs
// form a CUT-INDEXED DAG whose nodes are cuts and whose edges are compaction
// refinements (one parent) and JOINS (two parents, W = U ∪ V).
//
// WHY CUT-ADDRESSED. Two replicas that compacted the SAME settled cut compute
// the SAME map from the SAME certificate, so they must land on the SAME epoch
// node. A per-replica integer cannot express that two replicas' "epoch 1" are
// the same epoch, nor that two divergent "epoch 1"s are INCOMPARABLE. The cut
// key is the canonical identity: two epochs are the same iff their settled cuts
// are equal, comparable iff one cut ⊆ the other, incomparable (divergent)
// otherwise.
//
// THE JOIN. Merging heads at incomparable epochs U and V forms W = U ∪ V.
// Because the map at W is a function of W's certificate alone, each side
// computes it deterministically with no round trips; the merged state converges
// bit-identically. The join is recorded as a DAG node with parents [U, V]; the
// merge itself is realized in src/replica.js (op-replay to the common base, the
// id-addressed analogue of coordinate-map translation).

import { decodeOne } from './compact.js';

export const EPOCH0 = ''; // the empty settled cut: the uncompacted epoch

/** Split a flipped-Elias-delta coordinate into its list of encoded codeword
 *  segments (the strings, not the decoded deltas). */
function codewordSegs(coord) {
  const segs = [];
  let i = 0;
  while (i < coord.length) { const [, j] = decodeOne(coord, i); segs.push(coord.slice(i, j)); i = j; }
  return segs;
}

/** Build the INVERSE translate of one compaction step: post-epoch coordinate ->
 *  pre-epoch coordinate, the reverse of compact.js's `translate`. Under the
 *  runtime's default (NO spine fusion -- compactStable never fuses), a surviving
 *  record keeps one coordinate LEVEL per pre-level (dead-with-live-descendant
 *  ancestors persist as chain nodes), so its pre and post coordinates have the
 *  SAME number of codewords and align level-by-level. The inverse is a prefix
 *  map over post codewords carrying the cumulative pre prefix; a later-arriving
 *  straggler (post = survivingAnchorPost ++ tail) factors through its anchor's
 *  post prefix and keeps its tail verbatim. This is what lets a compacted state
 *  be lifted DOWN to the common base frame for a cross-epoch merge WITHOUT
 *  re-applying ops (which would fail on dead anchors). */
export function buildInverseTranslate(preState, postState) {
  const root = { pre: '', children: new Map() };
  for (const [id, rec] of postState) {
    const pre = preState.get(id)?.coord;
    if (pre === undefined) continue; // survivor missing from pre: skip (defensive)
    const preSegs = codewordSegs(pre);
    const post = rec.coord;
    let i = 0, node = root, k = 0;
    while (i < post.length) {
      const [, j] = decodeOne(post, i);
      const seg = post.slice(i, j);
      let ch = node.children.get(seg);
      if (!ch) { ch = { pre: node.pre + (preSegs[k] ?? post.slice(i, j)), children: new Map() }; node.children.set(seg, ch); }
      node = ch; i = j; k++;
    }
  }
  return (coord) => {
    let i = 0, node = root;
    while (i < coord.length) {
      const [, j] = decodeOne(coord, i);
      const ch = node.children.get(coord.slice(i, j));
      if (!ch) break; // left the mapped region: rest verbatim
      node = ch; i = j;
    }
    return node.pre + coord.slice(i);
  };
}

/** Canonical cut key: the settled insert ids, sorted ascending, comma-joined.
 *  Equal cuts ⟹ equal keys ⟹ the same epoch node. */
export function cutKey(settledIds) {
  return [...settledIds].map(Number).sort((x, y) => x - y).join(',');
}

/** Serialize a compaction cut for the wire (its Set fields become sorted
 *  arrays; array fields pass through). The receiver RECOMPUTES the epoch's
 *  translate map from parentState + this cut: the certificate travels, the map
 *  does not (each side computes the join map from the shared certificate
 *  data). */
export function serializeCut(cut) {
  const out = {};
  for (const [k, v] of Object.entries(cut ?? {})) {
    out[k] = v instanceof Set ? [...v].sort((a, b) => (a < b ? -1 : a > b ? 1 : 0)) : v;
  }
  return out;
}

/** Inverse of serializeCut: the fields that were Sets on the compacting side
 *  (settledIds, settledDelIds, settledMarkMids) are rebuilt as Sets; the rest
 *  (inflight arrays) pass through. */
export function deserializeCut(cut) {
  const setFields = new Set(['settledIds', 'settledDelIds', 'settledMarkMids']);
  const out = {};
  for (const [k, v] of Object.entries(cut ?? {})) {
    out[k] = setFields.has(k) && Array.isArray(v) ? new Set(v) : v;
  }
  return out;
}

export class EpochDag {
  constructor() {
    // key -> { key, num, settledIds:Set, cut, translate, translateInv, parents:[key], mapDropped }
    this.nodes = new Map();
    this.nodes.set(EPOCH0, {
      key: EPOCH0, num: 0, settledIds: new Set(), cut: null,
      translate: null, translateInv: null, parents: [], mapDropped: false,
    });
  }

  get(key) { return this.nodes.get(key); }
  has(key) { return this.nodes.has(key); }

  /** Register a COMPACTION epoch (one parent). The epoch KEY is the compaction
   *  commit's content id (the FRAME identity): two compactions at the same cut
   *  but with different straggler sets freeze groups differently, so they are
   *  DISTINCT frames with distinct content ids -- keying by cut alone would
   *  conflate them and a merge would assert false coordinate agreement. The cut
   *  is kept as node metadata (for the join W = U ∪ V and cut order). Idempotent
   *  by key; a later registration may fill in maps recomputed on ingest. */
  compaction(key, { settledIds = [], cut = null, translate = null, translateInv = null, parentKey = EPOCH0 } = {}) {
    const existing = this.nodes.get(key);
    if (!existing) {
      const parent = this.nodes.get(parentKey);
      this.nodes.set(key, {
        key, num: (parent ? parent.num : 0) + 1, settledIds: new Set([...settledIds].map(Number)),
        cut, translate, translateInv, parents: [parentKey], mapDropped: false,
      });
    } else {
      if (existing.translate == null && translate != null) existing.translate = translate;
      if (existing.translateInv == null && translateInv != null) existing.translateInv = translateInv;
      if (existing.cut == null && cut != null) existing.cut = cut;
    }
    return key;
  }

  /** Register the JOIN of two epochs: W = U ∪ V, the cut-DAG node with parents
   *  [U, V] (decl(W) = (decl(U) | decl(V)) - W; under a certified cut the
   *  declared sets are empty). Idempotent by cut key. Returns W's key. */
  join(keyU, keyV) {
    const U = this.nodes.get(keyU), V = this.nodes.get(keyV);
    const settled = new Set([...U.settledIds, ...V.settledIds]);
    const key = cutKey(settled);
    if (!this.nodes.has(key)) {
      this.nodes.set(key, {
        key, num: Math.max(U.num, V.num) + 1, settledIds: settled, cut: null,
        translate: null, translateInv: null, parents: [keyU, keyV], mapDropped: false,
      });
    }
    return key;
  }

  /** Cut order: is `subKey`'s cut ⊆ `supKey`'s cut (subKey ≤ supKey)? Equal cuts
   *  are ⊆ each other. Distinct cuts with neither ⊆ the other are INCOMPARABLE
   *  (the divergent case). */
  subcut(subKey, supKey) {
    const sub = this.nodes.get(subKey).settledIds, sup = this.nodes.get(supKey).settledIds;
    if (sub.size > sup.size) return false;
    for (const x of sub) if (!sup.has(x)) return false;
    return true;
  }

  /** Comparability verdict for two epoch keys: 'eq', 'sub' (a ≤ b), 'sup'
   *  (b ≤ a), or 'divergent' (incomparable cuts). */
  compare(a, b) {
    if (a === b) return 'eq';
    const ab = this.subcut(a, b), ba = this.subcut(b, a);
    if (ab && ba) return 'eq';
    if (ab) return 'sub';
    if (ba) return 'sup';
    return 'divergent';
  }

  /** The chain of translate maps that lifts a state coded in `fromKey` UP to
   *  `toKey` along a linear (single-parent) refinement chain, parent-map-first
   *  (ready for left-to-right remapState). Returns null if no such linear chain
   *  exists (a join intervenes, or a map was dropped/absent) -- the caller then
   *  falls back to op-replay. Requires fromKey ⊆ toKey. */
  liftChain(fromKey, toKey) {
    if (fromKey === toKey) return [];
    const maps = [];
    let k = toKey;
    while (k !== fromKey) {
      const n = this.nodes.get(k);
      if (!n || n.parents.length !== 1 || n.translate == null || n.mapDropped) return null;
      maps.push(n.translate);
      k = n.parents[0];
    }
    return maps.reverse();
  }
}

// ------------------------------------------------------------------ map GC
//
// A translation map is GARBAGE-COLLECTED per the DOUBLE certificate: everyone
// advanced past epoch e AND every pre-advance mint has been heard everywhere
// (acks PLUS AllHeardSince over the ack frontier). The ack-ONLY shortcut is
// UNSOUND: an epoch-e straggler minted before its minter advanced can still
// arrive after the acks, is old-space (its coordinate is an epoch-e coordinate
// needing the e-1→e map), and translating it needs the map.

/** Does the DOUBLE certificate justify dropping epoch e's map?
 *  - everyoneAdvanced: every registered replica's evidence sits at an epoch
 *    whose cut ⊋ e's cut (advanced strictly past e);
 *  - allHeardOverAckFrontier: every op minted before its minter's advance is in
 *    every replica's causal past (AllHeardSince over the ack frontier).
 *  BOTH are required. */
export function doubleCertificate({ everyoneAdvanced, allHeardOverAckFrontier }) {
  return everyoneAdvanced === true && allHeardOverAckFrontier === true;
}

/** The UNSOUND ack-only shortcut, kept as a NAMED NEGATIVE CONTROL: it would
 *  drop a map the double certificate retains (and dropping it flips a read).
 *  Never call this to gate a real drop. */
export function ackOnlyCertificate({ everyoneAdvanced }) {
  return everyoneAdvanced === true;
}
