// State-level GC for the embed RGA (task #97, practical tail):
// compactEliasDelta v1, a PURE function  state x cut -> { state', translate }.
//
// The state is the embed RGA's Map id -> { coord, el } with immutable chain
// coordinates under the flipped Elias-delta code (the verified default of
// src/datatypes/embedRGA.js; unary-coded states are NOT supported here).
//
// THE ALGORITHM, over the stable coordinate tree (the tree of decoded chain
// prefixes of the live records, seeded also with the settled prefixes of
// any KNOWN in-flight coordinates):
//
//   (1) DROP dead ranges. A dead subtree below the cut with no live
//       descendant and no known in-flight coordinate through it vanishes
//       entirely: in this representation dead RECORDS are already absent
//       (delete = pure removal), so a dead range simply never enters the
//       tree, and its deltas stop reserving room in step (2). Dead
//       ancestors WITH live descendants stay as chain nodes (their level
//       persists in every descendant's prefix; fusing such spines is
//       iteration two, out of scope here). Dead ranges WITH known
//       in-flight coordinates through them are kept: the in-flight prefix
//       must remain translatable.
//
//   (2) RANK-RENUMBER. Each sibling group whose members are all settled
//       and which has NO known in-flight child gets its deltas replaced by
//       the ordinals 1..k preserving order (deltas are distinct positive
//       integers, so ordinal i <= delta i and coordinates never grow);
//       re-encoded with eliasDeltaCode. A group WITH a known in-flight
//       child is SKIPPED this epoch: an in-flight sibling's delta is
//       frozen inside the op's already-minted coordinate, and dense
//       renumbering against it can FLIP an order (siblings 2 < 5(inflight)
//       < 7 renumber to 1,2 and the frozen 5 jumps the ex-7); the
//       negative-control knob opts.unguardedRenumber demonstrates exactly
//       that flip in test/compact.test.js and must never be set in
//       production. Groups containing an unsettled AT-REST member are
//       likewise never renumbered (its coordinate is a birth constant with
//       copies elsewhere; rewriting it would diverge at merge).
//
//   (2b) SPINE FUSION (iteration two, opt-in via opts.fuseSpines;
//       whiteboard/embed-recoding-note.md Addendum 2). A fusible spine is
//       a maximal chain of DEAD nodes d1..dk, each below the cut (settled,
//       via the same downward-closure evidence as step 2), each with
//       EXACTLY ONE child branch counting every known coordinate INCLUDING
//       the seeded in-flight prefixes, and with no in-flight op anchored
//       at (or landing on) any d_i. The spine collapses to ONE level at
//       the head's group codeword: every coordinate through it rewrites
//         prefix(parent) ++ block(d1) ++ .. ++ block(dk) ++ rest
//           -> prefix(parent) ++ enc(head's ordinal-or-delta) ++ rest,
//       i.e. in the tree all spine nodes share the head's newCoord and
//       dk's single child group continues below it. Order survives by the
//       three-class H2 argument of Addendum 2: (i) inside the block the
//       common prefix is replaced wholesale; (ii) against the head's
//       siblings the comparison is decided at the head's level, whose
//       codeword fusion keeps; (iii) no key ends at a fused-away level
//       (spine nodes are dead: no records), so no anchor-vs-extension
//       comparison is lost. THE GUARD, conservative and explicit: a dead
//       single-child chain node with a known in-flight branch or in-flight
//       anchor is NEVER a spine member (it caps any spine above it and
//       heads none; counted once in stats.spinesSkippedInflight when
//       examined as a head). Fusion with k = 1 is the identity and is
//       neither applied nor counted. Coordinates ending STRICTLY INSIDE a
//       fused spine translate (non-injectively) to the fused block; such
//       coordinates cannot exist at hand under an honest settled cut --
//       spine nodes are settled-dead, so no record, LCA payload, declared
//       in-flight (guarded), or future mint ends there -- they arise only
//       from a violated settledness assertion, the same failure class the
//       drop-finality clause pins.
//
//   (3) LAZY TRANSLATION. The returned translate implements the
//       stable-prefix map  rho-hat(c) = rho(stab c) ++ rest c : it walks
//       c's codewords down the tree, emits the re-mapped prefix, and keeps
//       the first unknown codeword onward VERBATIM. At-rest records are
//       re-coded in state'; any record arriving later in an older epoch's
//       coordinates is translated on ingest (the runtime hook wires this
//       through merges, see src/runtime.js). Post-settlement mints are
//       Lamport-fresh: their delta exceeds every original delta of the
//       group, hence every ordinal, so they sort newest-first past the
//       compacted block with no flip (see the future-mint test).
//
// THE SETTLED-CUT CONTRACT (whiteboard/stability-vc-note.md section 2):
// compaction is sound only when the cut is SETTLED at the compacting
// replica -- causally downward closed, and every event concurrent with a
// cut event that exists anywhere is already delivered here. The runtime
// can discharge this by heard-from-everyone-since-the-cut evidence (an
// absorbed commit from every replica that witnesses the cut), against the
// replica set closed at cut time (the open-membership caveat, as for the
// commit GC). In this v1 the CALLER ASSERTS settledness via cut.settledIds
// and declares any known in-flight coordinates via cut.inflight; computing
// evidence certificates is a follow-on.
//
// cut = {
//   settledIds: Set of insert-event ids (integer timestamps) asserted
//     settled. Listing an id asserts its insert AND any delete of it are
//     settled; consequently every id at or below the intended cut should
//     be listed, deleted ones included -- an absent unlisted id is treated
//     as never-existing, and if such an op is in fact in flight it MUST
//     appear in cut.inflight or compaction is unsound (the negative
//     control pins the failure mode). Node stability is derived from the
//     LIVE record ids plus downward closure (a settled record's whole
//     dead ancestor chain is settled, since cuts are causally downward
//     closed), so it stays correct across epochs even though renumbered
//     coordinates no longer telescope to ids.
//   inflight:   array of coordinate bit-strings known minted but not yet
//     delivered here, given in the CURRENT epoch's code (v1:
//     caller-supplied). Dead ranges they pass through are addressed by
//     telescoped prefix-sum ids, which is exact in the mint code; the
//     in-flight x multi-epoch combination (declaring in-flights whose
//     dead-range path was itself renumbered in an earlier epoch) is
//     approximated in v1 and owned by the evidence-certificate follow-on.
// }
//
// Returns { state', translate, stats } with stats =
//   { symbolsBefore, symbolsAfter, groupsRenumbered,
//     groupsSkippedInflight, groupsSkippedUnstable,
//     spinesFused, levelsRemoved, spinesSkippedInflight }.
// The fusion counters are 0 unless opts.fuseSpines is set. Under fusion,
// the k-1 collapsed singleton groups of a fused spine are not visited, so
// they do not count toward groupsRenumbered; levelsRemoved counts them.

import { embedRGA, eliasDeltaCode } from './datatypes/embedRGA.js';
import { PMap } from './pmap.js';

const enc = eliasDeltaCode.enc;

/** Decode ONE flipped-Elias-delta codeword of coord starting at i0.
 *  Returns [d, nextIndex]. Inverse of dEnc: unary run of c ones + '0'
 *  gives the length field's length, the next c bits complete the length
 *  L (leading 1 implicit), the next L-1 bits complete d (leading 1
 *  implicit). */
export function decodeOne(coord, i0) {
  let i = i0, c = 0;
  while (coord[i] === '1') { c++; i++; }
  if (coord[i] !== '0') {
    throw new Error(`bad eliasDelta codeword at ${i0}: missing header terminator`);
  }
  i++;
  let L = 1;
  for (let k = 0; k < c; k++, i++) {
    if (i >= coord.length) throw new Error(`truncated eliasDelta codeword at ${i0}`);
    L = 2 * L + (coord[i] === '1' ? 1 : 0);
  }
  let d = 1;
  for (let k = 0; k < L - 1; k++, i++) {
    if (i >= coord.length) throw new Error(`truncated eliasDelta codeword at ${i0}`);
    d = 2 * d + (coord[i] === '1' ? 1 : 0);
  }
  return [d, i];
}

/** Decode a whole coordinate into its chain of deltas. */
export function decodeChain(coord) {
  const out = [];
  let i = 0;
  while (i < coord.length) {
    const [d, j] = decodeOne(coord, i);
    out.push(d);
    i = j;
  }
  return out;
}

const mkNode = (id, delta) => ({
  id,                     // telescoped delta sum: = the insert-event id in
                          // the mint code (used only by the in-flight walk)
  delta,                  // current delta from the parent (null at root)
  children: new Map(),    // CURRENT delta -> child node
  recordId: null,         // live record occupying this node, if any
  inflightChild: false,   // a known in-flight coordinate's first frozen
                          // codeword lands in THIS node's child group
  inflightHere: false,    // a known in-flight coordinate ENDS at this node
                          // (contradictory caller input -- an in-flight op
                          // cannot be settled -- guarded conservatively:
                          // never a spine member)
  seedSettled: false,     // settledness witnessed by the in-flight walk
                          // (dead ranges kept for in-flight coordinates)
  evidence: false,        // settled evidence: own record listed, seeded,
                          // or any descendant with evidence (downward
                          // closure of the cut, computed bottom-up)
  stable: false,
  newCoord: '',
});

export function compactEliasDelta(state, cut, opts = {}) {
  const settled = cut?.settledIds ?? new Set();
  const inflight = cut?.inflight ?? [];
  const unguarded = opts.unguardedRenumber === true; // NEGATIVE-CONTROL ONLY
  const fuse = opts.fuseSpines === true;             // iteration two (step 2b)

  const root = mkNode(0, null);
  const childOf = (node, d) => {
    let ch = node.children.get(d);
    if (!ch) { ch = mkNode(node.id + d, d); node.children.set(d, ch); }
    return ch;
  };

  // --- build the coordinate tree from the live records
  const nodeOf = new Map(); // record id -> node
  let symbolsBefore = 0;
  for (const [id, rec] of state) {
    symbolsBefore += rec.coord.length;
    let node = root, i = 0;
    while (i < rec.coord.length) {
      const [d, j] = decodeOne(rec.coord, i);
      node = childOf(node, d);
      i = j;
    }
    node.recordId = id;
    nodeOf.set(id, node);
  }

  // --- seed the SETTLED prefixes of known in-flight coordinates (keeps
  // --- dead ranges they pass through) and mark the group receiving the
  // --- first frozen (unsettled) codeword. Prefix-sum id addressing: exact
  // --- in the mint code (see the contract note on multi-epoch in-flights).
  for (const c of inflight) {
    let node = root, i = 0;
    while (i < c.length) {
      const [d, j] = decodeOne(c, i);
      if (!settled.has(node.id + d)) { node.inflightChild = true; break; }
      node = childOf(node, d);
      node.seedSettled = true;
      i = j;
    }
    if (i >= c.length && node !== root) node.inflightHere = true;
  }

  // --- settled evidence, bottom-up (post-order): a node is evidenced
  // --- settled by its own listed record, by the in-flight walk, or by any
  // --- evidenced descendant (cuts are causally downward closed, so a
  // --- settled record witnesses its entire dead ancestor chain).
  const post = [];
  {
    const st = [root];
    while (st.length > 0) {
      const n = st.pop();
      post.push(n);
      for (const ch of n.children.values()) st.push(ch);
    }
  }
  for (let k = post.length - 1; k >= 0; k--) {
    const n = post[k];
    n.evidence = n.seedSettled
      || (n.recordId !== null && settled.has(n.recordId))
      || [...n.children.values()].some((ch) => ch.evidence);
  }

  // --- stability + rank-renumbering (+ spine fusion), pre-order
  root.stable = true;
  const stats = {
    symbolsBefore, symbolsAfter: 0,
    groupsRenumbered: 0, groupsSkippedInflight: 0, groupsSkippedUnstable: 0,
    spinesFused: 0, levelsRemoved: 0, spinesSkippedInflight: 0,
  };

  // Spine fusion (step 2b). head has its newCoord assigned; walks the
  // maximal chain of dead, settled, single-child, in-flight-free nodes and
  // collapses it onto the head's level. Returns the node the pre-order
  // traversal resumes from: the spine tail dk when fused (its child group
  // is then processed normally, so intermediate singleton groups are never
  // visited), else head itself. A structurally fusible node carrying an
  // in-flight branch/anchor is never a member; it is counted once, when
  // examined as a head.
  const spineMember = (n) => n.recordId === null && n.stable && n.children.size === 1;
  const inflightFree = (n) => !n.inflightChild && !n.inflightHere;
  const fuseSpine = (head) => {
    if (!spineMember(head)) return head;
    if (!inflightFree(head)) { stats.spinesSkippedInflight++; return head; }
    const members = [head];
    for (;;) {
      const n = members[members.length - 1];
      const next = n.children.values().next().value;
      next.stable = n.stable && next.evidence; // idempotent vs the main loop
      if (!spineMember(next) || !inflightFree(next)) break;
      members.push(next);
    }
    if (members.length < 2) return head; // k = 1: fusion is the identity
    for (let k = 1; k < members.length; k++) members[k].newCoord = head.newCoord;
    stats.spinesFused++;
    stats.levelsRemoved += members.length - 1;
    return members[members.length - 1];
  };

  const stack = [root];
  while (stack.length > 0) {
    const node = stack.pop();
    const kids = [...node.children.values()].sort((x, y) => x.delta - y.delta);
    if (kids.length === 0) {
      // a group whose only known members are in flight is a skipped group
      if (node.inflightChild) stats.groupsSkippedInflight++;
      continue;
    }
    for (const ch of kids) ch.stable = node.stable && ch.evidence;
    const allStable = kids.every((ch) => ch.stable);
    const renumber = allStable && (!node.inflightChild || unguarded);
    if (renumber) stats.groupsRenumbered++;
    else if (allStable) stats.groupsSkippedInflight++;
    else stats.groupsSkippedUnstable++;
    kids.forEach((ch, idx) => {
      ch.newCoord = node.newCoord + enc(renumber ? idx + 1 : ch.delta);
      stack.push(fuse ? fuseSpine(ch) : ch);
    });
  }

  // --- state': at-rest records re-coded (one transient pass -> PMap)
  const s2t = PMap.empty().begin();
  for (const [id, rec] of state) {
    const nc = nodeOf.get(id).newCoord;
    stats.symbolsAfter += nc.length;
    s2t.set(id, Object.freeze({ coord: nc, el: rec.el }));
  }
  const s2 = s2t.freeze();

  // --- translate: rho-hat(c) = rho(stab c) ++ rest c
  const translate = (coord) => {
    let node = root, i = 0;
    while (i < coord.length) {
      const [d, j] = decodeOne(coord, i);
      const ch = node.children.get(d);
      if (!ch) break; // left the mapped region: rest verbatim
      node = ch;
      i = j;
    }
    return node.newCoord + coord.slice(i);
  };

  return { state: s2, translate, stats };
}

/** Record-wise coordinate translation (the runtime's epoch-lifting hook). */
export function remapState(state, translate) {
  const s = PMap.empty().begin();
  for (const [id, rec] of state) {
    s.set(id, Object.freeze({ coord: translate(rec.coord), el: rec.el }));
  }
  return s.freeze();
}

/** The embed RGA with the state-GC hooks the runtime looks for. compact +
 *  remapState drive the certified state GC; encodeState + decodeState are the
 *  wire/disk (de)serialization of a COMPACTION commit's inline state, which
 *  cannot be recomputed from a parent (src/replica.js ships/ingests it
 *  parametrically through these -- a datatype that never compacts needs
 *  neither). */
export const compactibleEmbedRGA = {
  ...embedRGA,
  compact: compactEliasDelta,
  remapState,
  encodeState: (state) => [...state.entries()].map(([id, r]) => [id, r.coord, r.el]),
  decodeState: (enc) => PMap.from(enc.map(([id, coord, el]) => [id, Object.freeze({ coord, el })])),
};
