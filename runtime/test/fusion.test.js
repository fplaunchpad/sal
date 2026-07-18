// SPINE FUSION tests (task #97 iteration two; design:
// whiteboard/embed-recoding-note.md Addendum 2, implementation step 2b of
// src/compact.js, opt-in via opts.fuseSpines).
//
// EXPECTED VALUES ARE HAND-DERIVED from the flipped Elias-delta code,
// never evaluated from the implementation under test. Reference codewords
// (same derivation as test/compact.test.js, pinned against the
// kernel-checked values in test/code.test.js):
//   enc(1)='0'  enc(2)='1000'  enc(3)='1001'  enc(4)='10100'
//   enc(5)='10101'  enc(9)='11000001'  enc(12)='11000100'
//   enc(13)='11000101'  enc(14)='11000110'  enc(15)='11000111'
//   enc(25)='110011001'
//
// Suites:
//   1. directed typing-run-then-delete: a nine-node dead spine collapses
//      to one level (10 bits -> 2); the renumber-only pass CANNOT deliver
//      this (its result is pinned unchanged at 10 bits: the FAIL-shaped
//      companion separating fusion from renumbering);
//   2. H2 comparison class 1 (within the fused block): anchor-above-
//      descendant and newest-first-sibling order inside the block, both
//      preserved;
//   3. H2 comparison class 2 (block vs the head's siblings): a live
//      sibling with an ordinal on EACH side of the fused block, order
//      preserved on both sides;
//   4. H2 comparison class 3 (mints under compacted state): a fresh mint
//      under the fused child extends the fused coordinate natively; plus
//      mints under a renumbered sibling and at the root, all against a
//      never-compacted control;
//   5. in-flight THROUGH the spine: (a) the runtime lazy-translation path
//      (a never-compacted replica's old-spine-levels record translated on
//      ingest), (b) a DECLARED in-flight through the spine at the
//      datatype level -- the spine still fuses, the frozen tail is kept
//      verbatim;
//   6. THE GUARD: a spine with an in-flight second branch (an in-flight
//      op anchored at a spine node) is NOT fused (spinesSkippedInflight),
//      and the compaction stays sound;
//   7. twin PBT with fusion enabled: per-step read equality vs an
//      uncompacted control, criss-cross verdict agreement, compaction
//      never grows a state, LIVE oracle, aggregate fusion statistics.

import test from 'node:test';
import assert from 'node:assert/strict';
import { Runtime } from '../src/runtime.js';
import { mcas } from '../src/lca.js';
import {
  compactEliasDelta, compactibleEmbedRGA as D, decodeChain,
} from '../src/compact.js';

const range = (a, b) => Array.from({ length: b - a + 1 }, (_, i) => a + i);
const FUSE = { fuseSpines: true };

// --------------------------------------- 1. directed typing run + delete

// Typing run: ins 1..10, each anchored at its predecessor (delta 1
// everywhere, elements 'a'..'j'), then delete 1..9. Live: id 10 alone,
// coord enc(1)^10 = '0000000000' (10 bits: nine dead spine levels plus
// its own). The dead chain 1..9 is one maximal fusible spine (k = 9,
// node 10 is live and ends it). Fusion:
//   block 1..9 -> enc(1) = '0'   (node 1's ordinal in the root group)
//   node 10    -> '0' ++ enc(1) = '00'         (2 bits; levelsRemoved 8)
// Renumber-only leaves 10 bits: every group is already a singleton at
// ordinal 1, so v1 saves NOTHING here -- the separation this suite pins.
function typingRunState() {
  let s = D.init();
  s = D.apply(s, { type: 'ins', id: 1, el: 'a', anchorId: null });
  for (const id of range(2, 10)) {
    s = D.apply(s, { type: 'ins', id, el: String.fromCharCode(96 + id), anchorId: id - 1 });
  }
  for (const id of range(1, 9)) s = D.apply(s, { type: 'del', id });
  return s;
}
const typingCut = () => ({ settledIds: new Set(range(1, 10)), inflight: [] });

test('typing-run spine collapses: 10 bits -> 2, read pinned, translate pinned', () => {
  const s = typingRunState();
  assert.deepEqual(D.read(s), ['j']);
  assert.equal(s.get(10).coord, '0000000000');                 // 10 x enc(1)
  const { state: s2, translate, stats } = compactEliasDelta(s, typingCut(), FUSE);
  assert.deepEqual(D.read(s2), ['j']);                         // read identical
  assert.equal(s2.get(10).coord, '00');                        // hand-derived
  assert.deepEqual(decodeChain(s2.get(10).coord), [1, 1]);     // block + own level
  assert.equal(stats.symbolsBefore, 10);
  assert.equal(stats.symbolsAfter, 2);
  assert.equal(stats.spinesFused, 1);
  assert.equal(stats.levelsRemoved, 8);
  assert.equal(stats.spinesSkippedInflight, 0);
  assert.equal(stats.groupsRenumbered, 2);   // root group + dk's child group
  // the stable-prefix map, pinned pointwise
  assert.equal(translate('0000000000'), '00');   // the live record, old code
  assert.equal(translate('000000000'), '0');     // dk (node 9) -> the fused block
  assert.equal(translate('110011001'), '110011001'); // unknown root delta 25: verbatim
});

test('FAIL companion: renumber-only does NOT collapse the spine (10 bits stay)', () => {
  const s = typingRunState();
  const { state: s2, stats } = compactEliasDelta(s, typingCut()); // no fuseSpines
  assert.equal(s2.get(10).coord, '0000000000');                // unchanged
  assert.equal(stats.symbolsAfter, 10);
  assert.equal(stats.spinesFused, 0);                          // fusion off: 0
  assert.notEqual(s2.get(10).coord, '00');                     // fusion is not renumbering
});

// ------------------------- 2. H2 class 1: order WITHIN the fused block

// ins 1 'a' root; 2 'b' <-1; 3 'c' <-2; 4 'd' <-3; 5 'e' <-4; 8 'f' <-4;
// del 1,2,3. Live: 4 = '0000', 5 = '00000', 8 = '0000'++enc(4) =
// '000010100' (18 symbols). Read [d, f, e]: d is the anchor above its
// children, f (delta 4) newest-first before e (delta 1).
// Fusion (settled cut over 1..8): spine [1,2,3] -> '0'; 4 -> '00';
// group {5, 8} renumbers to ordinals 1, 2: 5 -> '000', 8 -> '001000'
// (11 symbols). Both within-block comparisons ride the common prefix
// replaced wholesale: order must be untouched.
test('H2 class 1: anchor-above-descendant and sibling order inside the block', () => {
  let s = D.init();
  s = D.apply(s, { type: 'ins', id: 1, el: 'a', anchorId: null });
  s = D.apply(s, { type: 'ins', id: 2, el: 'b', anchorId: 1 });
  s = D.apply(s, { type: 'ins', id: 3, el: 'c', anchorId: 2 });
  s = D.apply(s, { type: 'ins', id: 4, el: 'd', anchorId: 3 });
  s = D.apply(s, { type: 'ins', id: 5, el: 'e', anchorId: 4 });
  s = D.apply(s, { type: 'ins', id: 8, el: 'f', anchorId: 4 });
  for (const id of [1, 2, 3]) s = D.apply(s, { type: 'del', id });
  assert.deepEqual(D.read(s), ['d', 'f', 'e']);                // hand-derived
  assert.equal(D.symbolCount(s), 18);                          // 4 + 5 + 9
  const cut = { settledIds: new Set([1, 2, 3, 4, 5, 8]), inflight: [] };
  const { state: s2, stats } = compactEliasDelta(s, cut, FUSE);
  assert.deepEqual(D.read(s2), ['d', 'f', 'e']);               // class-1 order kept
  assert.equal(s2.get(4).coord, '00');
  assert.equal(s2.get(5).coord, '000');
  assert.equal(s2.get(8).coord, '001000');                     // ordinal 2 = enc(2)
  assert.equal(D.symbolCount(s2), 11);
  assert.equal(stats.spinesFused, 1);
  assert.equal(stats.levelsRemoved, 2);
  // FAIL companion: renumber-only lands at 17 symbols (only 8's delta
  // densifies, 4->'0000' keeps all spine levels), strictly worse.
  const { state: r2 } = compactEliasDelta(s, cut);
  assert.equal(r2.get(4).coord, '0000');
  assert.equal(D.symbolCount(r2), 17);
  assert.ok(D.symbolCount(s2) < D.symbolCount(r2));
});

// --------------- 3. H2 class 2: the block vs the head's siblings, both sides

// Root group: 2 'L', 5 'm', 9 'R'; 6 'n' <-5; 7 'p' <-6; del 5, del 6.
// Live: 2 = '1000', 7 = '1010100', 9 = '11000001'. Read [R, p, L]
// (newest root first; the 5-block's content between its siblings).
// Fusion (settled {2,5,6,7,9}): root ordinals 2 -> 1, 5 -> 2, 9 -> 3;
// spine [5,6] (k = 2) -> block '1000'; 7 -> '10000'. The block inherits
// the head's ordinal 2, so it still sits BETWEEN L (ordinal 1) and R
// (ordinal 3): the class-2 comparison decided at the head's level.
function blockVsSiblingState() {
  let s = D.init();
  s = D.apply(s, { type: 'ins', id: 2, el: 'L', anchorId: null });
  s = D.apply(s, { type: 'ins', id: 5, el: 'm', anchorId: null });
  s = D.apply(s, { type: 'ins', id: 6, el: 'n', anchorId: 5 });
  s = D.apply(s, { type: 'ins', id: 7, el: 'p', anchorId: 6 });
  s = D.apply(s, { type: 'ins', id: 9, el: 'R', anchorId: null });
  s = D.apply(s, { type: 'del', id: 5 });
  s = D.apply(s, { type: 'del', id: 6 });
  return s;
}
const blockCut = () => ({ settledIds: new Set([2, 5, 6, 7, 9]), inflight: [] });

test('H2 class 2: fused block keeps its ordinal between live siblings', () => {
  const s = blockVsSiblingState();
  assert.deepEqual(D.read(s), ['R', 'p', 'L']);                // hand-derived
  const { state: s2, stats } = compactEliasDelta(s, blockCut(), FUSE);
  assert.deepEqual(D.read(s2), ['R', 'p', 'L']);               // both sides hold
  assert.equal(s2.get(2).coord, '0');                          // ordinal 1
  assert.equal(s2.get(7).coord, '10000');                      // block(ord 2) ++ enc(1)
  assert.equal(s2.get(9).coord, '1001');                       // ordinal 3
  assert.deepEqual(decodeChain(s2.get(7).coord), [2, 1]);      // the block LEVEL survives
  assert.equal(stats.spinesFused, 1);
  assert.equal(stats.levelsRemoved, 1);
});

// ------------------- 4. H2 class 3: mints under the compacted state

// Continue class 2 through the runtime: after the fused compaction, mint
// q = 12 under the fused child 7 (delta 5, extends the FUSED coordinate
// natively: '10000'++enc(5)), v = 14 under renumbered sibling 2 (delta
// 12), w = 15 at the root (Lamport-fresh past the block). Control twin
// never compacts. Hand-derived read on both sides: [w, R, p, q, L, v].
test('H2 class 3: mint under the fused child (and siblings/root) vs control', () => {
  const mk = () => {
    const rt = new Runtime(D);
    const r = rt.replica('A');
    r.commit({ type: 'ins', id: 2, el: 'L', anchorId: null });
    r.commit({ type: 'ins', id: 5, el: 'm', anchorId: null });
    r.commit({ type: 'ins', id: 6, el: 'n', anchorId: 5 });
    r.commit({ type: 'ins', id: 7, el: 'p', anchorId: 6 });
    r.commit({ type: 'ins', id: 9, el: 'R', anchorId: null });
    r.commit({ type: 'del', id: 5 });
    r.commit({ type: 'del', id: 6 });
    return r;
  };
  const mint = (r) => {
    r.commit({ type: 'ins', id: 12, el: 'q', anchorId: 7 });
    r.commit({ type: 'ins', id: 14, el: 'v', anchorId: 2 });
    r.commit({ type: 'ins', id: 15, el: 'w', anchorId: null });
  };
  const control = mk();
  mint(control);
  assert.deepEqual(control.read(), ['w', 'R', 'p', 'q', 'L', 'v']); // hand-derived
  const subj = mk();
  const { stats } = subj.compact(blockCut(), FUSE);
  assert.equal(stats.spinesFused, 1);
  mint(subj);
  assert.equal(subj.head.state.get(12).coord, '1000010101');   // '10000'++enc(5)
  assert.equal(subj.head.state.get(14).coord, '011000100');    // '0'++enc(12)
  assert.equal(subj.head.state.get(15).coord, '11000111');     // enc(15)
  assert.deepEqual(subj.read(), control.read());               // reads identical
});

// -------------------------- 5. in-flight THROUGH the fused spine

// Shared, fully settled base: 5 'm' root; 6 'n' <-5; 7 'p' <-6; del 5,
// del 6. Live: p = '1010100' (the two dead spine levels inside it).
// Fused compaction: root {5} -> ordinal 1 = '0'; spine [5,6] -> block
// '0'; 7 -> '00'. A record minted elsewhere against the OLD coordinates,
// anchored at 7 (id 20, delta 13): '1010100'++enc(13). Its translation
// re-maps the spine levels and keeps the fresh delta verbatim:
// '00'++'11000101' = '0011000101'. Read [p, z] (z is p's child).
test('in-flight through the spine 5a: runtime lazy translation on ingest', () => {
  const mk = () => {
    const rt = new Runtime(D);
    const a = rt.replica('A'), b = rt.replica('B');
    a.commit({ type: 'ins', id: 5, el: 'm', anchorId: null });
    a.commit({ type: 'ins', id: 6, el: 'n', anchorId: 5 });
    a.commit({ type: 'ins', id: 7, el: 'p', anchorId: 6 });
    a.commit({ type: 'del', id: 5 });
    a.commit({ type: 'del', id: 6 });
    b.sync(a); // fully delivered: the cut below is genuinely settled
    return { a, b };
  };
  const control = mk();
  control.b.commit({ type: 'ins', id: 20, el: 'z', anchorId: 7 });
  control.a.sync(control.b);
  assert.deepEqual(control.a.read(), ['p', 'z']);              // hand-derived
  const subj = mk();
  const { stats } = subj.a.compact({ settledIds: new Set([5, 6, 7]), inflight: [] }, FUSE);
  assert.equal(stats.spinesFused, 1);
  assert.equal(subj.a.head.state.get(7).coord, '00');
  subj.b.commit({ type: 'ins', id: 20, el: 'z', anchorId: 7 }); // old-code mint
  assert.equal(subj.b.head.state.get(20).coord, '101010011000101'); // pre-merge
  subj.a.sync(subj.b);
  assert.equal(subj.a.head.state.get(20).coord, '0011000101'); // spine levels re-mapped
  assert.deepEqual(subj.a.read(), control.a.read());           // reads = control
  assert.deepEqual(subj.b.read(), control.a.read());
});

test('in-flight through the spine 5b: DECLARED in cut.inflight, spine still fuses', () => {
  let s = D.init();
  s = D.apply(s, { type: 'ins', id: 5, el: 'm', anchorId: null });
  s = D.apply(s, { type: 'ins', id: 6, el: 'n', anchorId: 5 });
  s = D.apply(s, { type: 'ins', id: 7, el: 'p', anchorId: 6 });
  s = D.apply(s, { type: 'del', id: 5 });
  s = D.apply(s, { type: 'del', id: 6 });
  const Z = '101010011000101'; // coord(7) ++ enc(13), minted elsewhere, in flight
  const cut = { settledIds: new Set([5, 6, 7]), inflight: [Z] };
  const { state: s2, translate, stats } = compactEliasDelta(s, cut, FUSE);
  assert.equal(stats.spinesFused, 1);                          // through-traffic fuses
  assert.equal(stats.spinesSkippedInflight, 0);
  assert.equal(stats.groupsSkippedInflight, 1);                // 7's child group frozen
  assert.equal(s2.get(7).coord, '00');
  assert.equal(translate(Z), '0011000101');                    // frozen delta verbatim
  const ingested = new Map(s2);
  ingested.set(20, Object.freeze({ coord: translate(Z), el: 'z' }));
  const full = D.apply(s, { type: 'ins', id: 20, el: 'z', anchorId: 7 });
  assert.deepEqual(D.read(ingested), D.read(full));            // sound: [p, z]
});

// ------------------- 6. THE GUARD: in-flight second branch, NOT fused

// Same chain 5 -> 6 -> 7, but the concurrent replica anchored its
// in-flight mint AT SPINE NODE 6 (id 20, delta 14): node 6 has a known
// in-flight branch, so it is never a spine member -- nothing fuses (the
// only candidate had k = 1). 7 keeps three levels; the in-flight's
// frozen delta lands in 6's child group, which the v1 guard also refuses
// to renumber. Reads still match the fully-delivered control.
test('guard: a spine with an in-flight second branch is NOT fused, still sound', () => {
  const mk = () => {
    const rt = new Runtime(D);
    const a = rt.replica('A'), c = rt.replica('C');
    a.commit({ type: 'ins', id: 5, el: 'm', anchorId: null });
    a.commit({ type: 'ins', id: 6, el: 'n', anchorId: 5 });
    a.commit({ type: 'ins', id: 7, el: 'p', anchorId: 6 });
    c.sync(a);
    c.commit({ type: 'ins', id: 20, el: 'z', anchorId: 6 });   // in flight to A
    a.commit({ type: 'del', id: 5 });
    a.commit({ type: 'del', id: 6 });
    return { a, c };
  };
  const control = mk();
  control.a.sync(control.c);
  assert.deepEqual(control.a.read(), ['z', 'p']);              // hand-derived
  const subj = mk();
  const Z = '10101011000110';                                  // coord(6) ++ enc(14)
  const { stats } = subj.a.compact(
    { settledIds: new Set([5, 6, 7]), inflight: [Z] }, FUSE);
  assert.equal(stats.spinesFused, 0);                          // THE GUARD
  assert.equal(stats.levelsRemoved, 0);
  assert.equal(stats.spinesSkippedInflight, 1);                // counted once
  assert.equal(stats.groupsRenumbered, 2);                     // root {5} + {6}
  assert.equal(stats.groupsSkippedInflight, 1);                // 6's child group
  assert.equal(subj.a.head.state.get(7).coord, '000');
  assert.deepEqual(decodeChain(subj.a.head.state.get(7).coord), [1, 1, 1]); // 3 levels kept
  subj.a.sync(subj.c);                                         // z translated on ingest
  assert.equal(subj.a.head.state.get(20).coord, '0011000110'); // '00' ++ frozen enc(14)
  assert.deepEqual(subj.a.read(), control.a.read());           // sound
  assert.deepEqual(subj.c.read(), control.a.read());
});

// ------------------------------------------------------------- 7. PBT

function mulberry32(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
const pick = (rng, xs) => xs[Math.floor(rng() * xs.length)];
const canon = (xs) => [...xs].map((x) => JSON.stringify(x)).sort();
const P = { pSync: 0.25, pDel: 0.35, pCompact: 0.12, pTyping: 0.7 };

// Twin execution, the compact.test.js harness pattern with fusion ON:
// identical random head-sync runs; the SUBJECT compacts (fuseSpines) at
// explicitly-settled points, the CONTROL never compacts. The op mix is
// biased toward TYPING RUNS (anchor at your own previous insert when it
// is still live) so deep spines actually arise once run-deletes land.
// Asserted per step, per replica: reads identical across twins;
// compaction never grows a state; LIVE oracle at the end.
//
// CRISS-CROSS GATING (a finding, diverging from the v1 harness): the
// subject's compaction commits perturb the commit graph -- a pair whose
// sync is a FAST-FORWARD in the control (one head subsumes the other)
// can be a REAL MERGE in the subject once an epoch commit sits between
// them -- so downstream criss-cross verdicts are NOT twin-stable; the v1
// harness's verdict-agreement assert survives only by schedule luck.
// Here gating is PRE-CHECKED on both twins and the pair is skipped if
// EITHER gates, which keeps the twins' delivered event sets in lockstep
// (the property the read assertions need); verdict divergences are
// counted and reported, not asserted away.
function runFusionTrial(seed) {
  const rng = mulberry32(seed);
  const nRep = 3 + (seed % 3);
  const nSteps = 35 + Math.floor(rng() * 36);
  const control = new Runtime(D);
  const subject = new Runtime(D);
  const cReps = Array.from({ length: nRep }, (_, i) => control.replica('r' + i));
  const sReps = Array.from({ length: nRep }, (_, i) => subject.replica('r' + i));
  const mint = { next: 1 };
  const insMinted = new Set();
  const lastIns = Array(nRep).fill(null); // per-replica typing anchor
  const stats = {
    compactions: 0, saved: 0, syncs: 0, skipped: 0, gateDiverged: 0,
    liftedMerges: 0, spinesFused: 0, levelsRemoved: 0, spinesSkippedInflight: 0,
  };

  // Would this pair's sync be criss-cross gated? (No mutation: pre-check.)
  const wouldGate = (rt, x, y) => {
    const a = x.head.id, b = y.head.id;
    if (a === b || rt.dag.isAncestor(a, b) || rt.dag.isAncestor(b, a)) return false;
    return mcas(rt.dag, a, b).length !== 1;
  };

  const doSync = (i, j) => {
    const gC = wouldGate(control, cReps[i], cReps[j]);
    const gS = wouldGate(subject, sReps[i], sReps[j]);
    if (gC !== gS) stats.gateDiverged++;   // epoch commits perturb the graph
    if (gC || gS) { stats.skipped++; return; }
    const a = sReps[i].head, b = sReps[j].head;
    if (a.id !== b.id
        && !subject.dag.isAncestor(a.id, b.id) && !subject.dag.isAncestor(b.id, a.id)
        && subject.epochOf.get(a.id) !== subject.epochOf.get(b.id)) {
      stats.liftedMerges++;
    }
    cReps[i].sync(cReps[j]);               // pre-checked: neither may throw
    sReps[i].sync(sReps[j]);
    stats.syncs++;
  };

  const settleAndCompact = () => {
    for (let pass = 0; pass < 3; pass++) {
      for (let i = 0; i < nRep; i++) for (let j = i + 1; j < nRep; j++) doSync(i, j);
    }
    const h = sReps[0].head.id;
    if (!sReps.every((r) => r.head.id === h)) return;  // criss-cross gated: not settled
    const r = pick(rng, sReps);
    const before = r.read();
    const { stats: cs } = r.compact({ settledIds: new Set(insMinted), inflight: [] }, FUSE);
    assert.deepEqual(r.read(), before, 'compaction changed the read');
    assert.ok(cs.symbolsAfter <= cs.symbolsBefore, 'compaction grew the state');
    assert.equal(cs.spinesSkippedInflight, 0, 'settled cut declared no in-flight');
    stats.compactions++;
    stats.saved += cs.symbolsBefore - cs.symbolsAfter;
    stats.spinesFused += cs.spinesFused;
    stats.levelsRemoved += cs.levelsRemoved;
    stats.spinesSkippedInflight += cs.spinesSkippedInflight;
  };

  for (let step = 0; step < nSteps; step++) {
    const r = Math.floor(rng() * nRep);
    if (rng() < P.pCompact) {
      settleAndCompact();
    } else if (rng() < P.pSync) {
      const j = Math.floor(rng() * nRep);
      if (j !== r) doSync(r, j);
    } else {
      assert.deepEqual(sReps[r].read(), cReps[r].read(), `pre-op read @${step} r${r}`);
      const doc = subject.datatype.readIds(sReps[r].head.state);
      let op;
      if (doc.length > 0 && rng() < P.pDel) {
        // RUN-delete in display order (the realistic editing pattern, and
        // what actually manufactures dead spines: a cleared chain prefix
        // above a survivor). Both twins get the identical run.
        const at = Math.floor(rng() * doc.length);
        const run = doc.slice(at, at + 1 + Math.floor(rng() * 4));
        for (const id of run.slice(1)) {
          cReps[r].commit({ type: 'del', id });
          sReps[r].commit({ type: 'del', id });
        }
        op = { type: 'del', id: run[0] };
      } else {
        const id = mint.next++;
        insMinted.add(id);
        const typing = lastIns[r] !== null && doc.includes(lastIns[r]) && rng() < P.pTyping;
        const anchorId = typing ? lastIns[r]
          : (doc.length > 0 && rng() < 0.6 ? pick(rng, doc) : null);
        op = { type: 'ins', id, el: id, anchorId };
        lastIns[r] = id;
      }
      cReps[r].commit(op);
      sReps[r].commit(op);
    }
    for (let i = 0; i < nRep; i++) {
      assert.deepEqual(sReps[i].read(), cReps[i].read(), `read @${step} r${i}`);
    }
  }

  for (let pass = 0; pass < 3; pass++) {
    for (let i = 0; i < nRep; i++) for (let j = i + 1; j < nRep; j++) doSync(i, j);
  }
  for (let i = 0; i < nRep; i++) {
    assert.deepEqual(sReps[i].read(), cReps[i].read(), 'final read');
    // LIVE oracle: read = fold of the head's implicit event set
    const evs = subject.dag.events(sReps[i].head.id).map((o) => o.payload);
    const del = new Set(evs.filter((p) => p.type === 'del').map((p) => p.id));
    const live = evs.filter((p) => p.type === 'ins' && !del.has(p.id)).map((p) => p.id);
    assert.deepEqual(canon(sReps[i].read()), canon(live), `LIVE oracle r${i}`);
  }
  return stats;
}

test('twin PBT with fusion enabled: 120 trials vs uncompacted control', (t) => {
  const tot = {
    compactions: 0, saved: 0, syncs: 0, skipped: 0, gateDiverged: 0,
    liftedMerges: 0, spinesFused: 0, levelsRemoved: 0, spinesSkippedInflight: 0,
  };
  for (let seed = 0; seed < 120; seed++) {
    const s = runFusionTrial(seed * 47303 + 11);
    for (const k of Object.keys(tot)) tot[k] += s[k];
  }
  t.diagnostic(`fusion PBT: ${JSON.stringify(tot)}`);
  assert.ok(tot.compactions > 100, `compaction must fire (${tot.compactions})`);
  assert.ok(tot.saved > 500, `compaction must actually save symbols (${tot.saved})`);
  assert.ok(tot.spinesFused > 100, `fusion must actually fire (${tot.spinesFused})`);
  assert.ok(tot.levelsRemoved >= tot.spinesFused,
    `every fused spine removes at least one level (${tot.levelsRemoved})`);
  assert.ok(tot.liftedMerges > 50,
    `the lazy-translation merge path must be exercised (${tot.liftedMerges})`);
});
