// THE MARKS-LAYER STATE GC: src/compact-peritext.js implements retention
// roots (H-A) and the A3 guarded pair-drop. Peritext's compactStable refuses
// without a certificate and fires with one.
//
// EXPECTED VALUES ARE HAND-DERIVED from the read rules R1-R4 (re-derived in
// comments below), never evaluated from the implementation under test; the
// PBT's specification is the never-compacted twin, which is not the
// implementation under test. Reference codewords (test/compact.test.js
// header, kernel-pinned in code.test.js):
//   enc(1)='0' enc(2)='1000' enc(3)='1001' enc(4)='10100' enc(5)='10101'
//   enc(9)='11000001' enc(19)='110010011'
//
// PASS+FAIL convention: every reads-identical claim carries a companion
// pinning the tempting degenerate behavior --
//   (a) the NONE control (opts.noRetention) FLIPS a read,
//   (b) the A3 alpha flip (an UNDECLARED straggler add inside the mid
//       window makes the guarded-looking drop unsound; declaring it makes
//       the guard refuse),
//   (c) the A3 beta flip (a settled char inside the growth window
//       (add.mid, remove.mid); the unguarded drop fires and flips, the
//       window guard refuses),
//   plus the unguardedRenumber order flip through the peritext path and
//   directed non-constancy inequalities.

import test from 'node:test';
import assert from 'node:assert/strict';
import { peritextEmbedRGA as peritext } from '../src/datatypes/peritext.js';
import { embedRGA } from '../src/datatypes/embedRGA.js';
import {
  compactPeritext, compactiblePeritext, compactSharedPeritext,
  compactibleSharedPeritext, compactSidedPeritext, compactibleSidedPeritext,
} from '../src/compact-peritext.js';
import { DistributedReplica, syncReplicas } from '../src/replica.js';

const build = (ops) => ops.reduce((s, op) => peritext.apply(s, op), peritext.init());
const ins = (id, el, anchorId) => ({ type: 'ins', id, el, anchorId });
const del = (id) => ({ type: 'del', id });
const mark = (mid, mtype, startId, endId, startSide = 'before', endSide = 'after') =>
  ({ type: 'addMark', mid, mtype, startId, endId, startSide, endSide });
const unmark = (mid, mtype, startId, endId, startSide = 'before', endSide = 'after') =>
  ({ type: 'removeMark', mid, mtype, startId, endId, startSide, endSide });
const flags = (s, mt) => peritext.flags(s, mt);
const order = (s) => peritext.read(s).map((e) => e.char);
const eq = (x) => JSON.stringify(x);
const birthIds = (s) => embedRGA.readEntries(s.text.shadow).map(([id]) => id);
const liveIds = (s) => birthIds(s).filter((x) => !s.text.deleted.has(x));

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

// D1 geometry: R=1 and L=2 minted at the root (L newer,
// reads first), d=3 child of L; reading order L d R; mark mid 5; d deleted.
const d1Barrier = (m) => build([ins(1, 'R', null), ins(2, 'L', null),
  ins(3, 'd', 2), m, del(3)]);
const d1Cut = () => ({
  settledIds: new Set([1, 2, 3]), settledDelIds: new Set([3]),
  settledMarkMids: new Set([5]), inflightIns: [], inflightMarks: [],
});

// ------------------------------------------------- D6: the no-retention flip
test('D6: retention keeps the read; the NONE control FLIPS it', () => {
  // Mark [start L before, end d after] mid 5; d dead.
  // Twin (hand, R2/R3): end anchor d is dead, endSide=after scans LEFT in
  // birth order L d R and finds L; covered {L}: L BOLD, R plain.
  const barrier = d1Barrier(mark(5, 'bold', 2, 3, 'before', 'after'));
  assert.deepEqual(flags(barrier, 'bold'), [['L', true], ['R', false]], 'twin (hand: L bold)');

  // PASS: retention roots keep d as a dead record; reads identical.
  const g = compactPeritext(barrier, d1Cut());
  assert.deepEqual(flags(g.state, 'bold'), [['L', true], ['R', false]], 'retained: read kept');
  assert.equal(g.state.text.shadow.has(3), true, 'dead anchor d retained as a record');
  assert.equal(g.state.text.deleted.has(3), true, 'and still listed in deleted');
  assert.equal(g.stats.retainedForMarks, 1);
  assert.equal(g.stats.recordsDropped, 0);

  // FAIL companion (a): no retention -> d has no record, the resolver
  // degrades to the collapse branch; covered {}: L PLAIN. FLIP.
  const n = compactPeritext(barrier, d1Cut(), { noRetention: true });
  assert.equal(n.state.text.shadow.has(3), false, 'NONE drops the dead anchor');
  assert.equal(n.stats.recordsDropped, 1);
  assert.deepEqual(flags(n.state, 'bold'), [['L', false], ['R', false]], 'hand: FLIP to plain');
  assert.notDeepEqual(flags(n.state, 'bold'), flags(barrier, 'bold'), 'the flip fires');

  // PASS companion: with LIVE mark anchors [L..R] even the NONE compactor
  // reads twin-identical (hand: covered {L,R}) -- the refusal's reason was
  // precisely dead mark anchors, nothing else.
  const live = d1Barrier(mark(5, 'bold', 2, 1, 'before', 'after'));
  assert.deepEqual(flags(live, 'bold'), [['L', true], ['R', true]], 'twin (hand: L,R bold)');
  const n2 = compactPeritext(live, d1Cut(), { noRetention: true });
  assert.equal(n2.state.text.shadow.has(3), false, 'interior dead d dropped (A2)');
  assert.deepEqual(flags(n2.state, 'bold'), [['L', true], ['R', true]], 'reads twin-identical');
});

// --------------------------- D1 straggler cells (declared in-flight inserts)
test('D1(b)/(c): declared stragglers around a retained dead anchor read as the twin', () => {
  // (b) end-inner cell: mark [L before, d after] mid 5; straggler n=4
  // anchored at L (OLDER than the mark), declared at the cut, delivered
  // after compaction. Twin (hand): birth L n d R (n delta 2
  // beats d delta 1 among L's children); end d dead scans left -> n live;
  // covered {L,n}: L,n bold, R plain.
  const bar1 = d1Barrier(mark(5, 'bold', 2, 3, 'before', 'after'));
  const twin1 = peritext.apply(bar1, ins(4, 'n', 2));
  assert.deepEqual(flags(twin1, 'bold'),
    [['L', true], ['n', true], ['R', false]], 'twin (hand: Ln)');
  const c1 = { ...d1Cut(), inflightIns: [{ id: 4, anchorId: 2 }] };
  const s1 = peritext.apply(compactPeritext(bar1, c1).state, ins(4, 'n', 2));
  assert.equal(eq(peritext.read(s1)), eq(peritext.read(twin1)), '(b) reads identical');

  // (c) start-inner cell: mark [d before, R after] mid 5; straggler n=4
  // anchored at the DEAD d itself. Twin (hand): birth L d n R; start d dead
  // scans right -> n; end R live; covered {n,R}.
  const bar2 = d1Barrier(mark(5, 'bold', 3, 1, 'before', 'after'));
  const twin2 = peritext.apply(bar2, ins(4, 'n', 3));
  assert.deepEqual(flags(twin2, 'bold'),
    [['L', false], ['n', true], ['R', true]], 'twin (hand: nR)');
  const c2 = { ...d1Cut(), inflightIns: [{ id: 4, anchorId: 3 }] };
  const s2 = peritext.apply(compactPeritext(bar2, c2).state, ins(4, 'n', 3));
  assert.equal(eq(peritext.read(s2)), eq(peritext.read(twin2)), '(c) reads identical');

  // FAIL companion: the two cells cover different sets (Ln vs nR) -- the
  // resolver is not a constant read across boundary shapes.
  assert.notEqual(eq(flags(s1, 'bold')), eq(flags(s2, 'bold')));
});

// -------------------- the frozen-anchor group guard through the peritext path
test('declared straggler freezes its sibling group; unguardedRenumber control FLIPS the order', () => {
  // A=1 root; b=3 (delta 2), c=10 (delta 9) children of A; straggler s=6
  // (delta 5) anchored at A, declared in flight. True sibling order
  // newest-first: c(9) > s(5) > b(2), so reading order A c s b.
  const barrier = build([ins(1, 'A', null), ins(3, 'b', 1), ins(10, 'c', 1)]);
  const cut = {
    settledIds: new Set([1, 3, 10]), settledDelIds: new Set(),
    settledMarkMids: new Set(), inflightIns: [{ id: 6, anchorId: 1 }],
    inflightMarks: [],
  };
  const twin = peritext.apply(barrier, ins(6, 's', 1));
  assert.deepEqual(order(twin), ['A', 'c', 's', 'b'], 'twin (hand: A c s b)');

  const g = compactPeritext(barrier, cut);
  assert.ok(g.stats.groupsSkippedInflight >= 1, 'the anchor group is skipped this epoch');
  const gs = peritext.apply(g.state, ins(6, 's', 1));
  assert.deepEqual(order(gs), ['A', 'c', 's', 'b'], 'guarded: order kept');

  // FAIL companion: dense renumbering against the frozen delta. b: 2->1,
  // c: 9->2 (enc 2 = '1000'); the frozen s ('10101') now beats the ex-9:
  // s JUMPS OVER c. NEVER set unguardedRenumber in production.
  const u = compactPeritext(barrier, cut, { unguardedRenumber: true });
  const us = peritext.apply(u.state, ins(6, 's', 1));
  assert.deepEqual(order(us), ['A', 's', 'c', 'b'], 'hand: s jumps c');
  assert.notDeepEqual(order(us), order(twin), 'the unguarded flip fires');
});

// ------------------------------------- D3: two boundaries in one dead run
test('D3: two retained dead anchors in one run keep their order; a gap straggler discriminates', () => {
  // A=1, x=2, y=3, B=4 chained; m1 bold [A..x] mid 10, m2 ital [A..y] mid
  // 11, inner sides; x,y deleted (one dead run); declared straggler g=5
  // anchored at x. g (delta 3) beats y (delta 1) among x's children:
  // birth A x g y B, live A g B.
  // Twin (hand): m1 end x dead scans left -> A: bold {A}. m2 end y dead
  // scans left -> g live: ital {A,g}. So g carries m2 and NOT m1: the
  // boundary order INSIDE the dead run is observable.
  const barrier = build([ins(1, 'A', null), ins(2, 'x', 1), ins(3, 'y', 2),
    ins(4, 'B', 3), mark(10, 'bold', 1, 2, 'before', 'after'),
    mark(11, 'ital', 1, 3, 'before', 'after'), del(2), del(3)]);
  const cut = {
    settledIds: new Set([1, 2, 3, 4]), settledDelIds: new Set([2, 3]),
    settledMarkMids: new Set([10, 11]), inflightIns: [{ id: 5, anchorId: 2 }],
    inflightMarks: [],
  };
  const twin = peritext.apply(barrier, ins(5, 'g', 2));
  assert.deepEqual(flags(twin, 'bold'), [['A', true], ['g', false], ['B', false]], 'twin bold (hand: A)');
  assert.deepEqual(flags(twin, 'ital'), [['A', true], ['g', true], ['B', false]], 'twin ital (hand: Ag)');

  const g = compactPeritext(barrier, cut);
  // x is a mark anchor AND the declared straggler's anchor (counted as an
  // in-flight anchor, not a mark retention); y is retained for m2.
  assert.equal(g.stats.retainedForMarks, 1);
  assert.equal(g.stats.recordsDropped, 0);
  const s = peritext.apply(g.state, ins(5, 'g', 2));
  assert.deepEqual(birthIds(s), [1, 2, 5, 3, 4], 'retained dead run keeps its internal order (A1)');
  assert.equal(eq(peritext.read(s)), eq(peritext.read(twin)), 'reads identical');
  // FAIL companion: bold and ital genuinely differ on g -- the retained
  // order is load-bearing, not decorative.
  assert.notEqual(eq(flags(s, 'bold')), eq(flags(s, 'ital')));
});

// --------------------------------------- D7 gamma: the guarded A3 pair-drop
test('A3 guarded pair-drop frees the retention root, reads identical', () => {
  // A=1, B=2 child of A; add bold [A..B] mid 3, remove bold [A..B] mid 4,
  // same sides; B deleted. Guards hold: removal settled, no other bold
  // mark below 4, window (3,4) empty. The pair drops AND the root B (dead,
  // referenced only by the pair) is freed.
  const barrier = build([ins(1, 'A', null), ins(2, 'B', 1),
    mark(3, 'bold', 1, 2, 'before', 'after'),
    unmark(4, 'bold', 1, 2, 'before', 'after'), del(2)]);
  const cut = () => ({
    settledIds: new Set([1, 2]), settledDelIds: new Set([2]),
    settledMarkMids: new Set([3, 4]), inflightIns: [], inflightMarks: [],
  });
  // Twin + beyond-cut ins x=10 under A (hand): birth A x B, live A x; both
  // marks resolve to {A,x} (end B dead scans left -> x; growth crosses
  // nothing settled in (3,4)); remove(4) wins everywhere: ALL PLAIN.
  const twin = peritext.apply(barrier, ins(10, 'x', 1));
  assert.deepEqual(flags(twin, 'bold'), [['A', false], ['x', false]], 'twin (hand: all plain)');

  const g = compactPeritext(barrier, cut());
  assert.equal(g.stats.markPairsDropped, 1, 'the guarded drop fires');
  assert.equal(g.state.marks.size, 0, 'both mark records gone');
  assert.equal(g.state.text.shadow.has(2), false, 'the retention root B is FREED');
  assert.equal(g.stats.recordsDropped, 1);
  const s = peritext.apply(g.state, ins(10, 'x', 1));
  assert.equal(eq(peritext.read(s)), eq(peritext.read(twin)), 'reads identical');

  // Contrast companion: plain retention (pairDrop off) must RETAIN B --
  // the root is freed only by the pair-drop.
  const a = compactPeritext(barrier, cut(), { pairDrop: false });
  assert.equal(a.stats.markPairsDropped, 0);
  assert.equal(a.state.text.shadow.has(2), true, 'plain H-A retains the root');
  assert.equal(a.stats.retainedForMarks, 1);
});

// ------------- D7 beta FAIL companion (c): settled char in the growth window
test('A3 beta: a settled char inside (add.mid, remove.mid) -- unguarded FLIPS, guard refuses', () => {
  // add bold mid 3 [A..B], char w=4 child of B (settled, live), remove
  // bold mid 5 [A..B]. Twin (hand): the add's end-growth grabs w (4 > 3)
  // but the remove's does not (4 < 5), so w is BOLD, A and B plain (the
  // remove wins on them).
  const barrier = build([ins(1, 'A', null), ins(2, 'B', 1),
    mark(3, 'bold', 1, 2, 'before', 'after'), ins(4, 'w', 2),
    unmark(5, 'bold', 1, 2, 'before', 'after')]);
  const cut = () => ({
    settledIds: new Set([1, 2, 4]), settledDelIds: new Set(),
    settledMarkMids: new Set([3, 5]), inflightIns: [], inflightMarks: [],
  });
  assert.deepEqual(flags(barrier, 'bold'),
    [['A', false], ['B', false], ['w', true]], 'twin (hand: w bold)');

  // FAIL: the unguarded drop erases the pair and w goes plain. FLIP.
  const u = compactPeritext(barrier, cut(), { unguardedPairDrop: true });
  assert.equal(u.stats.markPairsDropped, 1, 'the unguarded drop fires');
  assert.deepEqual(flags(u.state, 'bold'),
    [['A', false], ['B', false], ['w', false]], 'hand: FLIP -- w lost its bold');
  assert.notDeepEqual(flags(u.state, 'bold'), flags(barrier, 'bold'));

  // PASS: the window guard sees id 4 strictly inside (3, 5) and refuses.
  const g = compactPeritext(barrier, cut());
  assert.equal(g.stats.markPairsDropped, 0, 'guard refuses the drop');
  assert.deepEqual(flags(g.state, 'bold'), flags(barrier, 'bold'), 'reads identical');
});

// ---------- D7 alpha FAIL companion (b): undeclared straggler add in the window
test('A3 alpha: an undeclared in-flight add between the mids -- drop FLIPS, declaring it refuses', () => {
  // add bold mid 3 [A..B], remove bold mid 6 [A..B]; a concurrent add mid 4
  // over the same span is STILL IN FLIGHT at the cut. Twin (hand): after
  // delivery remove(6) beats both adds: ALL PLAIN.
  const barrier = build([ins(1, 'A', null), ins(2, 'B', 1),
    mark(3, 'bold', 1, 2, 'before', 'after'),
    unmark(6, 'bold', 1, 2, 'before', 'after')]);
  const straggler = mark(4, 'bold', 1, 2, 'before', 'after');
  const twin = peritext.apply(barrier, straggler);
  assert.deepEqual(flags(twin, 'bold'), [['A', false], ['B', false]], 'twin (hand: all plain)');
  const cut = (declared) => ({
    settledIds: new Set([1, 2]), settledDelIds: new Set(),
    settledMarkMids: new Set([3, 6]), inflightIns: [],
    inflightMarks: declared,
  });

  // FAIL: with the straggler UNDECLARED the guards see nothing wrong and
  // the pair drops; after delivery the straggler add(4) is unopposed. FLIP.
  const u = compactPeritext(barrier, cut([]));
  assert.equal(u.stats.markPairsDropped, 1, 'the drop fires without the declaration');
  const us = peritext.apply(u.state, straggler);
  assert.deepEqual(flags(us, 'bold'), [['A', true], ['B', true]], 'hand: FLIP -- resurrected add');
  assert.notDeepEqual(flags(us, 'bold'), flags(twin, 'bold'));

  // PASS: declaring the in-flight mark (mid 4 < 6, same mtype) makes the
  // guard refuse; after delivery reads are twin-identical.
  const d = compactPeritext(barrier,
    cut([{ mid: 4, mtype: 'bold', startId: 1, endId: 2, startSide: 'before', endSide: 'after' }]));
  assert.equal(d.stats.markPairsDropped, 0, 'declared: guard refuses');
  const ds = peritext.apply(d.state, straggler);
  assert.deepEqual(flags(ds, 'bold'), flags(twin, 'bold'), 'reads identical');
});

// =========================================================================
// THE CERTIFIED FIRE: DistributedReplica + compactiblePeritext. The same
// refuse-then-fire discipline as embedRGA -- refuse without the
// certificate, fire with it, reads identical to the never-compacted twin,
// wire catch-up across the compaction commit, and continued editing (with
// a NEW mark anchored on the retained dead record) in the new epoch.
// =========================================================================
test('compactiblePeritext certified GC: refuse-then-fire, reads identical, epoch continues', () => {
  const a = new DistributedReplica(compactiblePeritext, 'A');
  const b = new DistributedReplica(compactiblePeritext, 'B');
  a.register('B'); b.register('A');
  a.commit(ins(1, 'a', null)); a.commit(ins(2, 'b', 1)); a.commit(ins(3, 'c', 2));
  a.commit(mark(10, 'bold', 1, 2, 'before', 'after'));
  a.commit(del(2)); a.commit(del(3));

  // REFUSE: no certificate yet (never heard from B).
  const r0 = a.compactStable();
  assert.equal(r0.compacted, false, 'refuses without the certificate');
  assert.deepEqual(r0.missing, ['B']);
  syncReplicas(a, b);
  assert.equal(a.compactStable().compacted, false, 'still refuses: B authored nothing A absorbed');

  b.commit(ins(20, 'z', 1));
  syncReplicas(a, b); // NOW A has heard from B: everything is settled
  // Twin read (hand): birth a z b c (z delta 19 beats b delta 1), live a z;
  // mark 10's end b is dead, scans left -> z: covered {a,z}, both bold.
  assert.deepEqual(flags(a.head.state, 'bold'), [['a', true], ['z', true]], 'hand: a,z bold');
  const before = eq(a.read());

  // FIRE: c (settled-dead, unreferenced) drops; b (dead END anchor of mark
  // 10) is retained, re-coded, and stays listed in deleted.
  const r1 = a.compactStable();
  assert.equal(r1.compacted, true, 'peritext compaction FIRES');
  assert.equal(r1.stats.recordsDropped, 1, 'c dropped');
  assert.equal(r1.stats.retainedForMarks, 1, 'b retained for mark 10');
  assert.equal(a.epoch, 1, 'a new epoch opened');
  assert.equal(eq(a.read()), before, 'reads identical across the fire');
  assert.equal(a.head.state.text.shadow.has(3), false);
  assert.equal(a.head.state.text.shadow.has(2), true);
  assert.equal(a.head.state.text.deleted.has(2), true, 'retained dead anchor stays in deleted');

  // Idempotence: nothing more to compact at the same cut.
  const r2 = a.compactStable();
  assert.equal(r2.compacted, false);
  assert.match(r2.reason, /nothing to compact/);

  // WIRE: B and a fresh replica C catch up ACROSS the compaction commit
  // (inline encodeState/decodeState, SHA content-address gate).
  syncReplicas(a, b);
  assert.equal(b.epoch, 1);
  assert.equal(eq(b.read()), before, 'B reads identical after adopting the epoch');
  const c = new DistributedReplica(compactiblePeritext, 'C');
  c.ingest(a.delta(c.ancestryGids()));
  c.mergeWithGid(a.headGid);
  assert.equal(eq(c.read()), before, 'a fresh replica catches up across the compaction');

  // EPOCH CONTINUES: new text + a NEW mark whose end anchors on the
  // RETAINED dead record 2 -- it must resolve exactly as on a
  // never-compacted twin (built op-for-op, c included).
  b.commit(ins(30, 'w', 20));
  b.commit(mark(40, 'ital', 1, 2, 'before', 'after'));
  syncReplicas(a, b);
  assert.equal(eq(a.read()), eq(b.read()), 'post-epoch editing converges');
  const twin = build([ins(1, 'a', null), ins(2, 'b', 1), ins(3, 'c', 2),
    mark(10, 'bold', 1, 2, 'before', 'after'), del(2), del(3),
    ins(20, 'z', 1), ins(30, 'w', 20), mark(40, 'ital', 1, 2, 'before', 'after')]);
  // Hand: live a z w; ital 40's end (dead b) scans left -> w: covered all.
  assert.deepEqual(flags(twin, 'ital'), [['a', true], ['z', true], ['w', true]], 'twin (hand)');
  assert.equal(eq(a.read()), eq(peritext.read(twin)),
    'a NEW mark on the retained dead anchor reads as the never-compacted twin');
});

test('empty document audit: state metadata returns to zero; quiescent epoch history remains gated', () => {
  const a = new DistributedReplica(compactiblePeritext, 'A');
  const b = new DistributedReplica(compactiblePeritext, 'B');
  a.register('B'); b.register('A');

  // Make one birth and its delete causally stable at A. B's final authored
  // delete is state-idempotent but proves that B absorbed A's delete.
  a.commit(ins(1, 'x', null));
  syncReplicas(a, b);
  a.commit(del(1));
  syncReplicas(a, b);
  b.commit(del(1));
  syncReplicas(a, b);

  assert.deepEqual(a.read(), [], 'the client document is empty before GC');
  const compacted = a.compactStable();
  assert.equal(compacted.compacted, true);
  assert.equal(compacted.stats.recordsBefore, 1);
  assert.equal(compacted.stats.recordsAfter, 0);
  assert.equal(compacted.stats.markRecords, 0);
  assert.equal(a.head.state.text.shadow.size, 0, 'no character records remain');
  assert.equal(a.head.state.text.deleted.size, 0, 'no character tombstones remain');
  assert.equal(a.head.state.marks.size, 0, 'no mark records remain');
  assert.equal(a.symbolCount(), 0, 'no coordinate symbols remain');

  const empty = new DistributedReplica(compactiblePeritext, 'E');
  assert.equal(a.saveBytes(), empty.saveBytes(),
    'durable datatype metadata has the same constant size as a fresh empty document');

  // FAIL/liveness boundary: B has not yet advertised an authored commit in
  // A's new epoch. Exact history forgetting must refuse rather than assume an
  // acknowledgement from a quiescent peer.
  assert.equal(a.acknowledgeFetch('B', 'forged-head', a.epochKey), false,
    'a receipt not bound to a locally verified head is rejected');
  const history = a.pruneToEpochBase();
  assert.equal(history.pruned, 0);
  assert.match(history.reason, /evidence from B has not reached the compaction cut/);

  // PASS/liveness companion: an ordinary fetch/head-sync round advertises B's
  // verified current head. No fake Peritext operation is needed.
  syncReplicas(a, b);
  const acknowledged = a.pruneToEpochBase();
  assert.ok(acknowledged.pruned > 0, 'history reaches the epoch base after B acknowledges the cut');
  assert.equal(a.dag.size, 1, 'the empty document retains one constant-size epoch base');
});

test('certified fire waits for the DELETE to settle, not just the insert', () => {
  const a = new DistributedReplica(compactiblePeritext, 'A');
  const b = new DistributedReplica(compactiblePeritext, 'B');
  a.register('B'); b.register('A');
  a.commit(ins(1, 'a', null)); a.commit(ins(2, 'b', 1));
  syncReplicas(a, b);
  b.commit(ins(3, 'c', 1));
  syncReplicas(a, b);
  a.commit(del(2)); // the delete is NOT yet witnessed by B's evidence commit
  const r = a.compactStable();
  assert.equal(r.compacted, false, 'an unsettled delete cannot free its record');
  assert.match(r.reason, /nothing to compact/);
  assert.equal(a.head.state.text.shadow.has(2), true, 'record 2 kept while the delete propagates');

  syncReplicas(a, b);          // B hears the delete...
  b.commit(ins(4, 'd', 3));    // ...and authors evidence witnessing it
  syncReplicas(a, b);
  assert.deepEqual(order(a.head.state), ['a', 'c', 'd'], 'hand: live a c d');
  const before = eq(a.read());
  const r2 = a.compactStable();
  assert.equal(r2.compacted, true);
  assert.equal(r2.stats.recordsDropped, 1);
  assert.equal(a.head.state.text.shadow.has(2), false, 'freed once the delete is settled');
  assert.equal(eq(a.read()), before, 'reads identical');
});

test('shared Peritext direct GC preserves retention roots and frozen insert order', () => {
  const p = compactibleSharedPeritext;
  const ops = [ins(1, 'A', null), ins(3, 'x', 1), ins(10, 'C', 1),
    mark(20, 'bold', 1, 3, 'before', 'after'), del(3)];
  const barrier = ops.reduce((s, op) => p.apply(s, op), p.init());
  const twin = p.apply(barrier, ins(6, 's', 1));
  const cut = {
    settledIds: new Set([1, 3, 10]), settledDelIds: new Set([3]),
    settledMarkMids: new Set([20]), inflightIns: [{ id: 6, anchorId: 1 }],
    inflightMarks: [],
  };
  const g = compactSharedPeritext(barrier, cut);
  assert.equal(g.state.text.shadow.has(3), true, 'dead mark boundary is retained');
  assert.ok(g.stats.groupsSkippedInflight >= 1, 'in-flight anchor freezes its sibling group');
  const continued = p.apply(g.state, ins(6, 's', 1));
  assert.deepEqual(p.read(continued), p.read(twin));
});

test('shared Peritext certified GC empties state and survives snapshot recovery', () => {
  const a = new DistributedReplica(compactibleSharedPeritext, 'A');
  const b = new DistributedReplica(compactibleSharedPeritext, 'B');
  a.register('B'); b.register('A');
  a.commit(ins(1, 'x', null)); syncReplicas(a, b);
  a.commit(del(1)); syncReplicas(a, b);
  b.commit(del(1)); syncReplicas(a, b);
  const g = a.compactStable();
  assert.equal(g.compacted, true);
  assert.deepEqual(a.read(), []);
  assert.equal(a.symbolCount(), 0);
  const restored = compactibleSharedPeritext.decodeState(
    compactibleSharedPeritext.encodeState(a.head.state));
  assert.deepEqual(compactibleSharedPeritext.read(restored), []);
  assert.equal(compactibleSharedPeritext.saveBytes(restored),
    compactibleSharedPeritext.saveBytes(compactibleSharedPeritext.init()));
});

test('sided Peritext policy GC retains dead mark boundaries', () => {
  const p = compactibleSidedPeritext;
  let s = p.init();
  for (const op of [ins(1, 'A', null), ins(3, 'x', 1),
    mark(20, 'bold', 1, 3), del(3)]) s = p.apply(s, op);
  const before = p.read(s);
  const g = compactSidedPeritext(s, {
    settledIds: new Set([1, 3]), settledDelIds: new Set([3]),
    settledMarkMids: new Set([20]), inflightIns: [], inflightMarks: [],
  });
  assert.equal(g.state.text.shadow.records.has(3), true,
    'dead mark endpoint remains a policy/position node');
  assert.deepEqual(p.read(g.state), before);
});

test('LiveGap Peritext removes the dead record but retains anonymous root policy geometry', () => {
  const p = compactibleSidedPeritext;
  const a = new DistributedReplica(p, 'A'), b = new DistributedReplica(p, 'B');
  a.register('B'); b.register('A');
  a.commit(ins(1, 'x', null)); syncReplicas(a, b);
  a.commit(del(1)); syncReplicas(a, b);
  b.commit(del(1)); syncReplicas(a, b);
  const g = a.compactStable();
  assert.equal(g.compacted, true);
  assert.deepEqual(a.read(), []);
  assert.equal(a.head.state.text.shadow.records.size, 0,
    'the deleted identity-bearing record is gone');
  assert.equal(a.symbolCount(), 1, 'the anonymous root successor chain survives');
  const restored = p.decodeState(p.encodeState(a.head.state));
  assert.deepEqual(p.read(restored), []);
  const continued = p.apply(restored, ins(2, 'y', null));
  assert.deepEqual(p.read(continued).map((x) => x.char), ['y']);
});

// =========================================================================
// TWIN PBT (the harness's randomized DAG PBT, transliterated to the
// datatype level): multi-replica histories of text + mark ops (dead-anchor
// marks included), a full-exchange barrier as the settled cut, compaction
// on the subject only, continuations + merges + declared-straggler
// deliveries, MULTI-EPOCH (1..3 successive cuts). The subject is compared
// to the never-compacted control twin at EVERY version on two levels:
// text structure (subject birth order == control birth order filtered to
// the subject's records -- fatal always) and the full render (fatal for
// the guarded subject; counted as flip evidence for the NONE control).
// =========================================================================
function pbtTrial(seed, mode, res) {
  const rng = mulberry32(seed);
  const nrep = 2 + (seed % 2);
  const nepoch = 1 + (seed % 3);
  let g0 = peritext.init();
  g0 = peritext.apply(g0, ins(1, 'p', null));
  g0 = peritext.apply(g0, ins(2, 'q', 1));
  let nid = 2;
  const fresh = () => ++nid;
  const L0 = peritext.init();
  let subj = Array.from({ length: nrep }, () => g0);
  let ctrl = Array.from({ length: nrep }, () => g0);
  let diverged = false;
  const rv = (s) => eq(peritext.read(s));

  const compare = (i, where) => {
    const sb = birthIds(subj[i]);
    const cb = birthIds(ctrl[i]).filter((x) => subj[i].text.shadow.has(x));
    assert.deepEqual(sb, cb, `TEXT-ORDER ${where} seed=${seed} r${i}`);
    if (rv(subj[i]) !== rv(ctrl[i])) {
      if (mode === 'guarded') {
        assert.fail(`READ-DIVERGENCE ${where} seed=${seed} r${i}\n` +
          ` subj=${rv(subj[i])}\n ctrl=${rv(ctrl[i])}`);
      }
      diverged = true;
    }
  };
  const applyBoth = (i, op) => {
    subj[i] = peritext.apply(subj[i], op);
    ctrl[i] = peritext.apply(ctrl[i], op);
  };
  const randMarkOp = (i, isAdd) => {
    const birth = birthIds(subj[i]); // dead anchors allowed (the point)
    const i0 = Math.floor(rng() * birth.length);
    const j0 = i0 + Math.floor(rng() * (birth.length - i0));
    const mk = isAdd ? mark : unmark;
    applyBoth(i, mk(fresh(), rng() < 0.5 ? 'bold' : 'ital', birth[i0], birth[j0],
      rng() < 0.5 ? 'before' : 'after', rng() < 0.5 ? 'after' : 'before'));
  };
  const randOp = (i) => {
    const r = rng();
    const live = liveIds(subj[i]);
    if (r < 0.45 || live.length === 0) {
      const x = fresh();
      applyBoth(i, ins(x, String.fromCharCode(97 + (x % 26)), pick(rng, [null, ...live])));
    } else if (r < 0.65) {
      applyBoth(i, del(pick(rng, live)));
    } else {
      const isAdd = rng() < 0.7;
      // a remove often reuses a visible add's exact boundaries+sides (the
      // pair shape A3 needs); the template must be present in the subject
      // (i.e. not already pair-dropped).
      const templates = [...subj[i].marks.values()].filter((m) => !m.removed
        && subj[i].text.shadow.has(m.startId) && subj[i].text.shadow.has(m.endId));
      if (!isAdd && templates.length > 0 && rng() < 0.7) {
        const t = pick(rng, templates);
        applyBoth(i, unmark(fresh(), t.mtype, t.startId, t.endId, t.startSide, t.endSide));
      } else randMarkOp(i, isAdd);
    }
  };
  const maybeMerge = (i) => {
    if (nrep > 1 && rng() < 0.30) {
      const j = (i + 1 + Math.floor(rng() * (nrep - 1))) % nrep;
      subj[j] = peritext.merge3(L0, subj[j], subj[i]);
      ctrl[j] = peritext.merge3(L0, ctrl[j], ctrl[i]);
      compare(j, 'post-merge');
    }
  };

  for (let epoch = 0; epoch < nepoch; epoch++) {
    const nops = 4 + Math.floor(rng() * 7);
    for (let k = 0; k < nops; k++) {
      const i = Math.floor(rng() * nrep);
      randOp(i);
      compare(i, `e${epoch}-local`);
      maybeMerge(i);
    }
    // --- mint declared stragglers (applied NOWHERE yet)
    const pendIns = [], pendMarks = [];
    if (rng() < 0.55) {
      const r0 = Math.floor(rng() * nrep);
      const npend = 1 + Math.floor(rng() * 2);
      for (let k = 0; k < npend; k++) {
        pendIns.push({ id: fresh(), el: '*', anchorId: pick(rng, [null, ...liveIds(subj[r0])]) });
      }
      if (mode === 'guarded' && rng() < 0.6) {
        const birth = birthIds(subj[r0]);
        const i0 = Math.floor(rng() * birth.length);
        const j0 = i0 + Math.floor(rng() * (birth.length - i0));
        pendMarks.push({ mid: fresh(), mtype: rng() < 0.5 ? 'bold' : 'ital',
          removed: rng() >= 0.7, startId: birth[i0], endId: birth[j0],
          startSide: rng() < 0.5 ? 'before' : 'after',
          endSide: rng() < 0.5 ? 'after' : 'before' });
      }
      res.stragglerCuts++;
    }
    // --- barrier: full exchange = the settled-cut certificate
    let Bs = subj[0], Bc = ctrl[0];
    for (let i = 1; i < nrep; i++) {
      Bs = peritext.merge3(L0, Bs, subj[i]);
      Bc = peritext.merge3(L0, Bc, ctrl[i]);
    }
    ctrl = Array.from({ length: nrep }, () => Bc);
    const cut = {
      settledIds: new Set(birthIds(Bs)),
      settledDelIds: new Set([...Bs.text.deleted]),
      settledMarkMids: new Set([...Bs.marks.values()].map((m) => m.mid)),
      inflightIns: pendIns.map(({ id, anchorId }) => ({ id, anchorId })),
      inflightMarks: pendMarks,
    };
    const { state: cst, stats } = compactPeritext(Bs, cut,
      mode === 'none' ? { noRetention: true } : {});
    subj = Array.from({ length: nrep }, () => cst);
    res.cuts++;
    res.dead += stats.settledDead;
    res.dropped += stats.recordsDropped;
    res.pairsDropped += stats.markPairsDropped;
    res.retainedForMarks += stats.retainedForMarks;
    res.markRecords += stats.markRecords;
    if (stats.markRecords > 0) {
      res.maxPerMark = Math.max(res.maxPerMark, stats.retainedForMarks / stats.markRecords);
      assert.ok(stats.retainedForMarks <= 2 * stats.markRecords,
        `cost claim violated seed=${seed}: ${stats.retainedForMarks} > 2x${stats.markRecords}`);
    }
    for (let i = 0; i < nrep; i++) compare(i, `e${epoch}-post-compaction`);
    // --- continuation: random ops + merges + straggler deliveries
    const deliveries = [];
    for (const p of pendIns) for (let i = 0; i < nrep; i++) deliveries.push(['ins', p, i]);
    for (const m of pendMarks) for (let i = 0; i < nrep; i++) deliveries.push(['mark', m, i]);
    for (let k = deliveries.length - 1; k > 0; k--) {
      const j = Math.floor(rng() * (k + 1));
      [deliveries[k], deliveries[j]] = [deliveries[j], deliveries[k]];
    }
    const deliver = ([kind, p, i]) => {
      if (kind === 'ins') { // may already be present via a merge
        if (!subj[i].text.shadow.has(p.id)) subj[i] = peritext.apply(subj[i], ins(p.id, p.el, p.anchorId));
        if (!ctrl[i].text.shadow.has(p.id)) ctrl[i] = peritext.apply(ctrl[i], ins(p.id, p.el, p.anchorId));
      } else {
        const mk = p.removed ? unmark : mark;
        applyBoth(i, mk(p.mid, p.mtype, p.startId, p.endId, p.startSide, p.endSide));
      }
      compare(i, `e${epoch}-delivery`);
    };
    const ncont = 4 + Math.floor(rng() * 7) + deliveries.length;
    for (let k = 0; k < ncont; k++) {
      if (deliveries.length > 0 && rng() < 0.5) deliver(deliveries.pop());
      else {
        const i = Math.floor(rng() * nrep);
        randOp(i);
        compare(i, `e${epoch}-continuation`);
        maybeMerge(i);
      }
    }
    while (deliveries.length > 0) deliver(deliveries.pop());
  }
  // --- end of trial: subject replicas must agree among themselves
  let F = subj[0];
  for (let i = 1; i < nrep; i++) F = peritext.merge3(L0, F, subj[i]);
  for (let i = 0; i < nrep; i++) {
    assert.equal(rv(peritext.merge3(L0, subj[i], F)), rv(F),
      `SUBJECT-CONVERGENCE seed=${seed} r${i}`);
  }
  if (diverged) res.divTrials++;
  res.trials++;
}

const freshRes = () => ({ trials: 0, cuts: 0, stragglerCuts: 0, divTrials: 0,
  dead: 0, dropped: 0, pairsDropped: 0, retainedForMarks: 0, markRecords: 0,
  maxPerMark: 0 });

test('twin PBT: guarded marks GC == never-compacted twin at every version, multi-epoch', (t) => {
  const res = freshRes();
  for (let e = 0; e < 150; e++) pbtTrial(1000003 * 7 + e, 'guarded', res);
  t.diagnostic(`guarded: ${res.trials} trials, ${res.cuts} cuts ` +
    `(${res.stragglerCuts} with declared stragglers), ` +
    `${res.dropped}/${res.dead} settled-dead records dropped, ` +
    `${res.pairsDropped} guarded pair-drops, ` +
    `retained-for-marks ${res.retainedForMarks} over ${res.markRecords} mark records ` +
    `(per-cut max ${res.maxPerMark.toFixed(3)}, claim bound 2)`);
  assert.equal(res.trials, 150, 'no trial diverged from the twin');
  assert.equal(res.divTrials, 0);
  assert.ok(res.cuts >= 300, 'multi-epoch: 2 cuts per trial on average');
  assert.ok(res.stragglerCuts > 0, 'straggler cuts exercised');
  assert.ok(res.dropped > 0, 'the GC genuinely bites');
  assert.ok(res.pairsDropped > 0, 'A3 non-vacuity: guarded pair-drops fired');
  assert.ok(res.maxPerMark <= 2, 'cost claim: retained dead records <= 2 per mark record');
});

test('twin PBT FAIL companion: the NONE control (no retention) flips reads', (t) => {
  const res = freshRes();
  for (let e = 0; e < 60; e++) pbtTrial(7919 * 13 + e, 'none', res);
  t.diagnostic(`NONE: ${res.trials} trials, ${res.cuts} cuts, ` +
    `${res.divTrials} trials flipped vs the twin`);
  assert.equal(res.trials, 60, 'text structure stays sound even without retention');
  assert.ok(res.divTrials > 0,
    'no-retention compaction must flip reads');
});
