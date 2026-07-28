// PERITEXT datatype tests: the verified DOCUMENT-ORDER mark read model as a
// runtime datatype, and THE PARAMETRICITY PAYOFF -- rich text carried by the
// general DistributedReplica with no Peritext-specific runtime code.
//
// FIXTURE PROVENANCE. Every expected value below is EXTRACTED from the
// validated reference model whiteboard/litmus/peritext_read_model.py (which
// passes end to end), via the harness scratchpad/extract_fixtures.py, run as:
//     cd whiteboard/litmus && \
//       PYTHONPATH=whiteboard/litmus python3 .../extract_fixtures.py
// The values are hand-transcribed from that JSON dump -- NOT read back from the
// JS implementation under test (no self-oracle). Python anchor 0 = JS anchorId
// null (document start). Each PASS carries a FAIL companion pinning the
// tempting degenerate reading (a leak, a constant read, an atomic delete).

import test from 'node:test';
import assert from 'node:assert/strict';
import { peritext } from '../src/datatypes/peritext.js';
import { DistributedReplica, syncReplicas } from '../src/replica.js';

const build = (ops) => ops.reduce((s, op) => peritext.apply(s, op), peritext.init());
const ins = (id, el, anchorId) => ({ type: 'ins', id, el, anchorId });
const del = (id) => ({ type: 'del', id });
const mark = (mid, mtype, startId, endId, startSide = 'before', endSide = 'after', extra = {}) =>
  ({ type: 'addMark', mid, mtype, startId, endId, startSide, endSide, ...extra });
const unmark = (mid, mtype, startId, endId, startSide = 'before', endSide = 'after') =>
  ({ type: 'removeMark', mid, mtype, startId, endId, startSide, endSide });
const order = (s) => peritext.read(s).map((e) => e.char);
const flags = (s, mt) => peritext.flags(s, mt);
const eq = (x) => JSON.stringify(x);

// --------------------------------------------------------- Ex1-8
test('Ex1 insert-within-span: b typed inside [a,c] is bold (reading order a,b,c)', () => {
  const s = build([ins(1, 'a', null), ins(2, 'c', 1),
    mark(3, 'bold', 1, 2), ins(4, 'b', 1)]);
  assert.equal(order(s).join(''), 'abc', 'embedRGA reading order = Python live order');
  assert.deepEqual(flags(s, 'bold'), [['a', true], ['b', true], ['c', true]]);
  // FAIL companion: the inserted b is NOT left plain.
  assert.notDeepEqual(flags(s, 'bold'), [['a', true], ['b', false], ['c', true]]);
});

test('Ex2 overlapping bold[a,c] + italic[b,d]: the overlap carries both', () => {
  const s = build([ins(1, 'a', null), ins(2, 'b', 1), ins(3, 'c', 2), ins(4, 'd', 3),
    mark(10, 'bold', 1, 3), mark(11, 'italic', 2, 4)]);
  assert.equal(order(s).join(''), 'abcd');
  assert.deepEqual(flags(s, 'bold'), [['a', true], ['b', true], ['c', true], ['d', false]]);
  assert.deepEqual(flags(s, 'italic'), [['a', false], ['b', true], ['c', true], ['d', true]]);
  // FAIL companion: the overlap b,c does NOT carry bold only (marks genuinely coexist).
  assert.notDeepEqual(flags(s, 'italic'), [['a', false], ['b', false], ['c', false], ['d', true]]);
});

test('Ex3 delete-whole-span-then-reinsert: fresh text is plain (span collapses)', () => {
  const s = build([ins(1, 'a', null), ins(2, 'b', 1), ins(3, 'c', 2),
    mark(10, 'bold', 1, 3), del(1), del(2), del(3), ins(4, 'd', null)]);
  assert.equal(order(s).join(''), 'd', 'only the reinserted d is live');
  assert.deepEqual(flags(s, 'bold'), [['d', false]]);
  // FAIL companion: the collapsed span does NOT leak bold onto fresh d.
  assert.notDeepEqual(flags(s, 'bold'), [['d', true]]);
});

test('Ex5 concurrent add vs removeMark: LWW by mid, and it discriminates', () => {
  const removeWins = build([ins(1, 'a', null), ins(2, 'b', 1),
    mark(10, 'bold', 1, 2), unmark(20, 'bold', 1, 2)]);
  const addWins = build([ins(1, 'a', null), ins(2, 'b', 1),
    mark(20, 'bold', 1, 2), unmark(10, 'bold', 1, 2)]);
  assert.deepEqual(flags(removeWins, 'bold'), [['a', false], ['b', false]], 'higher-mid remove wins');
  assert.deepEqual(flags(addWins, 'bold'), [['a', true], ['b', true]], 'higher-mid add wins');
  // FAIL companion: LWW is not a constant read -- swapping which is higher flips the verdict.
  assert.notEqual(eq(flags(removeWins, 'bold')), eq(flags(addWins, 'bold')));
});

test('Ex7 bold end-side grows over a newer insert; an older insert is not grabbed', () => {
  const expand = build([ins(1, 'a', null), ins(2, 'b', 1), mark(3, 'bold', 1, 2), ins(4, 'x', 2)]);
  const older = build([ins(1, 'a', null), ins(2, 'b', 1), mark(9, 'bold', 1, 2), ins(4, 'x', 2)]);
  assert.equal(order(expand).join(''), 'abx');
  assert.deepEqual(flags(expand, 'bold'), [['a', true], ['b', true], ['x', true]], 'x newer than mark: grabbed');
  assert.deepEqual(flags(older, 'bold'), [['a', true], ['b', true], ['x', false]], 'x older than mark: not grabbed');
  // FAIL companion: growth is directed, not constant -- the two reads differ on x.
  assert.notEqual(eq(flags(expand, 'bold')), eq(flags(older, 'bold')));
});

test('Ex8 gravity contrast: a link does NOT grow over x, bold on the same insert DOES', () => {
  const linkDoc = build([ins(1, 'a', null), ins(2, 'b', 1), ins(3, 'z', 2),
    mark(4, 'link', 1, 3, 'before', 'before', { value: 'http://x' }), ins(5, 'x', 2)]);
  const boldDoc = build([ins(1, 'a', null), ins(2, 'b', 1), ins(3, 'z', 2),
    mark(4, 'bold', 1, 2, 'before', 'after'), ins(5, 'x', 2)]);
  assert.equal(order(linkDoc).join(''), 'abxz', 'reading order a,b,x,z');
  assert.deepEqual(flags(linkDoc, 'link'), [['a', true], ['b', true], ['x', false], ['z', false]]);
  assert.deepEqual(flags(boldDoc, 'bold'), [['a', true], ['b', true], ['x', true], ['z', false]]);
  // FAIL companion: the two gravities are not the same -- link and bold differ on x.
  assert.notEqual(eq(flags(linkDoc, 'link')), eq(flags(boldDoc, 'bold')));
});

// ------------------------------------------------- doc_no_backward_leak (directed)
test('doc_no_backward_leak: deleting a bold START anchor rehomes forward, W stays plain', () => {
  // Chain W,A,B,C; bold[A,B]; delete the start anchor A. Doc-order rehomes the
  // start to the nearest survivor to the RIGHT (B); W (earlier) is untouched.
  const s = build([ins(1, 'W', null), ins(2, 'A', 1), ins(3, 'B', 2), ins(4, 'C', 3),
    mark(100, 'bold', 2, 3), del(2)]);
  assert.equal(order(s).join(''), 'WBC', 'A deleted, survivors W,B,C');
  assert.deepEqual(flags(s, 'bold'), [['W', false], ['B', true], ['C', false]]);
  // FAIL companion: the boundary does NOT migrate BACKWARD onto W (the tree-ancestry leak).
  assert.notDeepEqual(flags(s, 'bold'), [['W', true], ['B', true], ['C', false]]);
});

// ------------------------------------------------------------- gravity contrast
test('gravity: an inner-before start is stable (no left over-grab); outer sides skip the newer run', () => {
  // W,A,B; insert y between W and A (newer than the marks). Bold start=(A,before)
  // is stable -> y NOT grabbed. Link start=(W,after) skips y, end=(B,before) excludes B -> covers A only.
  const boldDoc = build([ins(1, 'W', null), ins(2, 'A', 1), ins(3, 'B', 2),
    mark(3, 'bold', 2, 3, 'before', 'after'), ins(4, 'y', 1)]);
  const linkDoc = build([ins(1, 'W', null), ins(2, 'A', 1), ins(3, 'B', 2),
    mark(3, 'link', 1, 3, 'after', 'before', { value: 'u' }), ins(4, 'y', 1)]);
  assert.equal(order(boldDoc).join(''), 'WyAB', 'y reads between W and A');
  assert.deepEqual(flags(boldDoc, 'bold'), [['W', false], ['y', false], ['A', true], ['B', true]]);
  assert.deepEqual(flags(linkDoc, 'link'), [['W', false], ['y', false], ['A', true], ['B', false]]);
  // FAIL companion: a 'before' start does NOT grow left onto the newer y.
  assert.notDeepEqual(flags(boldDoc, 'bold'), [['W', false], ['y', true], ['A', true], ['B', true]]);
});

// -------------------------------------------------- doc_delete_can_respan (trilemma)
test('doc_delete_can_respan: deleting a plain separator re-spans an untouched survivor', () => {
  // bold[A,B] endSide=after; C (older than mark) blocks growth; D (newer) plain.
  // Delete the plain C: D becomes contiguous with B and the growth run grabs it,
  // though the delete touched neither D nor any boundary. The honest atomicity price.
  const before = build([ins(1, 'A', null), ins(2, 'B', 1), ins(3, 'C', 2),
    mark(4, 'bold', 1, 2), ins(5, 'D', 3)]);
  const after = peritext.apply(before, del(3));
  assert.deepEqual(flags(before, 'bold'), [['A', true], ['B', true], ['C', false], ['D', false]]);
  assert.deepEqual(flags(after, 'bold'), [['A', true], ['B', true], ['D', true]], 'D re-spanned');
  // FAIL companion: the post-delete read is NOT the pre-delete read minus C
  // (the tombstone/"atomic" answer would keep D plain).
  assert.notDeepEqual(flags(after, 'bold'), [['A', true], ['B', true], ['D', false]]);
});

// ------------------------------------------------------------------ convergence
test('convergence: the render is a pure function of the mark SET (permutation-invariant)', () => {
  const base = [ins(1, 'a', null), ins(2, 'b', 1), ins(3, 'c', 2), ins(4, 'd', 3)];
  const both = build([...base, mark(10, 'bold', 1, 3), mark(11, 'italic', 2, 4)]);
  const swapped = build([...base, mark(11, 'italic', 2, 4), mark(10, 'bold', 1, 3)]);
  assert.equal(eq(peritext.read(both)), eq(peritext.read(swapped)), 'mark order does not change the read');
  // FAIL companion: convergence is not vacuous -- dropping a mark DOES change the read.
  const dropped = build([...base, mark(10, 'bold', 1, 3)]);
  assert.notEqual(eq(peritext.read(both)), eq(peritext.read(dropped)));
});

// =========================================================================
// THE PARAMETRICITY PAYOFF: rich text over the GENERAL DistributedReplica.
// Two replicas concurrently edit text AND marks, gossip via the delta
// protocol, and converge -- with NO Peritext-specific runtime code (the same
// object that carries embedRGA and orset). Plus a clone/catch-up over the wire
// and a snapshot round-trip (the durable-persistence surface).
// =========================================================================
test('DistributedReplica carries Peritext: concurrent text+mark edits gossip and converge', () => {
  const a = new DistributedReplica(peritext, 'A');
  const b = new DistributedReplica(peritext, 'B');
  a.register('B'); b.register('A');

  a.commit(ins(1, 'H', null)); a.commit(ins(2, 'i', 1)); // shared prefix "Hi"
  syncReplicas(a, b);
  assert.equal(eq(a.read()), eq(b.read()), 'both hold "Hi" after the first sync');

  // Concurrent, on divergent heads: A bolds + types '!'; B italicises + types '?' + deletes 'i'.
  a.commit(mark(10, 'bold', 1, 2));
  a.commit(ins(3, '!', 2));
  b.commit(mark(20, 'italic', 1, 2));
  b.commit(ins(4, '?', 2));
  b.commit(del(2));
  syncReplicas(a, b);

  assert.equal(eq(a.read()), eq(b.read()), 'text AND marks converge across the wire');
  const doc = a.read();
  // H survives (bold+italic), i is deleted, and both a '!' and a '?' are present.
  const chars = doc.map((e) => e.char).join('');
  assert.ok(!chars.includes('i'), 'the concurrently deleted i is gone on both');
  assert.ok(chars.includes('!') && chars.includes('?'), 'both concurrent inserts survive');
  const H = doc.find((e) => e.char === 'H');
  assert.deepEqual(H.marks.map((m) => m.mtype).sort(), ['bold', 'italic'], 'H carries BOTH concurrent marks');

  // CLONE + CATCH-UP over the wire: a brand-new replica pulls the whole history
  // as a delta and lands on the identical render (the git-clone surface).
  const c = new DistributedReplica(peritext, 'C');
  c.ingest(a.delta(c.ancestryGids()));
  c.mergeWithGid(a.headGid);
  assert.equal(eq(c.read()), eq(a.read()), 'a fresh replica catches up to the same rich-text render');

  // DURABLE-SNAPSHOT round-trip (what git persistence serializes): encode ->
  // decode reproduces the read exactly.
  const roundTrip = peritext.decodeState(peritext.encodeState(a.head.state));
  assert.equal(eq(peritext.read(roundTrip)), eq(a.read()), 'snapshot encode/decode preserves the render');

  // The PLAIN datatype (no compact/remapState hooks) still refuses state
  // compaction, the orset path. The marks-layer GC that FIRES instead --
  // retention roots + the A3 guarded pair-drop -- is
  // `compactiblePeritext` in src/compact-peritext.js, test/peritext-gc.test.js.
  const r = a.compactStable();
  assert.equal(r.compacted, false, 'plain peritext (hookless) refuses epoch compaction');
  assert.match(r.reason, /does not support state compaction/);
});

test('DistributedReplica Peritext: SHA content-address round-trip and dedup', () => {
  const a = new DistributedReplica(peritext, 'A'), b = new DistributedReplica(peritext, 'B');
  a.commit(ins(1, 'x', null)); a.commit(mark(9, 'bold', 1, 1));
  assert.equal(a.headGid.length, 40, 'commit ids are 40-hex SHA content ids');
  const d = a.delta(b.ancestryGids());
  assert.equal(b.ingest(d), 2, 'B ingests the two commits');
  assert.equal(b.ingest(d), 0, 'idempotent re-ingest (SHA dedup)');
  b.mergeWithGid(a.headGid);
  assert.equal(eq(a.read()), eq(b.read()), 'reads round-trip over the wire');
});

// ------------------------------------------------ comments (unique-mtype encoding)
// COMMENTS: overlapping annotations that must COEXIST, not
// collapse. The read model resolves per (char, mtype) by LWW, so the encoding
// is one mtype PER COMMENT (`comment:<id>`, note text in `value`); distinct
// mtypes never compete. Expected values here are HAND-DERIVED from the same
// per-mtype resolution rules the extracted Ex1-8 fixtures pin (each mtype
// resolves independently, exactly as 'bold' vs 'link' do in Ex8); the FAIL
// companion pins the collapse that makes the naive same-mtype encoding wrong.

const commentMarks = (s) =>
  peritext.read(s).map((e) => [e.char, e.marks.map((m) => `${m.mtype}=${m.value}`).join('|')]);

test('comments: overlapping distinct-mtype comments COEXIST on the overlap', () => {
  const s = build([ins(1, 'a', null), ins(2, 'b', 1), ins(3, 'c', 2), ins(4, 'd', 3),
    mark(10, 'comment:r1', 1, 3, 'before', 'after', { value: 'first note' }),   // a..c
    mark(11, 'comment:r2', 2, 4, 'before', 'after', { value: 'second note' })]); // b..d
  assert.deepEqual(commentMarks(s), [
    ['a', 'comment:r1=first note'],
    ['b', 'comment:r1=first note|comment:r2=second note'],
    ['c', 'comment:r1=first note|comment:r2=second note'],
    ['d', 'comment:r2=second note'],
  ], 'the overlap (b,c) carries BOTH comments, each with its own note');

  // FAIL companion: the NAIVE encoding (both marks share mtype 'comment')
  // collapses -- per (char,'comment') the higher mid wins, so on b,c the first
  // note is LOST. This is exactly why the editor mints one mtype per comment.
  const naive = build([ins(1, 'a', null), ins(2, 'b', 1), ins(3, 'c', 2), ins(4, 'd', 3),
    mark(10, 'comment', 1, 3, 'before', 'after', { value: 'first note' }),
    mark(11, 'comment', 2, 4, 'before', 'after', { value: 'second note' })]);
  const naiveB = peritext.read(naive)[1];
  assert.equal(naiveB.marks.length, 1, 'naive: ONE surviving comment on b');
  assert.equal(naiveB.marks[0].value, 'second note', 'naive: the higher mid clobbers');
  assert.notEqual(eq(commentMarks(naive)), eq(commentMarks(s)),
    'the two encodings genuinely differ');
});

test('comments: removeMark deletes ONE comment by its mtype, the overlap survives', () => {
  const s = build([ins(1, 'a', null), ins(2, 'b', 1), ins(3, 'c', 2), ins(4, 'd', 3),
    mark(10, 'comment:r1', 1, 3, 'before', 'after', { value: 'first note' }),
    mark(11, 'comment:r2', 2, 4, 'before', 'after', { value: 'second note' }),
    unmark(12, 'comment:r1', 1, 3)]);
  assert.deepEqual(commentMarks(s), [
    ['a', ''],
    ['b', 'comment:r2=second note'],
    ['c', 'comment:r2=second note'],
    ['d', 'comment:r2=second note'],
  ], 'r1 is retracted everywhere; r2 is untouched');
  // FAIL companions: removal is targeted (r2 survives), and text is intact.
  assert.ok(peritext.read(s)[3].marks.some((m) => m.mtype === 'comment:r2'),
    'removing r1 did not take r2 with it');
  assert.equal(order(s).join(''), 'abcd', 'removal touches marks, never text');
});
