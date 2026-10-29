/**
 * Hand-derived tests for the Automerge instance's specification and the
 * witness search over it. Every expected value is written out by hand; every
 * block also asserts that a tempting wrong answer is not produced. Run with
 * `node spec-tests.mjs`.
 */
import assert from 'node:assert/strict';
import { initial, apply, applyAll, view, viewWithIds, localEdit, insertedAttrs, anchorsOf, viewsEqual, textSpec } from '../../ra-pbt/instances/automerge/spec.js';
import { findWitness, allFinalViews } from '../../ra-pbt/src/witness.js';

let passed = 0;
function test(name, fn) {
  try {
    fn();
    passed++;
    console.log('ok   ' + name);
  } catch (e) {
    console.log('FAIL ' + name);
    console.log(e);
    process.exitCode = 1;
  }
}

const B = { bold: true };
const ins = (id, ch, origin = null, rightOrigin = null) => ({ kind: 'insert', id, ch, origin, rightOrigin });
const del = (...ids) => ({ kind: 'delete', ids });
const mark = (id, name, value, start, end) => ({ kind: 'mark', id, name, value, start, end });
const markB = (id, name, value, begin, end) => ({ kind: 'mark', id, name, value, begin, end });
const after = (id) => ({ side: 'after', id });
const before = (id) => ({ side: 'before', id });
const fold = (ops) => ops.reduce((s, op) => (s === null ? null : apply(s, op)), initial());
const v = (...pairs) => pairs.map(([ch, attrs]) => ({ ch, attrs: attrs ?? {} }));
const plain = (s) => v(...[...s].map((ch) => [ch]));
const abc = [ins('a', 'a'), ins('b', 'b', 'a'), ins('c', 'c', 'b')];

test('gap rule: every position strictly between origin and right origin', () => {
  // a b c; x after a, before c: positions between a and b, or between b and c.
  const s = fold(abc);
  const out = applyAll(s, ins('x', 'x', 'a', 'c')).map(view);
  assert.deepEqual(out, [plain('axbc'), plain('abxc')]);
  assert.ok(!out.some((w) => viewsEqual(w, plain('xabc'))));
  assert.ok(!out.some((w) => viewsEqual(w, plain('abcx'))));
});

test('insert preconditions: missing origin, duplicate id, right origin before origin', () => {
  const s = fold(abc);
  assert.deepEqual(applyAll(s, ins('x', 'x', 'q')), []);
  assert.deepEqual(applyAll(s, ins('a', 'z')), []);
  assert.deepEqual(applyAll(s, ins('x', 'x', 'c', 'a')), []);
  assert.notDeepEqual(applyAll(s, ins('x', 'x', 'c')), []);
});

test('delete by identity is idempotent; a deleted character still anchors', () => {
  const s = fold([...abc, del('b')]);
  assert.deepEqual(view(s), plain('ac'));
  assert.deepEqual(view(apply(s, del('b'))), plain('ac'));
  assert.notEqual(apply(s, del('b')), null);
  assert.equal(apply(s, del('q')), null);
  // x after the deleted b and before c: a x c, not x a c.
  assert.deepEqual(view(apply(s, ins('x', 'x', 'b', 'c'))), plain('axc'));
  assert.notDeepEqual(view(apply(s, ins('x', 'x', 'b', 'c'))), plain('xac'));
});

test('anchor marks: before/after sides decide coverage of a later insertion at the boundary', () => {
  // bold b with start before b and end before c (expand after): x inserted
  // between b and c is covered; y inserted between a and b is not.
  const s = fold([...abc, mark('m', 'bold', true, before('b'), before('c'))]);
  assert.deepEqual(view(s), v(['a'], ['b', B], ['c']));
  const x = apply(s, ins('x', 'x', 'b', 'c'));
  assert.deepEqual(view(x), v(['a'], ['b', B], ['x', B], ['c']));
  assert.notDeepEqual(view(x), v(['a'], ['b', B], ['x'], ['c']));
  const y = apply(s, ins('y', 'y', 'a', 'b'));
  assert.deepEqual(view(y), v(['a'], ['y'], ['b', B], ['c']));
  assert.notDeepEqual(view(y), v(['a'], ['y', B], ['b', B], ['c']));
});

test('anchor marks: an end of the text anchor covers everything appended later', () => {
  const s = fold([ins('a', 'a'), mark('m', 'bold', true, before('a'), null), ins('z', 'z', 'a')]);
  assert.deepEqual(view(s), v(['a', B], ['z', B]));
  assert.notDeepEqual(view(s), v(['a', B], ['z']));
});

test('marks: the covering mark with the greatest identity wins in either order; null shows nothing', () => {
  // 5@01 bolds a..c, 6@01 unbolds b: b is plain whichever is applied last.
  const s = fold([...abc, mark('5@01', 'bold', true, before('a'), after('c')), mark('6@01', 'bold', null, before('b'), after('b'))]);
  assert.deepEqual(view(s), v(['a', B], ['b'], ['c', B]));
  const t = fold([...abc, mark('6@01', 'bold', null, before('b'), after('b')), mark('5@01', 'bold', true, before('a'), after('c'))]);
  assert.deepEqual(view(t), v(['a', B], ['b'], ['c', B]));
  assert.notDeepEqual(view(t), v(['a', B], ['b', B], ['c', B]));
  // Counter first, then actor: 6@01 beats 5@02, and 6@02 beats 6@01.
  const u = fold([...abc, mark('6@01', 'bold', true, before('b'), after('b')), mark('5@02', 'bold', null, before('b'), after('b'))]);
  assert.deepEqual(view(u), v(['a'], ['b', B], ['c']));
  const w = fold([...abc, mark('6@02', 'bold', null, before('b'), after('b')), mark('6@01', 'bold', true, before('b'), after('b'))]);
  assert.deepEqual(view(w), plain('abc'));
  assert.notDeepEqual(view(w), view(u));
});

test('anchor marks: a missing anchor is a precondition failure', () => {
  assert.equal(apply(fold(abc), mark('m', 'bold', true, before('q'), null)), null);
  assert.notEqual(apply(fold(abc), mark('m', 'bold', true, null, null)), null);
});

test('marker marks: boundaries are list elements under the gap rule', () => {
  // begin in the gap (head, a), end in (c, end): covers a b c; a concurrent
  // z after c may land before or after the end boundary.
  const s = fold([...abc, markB('m', 'bold', true, { id: 'mb', origin: null, rightOrigin: 'a' }, { id: 'me', origin: 'c', rightOrigin: null })]);
  assert.deepEqual(view(s), v(['a', B], ['b', B], ['c', B]));
  const zs = applyAll(s, ins('z', 'z', 'c')).map(view);
  assert.deepEqual(zs, [v(['a', B], ['b', B], ['c', B], ['z', B]), v(['a', B], ['b', B], ['c', B], ['z'])]);
  assert.equal(zs.length, 2);
});

test('anchorsOf follows the expand policy', () => {
  const ids = ['a', 'b', 'c'];
  assert.deepEqual(anchorsOf(ids, 1, 2, 'bold'), { start: before('b'), end: before('c') });
  assert.deepEqual(anchorsOf(ids, 1, 3, 'bold'), { start: before('b'), end: null });
  assert.deepEqual(anchorsOf(ids, 1, 2, 'italic'), { start: after('a'), end: after('b') });
  assert.deepEqual(anchorsOf(ids, 0, 2, 'italic'), { start: null, end: after('b') });
  assert.deepEqual(anchorsOf(ids, 1, 2, 'link'), { start: before('b'), end: after('b') });
  assert.notDeepEqual(anchorsOf(ids, 1, 2, 'link'), anchorsOf(ids, 1, 2, 'bold'));
});

test('insertedAttrs: after takes the left, before the right, none the shared value', () => {
  const l = { attrs: { bold: true, italic: true, link: 'u1' } };
  const r = { attrs: { link: 'u1' } };
  assert.deepEqual(insertedAttrs(l, r), { bold: true, link: 'u1' });
  assert.notDeepEqual(insertedAttrs(l, r), { bold: true, italic: true, link: 'u1' });
  assert.deepEqual(insertedAttrs({ attrs: { link: 'u1' } }, { attrs: { link: 'u2' } }), {});
  assert.deepEqual(insertedAttrs(null, { attrs: { italic: true, bold: true } }), { italic: true });
});

test('localEdit: insert inherits by policy then takes its own attributes; format marks exactly its range', () => {
  const view0 = v(['a', B], ['b']);
  assert.deepEqual(localEdit(view0, { kind: 'insert', index: 1, text: 'xy', attrs: {} }), v(['a', B], ['x', B], ['y', B], ['b']));
  assert.notDeepEqual(localEdit(view0, { kind: 'insert', index: 1, text: 'xy', attrs: {} }), v(['a', B], ['x'], ['y'], ['b']));
  assert.deepEqual(localEdit(view0, { kind: 'insert', index: 1, text: 'x', attrs: { bold: null } }), v(['a', B], ['x'], ['b']));
  assert.deepEqual(localEdit(view0, { kind: 'format', index: 1, len: 1, attrs: B }), v(['a', B], ['b', B]));
  assert.notDeepEqual(localEdit(view0, { kind: 'format', index: 0, len: 1, attrs: { bold: null } }), view0);
  assert.throws(() => localEdit(view0, { kind: 'delete', index: 1, len: 2 }), RangeError);
});

test('witness search: concurrent mark and boundary insert under the two semantics', () => {
  // Events: A inserts a; M marks a bold (expand after) after A; X inserts h
  // at the head after A, concurrent with M. Anchor: start before a, so h is
  // never covered: views { h a* }. Marker: begin and h both at the head:
  // views { h a*, h* a* }.
  const anchor = textSpec({ semantics: 'anchor', direct: 'chars' });
  const marker = textSpec({ semantics: 'marker', direct: 'chars' });
  const evA = { key: 'A', deps: [], specOps: [ins('a', 'a')] };
  const evX = { key: 'X', deps: ['A'], specOps: [ins('h', 'h', null, 'a')] };
  const mA = { key: 'M', deps: ['A'], specOps: [mark('m', 'bold', true, before('a'), null)] };
  const mM = { key: 'M', deps: ['A'], specOps: [markB('m', 'bold', true, { id: 'mb', origin: null, rightOrigin: 'a' }, { id: 'me', origin: 'a', rightOrigin: null })] };
  assert.deepEqual(allFinalViews(anchor, [evA, evX, mA]), [v(['h'], ['a', B])]);
  const mv = allFinalViews(marker, [evA, evX, mM]);
  assert.equal(mv.length, 2);
  assert.ok(mv.some((w) => viewsEqual(w, v(['h', B], ['a', B]))));
  const target = [{ id: 'h', ch: 'h', attrs: B }, { id: 'a', ch: 'a', attrs: B }];
  assert.equal(findWitness(anchor, [evA, evX, mA], target).found, false);
  assert.equal(findWitness(marker, [evA, evX, mM], target).found, true);
});

console.log(`${passed} passed`);
