/**
 * Hand-derived tests for the Y.Text specification and the witness search. Every expected value is
 * written out by hand; every block also asserts that a tempting wrong answer
 * is not produced. Run with `node spec-tests.mjs`.
 */
import assert from 'node:assert/strict';
import { initial, apply, applyAll, view, viewWithIds, serialise, localEdit, interpret, viewsEqual, findWitness, allFinalViews } from '../../ra-pbt/instances/yjs/oracle.js';

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

const A = [1, 0], B = [1, 1], C = [2, 0], X = [1, 2], Y = [2, 1];
const ins = (id, ch, origin, attrs = {}) => ({ kind: 'insert', id, ch, origin, attrs });
const del = (...ids) => ({ kind: 'delete', ids });
const fmt = (left, right, attrs) => ({ kind: 'format', left, right, attrs });
const fold = (ops) => ops.reduce((s, op) => (s === null ? null : apply(s, op)), initial());
const plain = (text) => [...text].map((ch) => ({ ch, attrs: {} }));
const v = (...pairs) => pairs.map(([ch, attrs]) => ({ ch, attrs: attrs ?? {} }));

test('insert after an origin places the later sibling nearer the anchor', () => {
  // a at head; b after a gives "ab"; c after a goes immediately after a: "acb".
  const s = fold([ins(A, 'a', null), ins(B, 'b', A), ins(C, 'c', A)]);
  assert.deepEqual(view(s), plain('acb'));
  assert.notDeepEqual(view(s), plain('abc'));
  assert.deepEqual(viewWithIds(s).map((e) => e.id), [A, C, B]);
});

test('insert at head and insert chain', () => {
  // b at head, then a at head: "ab"; then c after b: "abc".
  const s = fold([ins(B, 'b', null), ins(A, 'a', null), ins(C, 'c', B)]);
  assert.deepEqual(view(s), plain('abc'));
  assert.notDeepEqual(view(s), plain('bac'));
});

test('insert preconditions: missing origin and duplicate id fail', () => {
  assert.equal(apply(initial(), ins(A, 'a', B)), null);
  const s = fold([ins(A, 'a', null)]);
  assert.equal(apply(s, ins(A, 'z', null)), null);
  assert.notEqual(apply(s, ins(B, 'b', A)), null);
});

test('insert after a deleted origin is allowed and lands after it', () => {
  // a b, delete a, insert c after a: list a(del) c b, view "cb".
  const s = fold([ins(A, 'a', null), ins(B, 'b', A), del(A), ins(C, 'c', A)]);
  assert.deepEqual(view(s), plain('cb'));
  assert.notDeepEqual(view(s), plain('bc'));
});

test('delete preconditions: a missing id returns null, a deleted id stays deleted', () => {
  const s = fold([ins(A, 'a', null), ins(B, 'b', A)]);
  assert.equal(apply(s, del(C)), null);
  const s2 = apply(s, del(A));
  assert.deepEqual(view(s2), plain('b'));
  assert.deepEqual(apply(s2, del(A)), s2);
  assert.notEqual(apply(s2, del(A)), null);
  assert.deepEqual(view(apply(s, del(A, A))), plain('b'));
  assert.notEqual(apply(s, del(A, B)), null);
  assert.deepEqual(view(apply(s, del(A, B))), []);
});

test('format with reversed endpoints returns null, equal endpoints succeed', () => {
  const s = fold([ins(A, 'a', null), ins(B, 'b', A)]);
  assert.equal(apply(s, fmt(B, A, { bold: true })), null);
  assert.equal(apply(s, fmt(A, C, { bold: true })), null);
  const s2 = apply(s, fmt(B, B, { bold: true }));
  assert.deepEqual(view(s2), v(['a'], ['b', { bold: true }]));
  assert.notDeepEqual(view(s2), v(['a', { bold: true }], ['b', { bold: true }]));
});

test('format merges keys and removes with null', () => {
  // a b c; bold a..c; italic b..c; bold:null a..b gives a{} b{italic} c{bold,italic}.
  const s = fold([
    ins(A, 'a', null), ins(B, 'b', A), ins(C, 'c', B),
    fmt(A, C, { bold: true }), fmt(B, C, { italic: true }), fmt(A, B, { bold: null }),
  ]);
  assert.deepEqual(view(s), v(['a'], ['b', { italic: true }], ['c', { bold: true, italic: true }]));
  assert.notDeepEqual(view(s), v(['a'], ['b', { italic: true }], ['c', { italic: true }]));
  assert.ok(!('bold' in view(s)[0].attrs));
});

test('marks on a deleted character are invisible but the character still bounds a format', () => {
  // a b c, delete b, format b..c bold: view a c(bold); undelete is impossible so b's mark never shows.
  const s = fold([ins(A, 'a', null), ins(B, 'b', A), ins(C, 'c', B), del(B), fmt(B, C, { bold: true })]);
  assert.deepEqual(view(s), v(['a'], ['c', { bold: true }]));
  assert.notDeepEqual(view(s), v(['a'], ['b', { bold: true }], ['c', { bold: true }]));
  assert.equal(s[1].deleted, true);
  assert.deepEqual(s[1].attrs, { bold: true });
});

test('serialise is canonical across attribute key order', () => {
  const s1 = fold([ins(A, 'a', null, { b: 1, a: 2 })]);
  const s2 = fold([ins(A, 'a', null, { a: 2, b: 1 })]);
  assert.equal(serialise(s1), serialise(s2));
  const s3 = fold([ins(A, 'a', null, { a: 2 })]);
  assert.notEqual(serialise(s1), serialise(s3));
});

test('states are immutable', () => {
  const s = fold([ins(A, 'a', null)]);
  const before = serialise(s);
  apply(s, fmt(A, A, { bold: true }));
  apply(s, del(A));
  assert.equal(serialise(s), before);
  assert.notEqual(serialise(apply(s, del(A))), before);
});

test('localEdit insert carries exactly the request attributes', () => {
  const base = v(['a', { bold: true }], ['b']);
  const out = localEdit(base, { kind: 'insert', index: 1, text: 'xy', attrs: { italic: true } });
  assert.deepEqual(out, v(['a', { bold: true }], ['x', { italic: true }], ['y', { italic: true }], ['b']));
  // Not inherited from the left neighbour.
  assert.notDeepEqual(out, v(['a', { bold: true }], ['x', { bold: true, italic: true }], ['y', { bold: true, italic: true }], ['b']));
  assert.deepEqual(localEdit(plain('ab'), { kind: 'insert', index: 2, text: 'c' }), plain('abc'));
});

test('localEdit delete removes exactly the range', () => {
  const out = localEdit(plain('abcd'), { kind: 'delete', index: 1, len: 2 });
  assert.deepEqual(out, plain('ad'));
  assert.notDeepEqual(out, plain('abd'));
});

test('localEdit format merges into exactly the range', () => {
  const base = v(['a', { bold: true }], ['b', { bold: true }], ['c']);
  const out = localEdit(base, { kind: 'format', index: 1, len: 2, attrs: { bold: null, italic: true } });
  assert.deepEqual(out, v(['a', { bold: true }], ['b', { italic: true }], ['c', { italic: true }]));
  assert.notDeepEqual(out, v(['a', { italic: true }], ['b', { italic: true }], ['c', { italic: true }]));
});

test('localEdit throws on out-of-range requests', () => {
  assert.throws(() => localEdit(plain('ab'), { kind: 'insert', index: 3, text: 'x' }), RangeError);
  assert.throws(() => localEdit(plain('ab'), { kind: 'delete', index: 1, len: 2 }), RangeError);
  assert.throws(() => localEdit(plain('ab'), { kind: 'format', index: -1, len: 1, attrs: {} }), RangeError);
  assert.doesNotThrow(() => localEdit(plain('ab'), { kind: 'delete', index: 1, len: 1 }));
});

test('interpret a two-character insert record', () => {
  const record = {
    kind: 'insert',
    chars: [
      { id: [3, 0], ch: 'x', origin: A, rightOrigin: B, attrs: { bold: true } },
      { id: [3, 1], ch: 'y', origin: [3, 0], rightOrigin: B, attrs: { bold: true } },
    ],
  };
  const expected = [
    { kind: 'insert', id: [3, 0], ch: 'x', origin: A, rightOrigin: B, attrs: { bold: true } },
    { kind: 'insert', id: [3, 1], ch: 'y', origin: [3, 0], rightOrigin: B, attrs: { bold: true } },
  ];
  assert.deepEqual(interpret(record), expected);
  // Both characters anchored at the original left neighbour would reverse them.
  assert.notDeepEqual(interpret(record), [
    { kind: 'insert', id: [3, 0], ch: 'x', origin: A, rightOrigin: B, attrs: { bold: true } },
    { kind: 'insert', id: [3, 1], ch: 'y', origin: A, rightOrigin: B, attrs: { bold: true } },
  ]);
  // a b, then xy after a: "axyb", not "ayxb".
  const s = fold([ins(A, 'a', null), ins(B, 'b', A), ...interpret(record)]);
  assert.deepEqual(view(s).map((e) => e.ch).join(''), 'axyb');
});

test('placement rules: the gap rule admits a concurrent head insert between a character and its right origin', () => {
  // p (client 1), d (client 2) and j (client 3) are concurrent head inserts.
  // Client 3 then sees "p j" and inserts t between them, recording origin p
  // and right origin j. Yjs shows p t d j: t stays in p's subtree and d, a
  // head sibling, sorts between p's subtree and j.
  // Two-sided rule: t lands immediately before j, so d can never separate t
  // from j: no witness. One-sided rule: t lands immediately after p, and the
  // order j, d, p, t gives p t d j. Gap rule: t may take any position between
  // p and j, and the same order gives p t d j.
  const P = [1, 0];
  const D = [2, 0];
  const J = [3, 0];
  const T = [3, 1];
  const events = [
    { key: 'p', deps: [], specOps: [{ kind: 'insert', id: P, ch: 'p', origin: null, rightOrigin: null, attrs: {} }] },
    { key: 'd', deps: [], specOps: [{ kind: 'insert', id: D, ch: 'd', origin: null, rightOrigin: null, attrs: {} }] },
    { key: 'j', deps: [], specOps: [{ kind: 'insert', id: J, ch: 'j', origin: null, rightOrigin: null, attrs: {} }] },
    { key: 't', deps: ['p', 'j'], specOps: [{ kind: 'insert', id: T, ch: 't', origin: P, rightOrigin: J, attrs: {} }] },
  ];
  const target = plain('ptdj');
  assert.equal(findWitness(events, target).found, true);
  assert.equal(findWitness(events, target, { rule: 'gap' }).found, true);
  assert.equal(findWitness(events, target, { rule: 'left' }).found, true);
  assert.equal(findWitness(events, target, { rule: 'both' }).found, false);
  const bothViews = allFinalViews(events, { rule: 'both' }).map((v) => v.map((c) => c.ch).join(''));
  assert.ok(bothViews.every((v) => v.indexOf('t') + 1 === v.indexOf('j')));
  // The gap rule never places t outside its gap: p always precedes t and t precedes j.
  const gapViews = allFinalViews(events).map((v) => v.map((c) => c.ch).join(''));
  assert.ok(gapViews.every((v) => v.indexOf('p') < v.indexOf('t') && v.indexOf('t') < v.indexOf('j')));
  assert.ok(!gapViews.includes('tpdj'));
  // A right origin that precedes the origin is a precondition failure under every rule.
  const s = fold([ins(P, 'p', null), ins(J, 'j', P)]);
  const bad = { kind: 'insert', id: T, ch: 't', origin: J, rightOrigin: P, attrs: {} };
  assert.equal(apply(s, bad), null);
  assert.deepEqual(applyAll(s, bad), []);
});

test('interpret delete and format records, ignoring covered', () => {
  assert.deepEqual(interpret({ kind: 'delete', deleted: [A, B] }), [{ kind: 'delete', ids: [A, B] }]);
  const f = interpret({ kind: 'format', range: { left: A, right: B, covered: [A] }, request: { attrs: { bold: true } } });
  assert.deepEqual(f, [{ kind: 'format', left: A, right: B, attrs: { bold: true } }]);
  assert.notDeepEqual(f, [{ kind: 'format', left: A, right: A, attrs: { bold: true } }]);
});

test('witness: concurrent inserts after one anchor admit both arrangements', () => {
  // e0 inserts a; replica 1 inserts x after a, replica 2 inserts y after a, concurrently.
  // Order e0 ex ey: a x, then y after a: "ayx". Order e0 ey ex: "axy". Both are witnesses.
  const ops = [
    { key: 'e0', deps: [], specOps: [ins(A, 'a', null)] },
    { key: 'ex', deps: ['e0'], specOps: [ins(X, 'x', A)] },
    { key: 'ey', deps: ['e0'], specOps: [ins(Y, 'y', A)] },
  ];
  // Under the one-sided rule each arrangement has exactly one witness order;
  // under the gap rule a later insert may also land after an earlier one, so
  // only existence is pinned there.
  assert.deepEqual(findWitness(ops, plain('axy'), { rule: 'left' }), { found: true, order: ['e0', 'ey', 'ex'] });
  assert.deepEqual(findWitness(ops, plain('ayx'), { rule: 'left' }), { found: true, order: ['e0', 'ex', 'ey'] });
  assert.equal(findWitness(ops, plain('axy')).found, true);
  assert.equal(findWitness(ops, plain('ayx')).found, true);
  const w3 = findWitness(ops, plain('xay'));
  assert.equal(w3.found, false);
  assert.equal(w3.reachableViews, 2);
  assert.deepEqual(allFinalViews(ops), [plain('axy'), plain('ayx')]);
});

test('witness: the order respects causality and transitive deps', () => {
  // e0 a; e1 b after a (deps e0); e2 deletes a (deps e1 only, e0 via closure).
  const ops = [
    { key: 'e2', deps: ['e1'], specOps: [del(A)] },
    { key: 'e1', deps: ['e0'], specOps: [ins(B, 'b', A)] },
    { key: 'e0', deps: [], specOps: [ins(A, 'a', null)] },
  ];
  assert.deepEqual(findWitness(ops, plain('b')), { found: true, order: ['e0', 'e1', 'e2'] });
  assert.equal(findWitness(ops, plain('ab')).found, false);
});

// The key test.
//
// Prefix (all causally ordered): e0 a; e1 b after a; e2 c after b; e3 format b..b bold:true.
// State after the prefix: a{} b{bold} c{}.
// e4 = format a..b bold:true, e5 = format b..c bold:null, concurrent, both after e3.
// Linear extensions: e0 e1 e2 e3 e4 e5 and e0 e1 e2 e3 e5 e4.
//   e4 then e5: after e4 a{bold} b{bold} c{}; after e5 b,c lose bold: a{bold} b{} c{}.
//   e5 then e4: after e5 a{} b{} c{};      after e4 a,b gain bold: a{bold} b{bold} c{}.
// So the spec admits exactly "a(bold) b c" and "a(bold) b(bold) c"; "all three bold" is
// reachable by neither, since c is only ever unbolded by e5 and never bolded after e2.
const bold = { bold: true };
const keyOps = [
  { key: 'e0', deps: [], specOps: [ins(A, 'a', null)] },
  { key: 'e1', deps: ['e0'], specOps: [ins(B, 'b', A)] },
  { key: 'e2', deps: ['e1'], specOps: [ins(C, 'c', B)] },
  { key: 'e3', deps: ['e0', 'e1', 'e2'], specOps: [fmt(B, B, bold)] },
  { key: 'e4', deps: ['e0', 'e1', 'e2', 'e3'], specOps: [fmt(A, B, { bold: true })] },
  { key: 'e5', deps: ['e0', 'e1', 'e2', 'e3'], specOps: [fmt(B, C, { bold: null })] },
];
const aBold = v(['a', bold], ['b'], ['c']);
const abBold = v(['a', bold], ['b', bold], ['c']);
const allBold = v(['a', bold], ['b', bold], ['c', bold]);

test('witness key test: all three bold has no witness', () => {
  const w = findWitness(keyOps, allBold);
  assert.equal(w.found, false);
  assert.equal(w.reachableViews, 2);
  assert.ok(w.explored > 0);
});

test('witness key test: a(bold) b c and a(bold) b(bold) c each have one witness', () => {
  assert.deepEqual(findWitness(keyOps, aBold), { found: true, order: ['e0', 'e1', 'e2', 'e3', 'e4', 'e5'] });
  assert.deepEqual(findWitness(keyOps, abBold), { found: true, order: ['e0', 'e1', 'e2', 'e3', 'e5', 'e4'] });
  assert.notDeepEqual(findWitness(keyOps, abBold).order, ['e0', 'e1', 'e2', 'e3', 'e4', 'e5']);
});

test('witness key test: allFinalViews is exactly the two views', () => {
  const views = allFinalViews(keyOps);
  assert.equal(views.length, 2);
  assert.ok(views.some((x) => viewsEqual(x, aBold)));
  assert.ok(views.some((x) => viewsEqual(x, abBold)));
  assert.ok(!views.some((x) => viewsEqual(x, allBold)));
  console.log('     allFinalViews =', JSON.stringify(views));
});

// e0 inserts "abcdefghijk" as one event; eleven concurrent events each insert the
// upper-case letter after its lower-case anchor. The inserts commute, so the only
// final view is "aAbBcC...kK".
function wideHistory(n) {
  const lower = 'abcdefghijklmnopqrstuvwxyz'.slice(0, n);
  const base = [...lower].map((ch, i) => ins([0, i], ch, i === 0 ? null : [0, i - 1]));
  const ops = [{ key: 'base', deps: [], specOps: base }];
  [...lower].forEach((ch, i) => {
    ops.push({ key: 'u' + i, deps: ['base'], specOps: [ins([i + 1, 0], ch.toUpperCase(), [0, i])] });
  });
  return ops;
}

test('witness over 12 events completes', () => {
  const ops = wideHistory(11);
  assert.equal(ops.length, 12);
  const w = findWitness(ops, plain('aAbBcCdDeEfFgGhHiIjJkK'), { rule: 'left' });
  assert.equal(w.found, true);
  assert.equal(w.order[0], 'base');
  const neg = findWitness(ops, plain('abcdefghijkABCDEFGHIJK'), { rule: 'left' });
  assert.equal(neg.found, false);
  assert.equal(neg.reachableViews, 1);
});

test('witness over 20 events terminates and reports', () => {
  const ops = wideHistory(19);
  assert.equal(ops.length, 20);
  const neg = findWitness(ops, plain('x'), { rule: 'left' });
  assert.equal(neg.found, false);
  assert.equal(neg.reachableViews, 1);
  // One state per down-closed subset: the empty set plus base with any subset of 19.
  assert.equal(neg.explored, 1 + 2 ** 19);
});

test('witness under the gap rule compares views without identities: repeated characters', () => {
  // Client 1 inserts x at the head; client 2, having seen it, inserts a second
  // x at the head with the first as its right origin. The second x can only
  // land before the first, so the display is "xx" whichever identities the
  // target lists first. A search restricted to the target's identity order
  // would reject the swapped listing; the view ignores identities, so both
  // listings have the witness, and a bold x has none.
  const A = [1, 0];
  const B = [2, 0];
  const events = [
    { key: 'a', deps: [], specOps: [{ kind: 'insert', id: A, ch: 'x', origin: null, rightOrigin: null, attrs: {} }] },
    { key: 'b', deps: ['a'], specOps: [{ kind: 'insert', id: B, ch: 'x', origin: null, rightOrigin: A, attrs: {} }] },
  ];
  const listed = (first, second) => [{ id: first, ch: 'x', attrs: {} }, { id: second, ch: 'x', attrs: {} }];
  assert.deepEqual(findWitness(events, listed(B, A)), { found: true, order: ['a', 'b'] });
  assert.deepEqual(findWitness(events, listed(A, B)), { found: true, order: ['a', 'b'] });
  assert.equal(findWitness(events, [{ id: A, ch: 'x', attrs: { bold: true } }, { id: B, ch: 'x', attrs: {} }]).found, false);
  assert.equal(findWitness(events, plain('x')).found, false);
});

test('the gap enumeration without a target is capped and says so', () => {
  const views = allFinalViews(wideHistory(6), { limit: 500 });
  assert.equal(views.truncated, true);
  assert.notEqual(allFinalViews(wideHistory(3)).truncated, true);
});

test('witness search rejects malformed histories', () => {
  assert.throws(() => findWitness([{ key: 'p', deps: ['q'], specOps: [] }], []));
  assert.throws(() => findWitness([
    { key: 'p', deps: ['q'], specOps: [] },
    { key: 'q', deps: ['p'], specOps: [] },
  ], []));
  assert.deepEqual(findWitness([], []), { found: true, order: [] });
});

console.log(`${passed} passed`);
