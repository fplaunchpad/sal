/**
 * Hand-derived tests for the Loro text specification and the witness search
 * bound to it. Every expected value is written out by hand; every block also
 * asserts that a tempting wrong answer is not produced. Run with
 * `node spec-tests.mjs`.
 */
import assert from 'node:assert/strict';
import {
  initial,
  apply,
  applyAll,
  applyPlaced,
  placementOf,
  view,
  viewWithIds,
  localEdit,
  expandAttrs,
  interpret,
  viewsEqual,
  findWitness,
  allFinalViews,
  EXPAND,
} from '../../ra-pbt/instances/loro/oracle.js';
import * as anchored from '../../ra-pbt/instances/loro/anchored.js';

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

const A = [1, 0], B = [1, 1], C = [2, 0], D = [2, 1], X = [3, 0];
const ins = (id, ch, origin, rightOrigin = null, attrs = {}) => ({ kind: 'insert', id, ch, origin, rightOrigin, attrs });
const del = (...ids) => ({ kind: 'delete', ids });
const mark = (left, right, key, value = true, outerLeft = null, outerRight = null) => ({ kind: 'mark', left, right, outerLeft, outerRight, key, value });
const fold = (ops, rule = 'both') => ops.reduce((s, op) => (s === null ? null : apply(s, op, rule)), initial());
const plain = (text) => [...text].map((ch) => ({ ch, attrs: {} }));
const v = (...pairs) => pairs.map(([ch, attrs]) => ({ ch, attrs: attrs ?? {} }));
const bold = { bold: true };
const link = { link: true };
const sup = { sup: true };
const hl = { hl: true };

test('the expand table is the one the instance configures', () => {
  assert.deepEqual({ ...EXPAND }, { bold: 'after', link: 'none', sup: 'before', hl: 'both' });
  assert.notEqual(EXPAND.link, 'after');
});

test('left rule: a later sibling of one origin lands nearer it', () => {
  // a at head; b after a: "ab"; c after a lands immediately after a: "acb".
  const s = fold([ins(A, 'a', null), ins(B, 'b', A), ins(C, 'c', A)], 'left');
  assert.deepEqual(view(s), plain('acb'));
  assert.notDeepEqual(view(s), plain('abc'));
  assert.deepEqual(viewWithIds(s).map((e) => e.id), [A, C, B]);
});

test('both rule: an insertion with a right origin lands immediately before it', () => {
  // a, then b after a: "ab"; c recorded (a, b) lands before b: "acb";
  // d recorded (a, b) also lands immediately before b: "acdb", not "adcb".
  const s = fold([ins(A, 'a', null), ins(B, 'b', A), ins(C, 'c', A, B), ins(D, 'd', A, B)], 'both');
  assert.deepEqual(view(s), plain('acdb'));
  assert.notDeepEqual(view(s), plain('adcb'));
  // Under the left rule the same ops give "adcb": d lands right after a.
  const l = fold([ins(A, 'a', null), ins(B, 'b', A), ins(C, 'c', A, B), ins(D, 'd', A, B)], 'left');
  assert.deepEqual(view(l), plain('adcb'));
  assert.notDeepEqual(view(l), plain('acdb'));
});

test('gap rule: every position strictly between the origins, and nothing else', () => {
  // State a c b (c between a and b); d recorded (a, b) may land at 1 or 2: "adcb", "acdb".
  const s = fold([ins(A, 'a', null), ins(B, 'b', A), ins(C, 'c', A, B)]);
  const outs = applyAll(s, ins(D, 'd', A, B), 'gap').map((st) => view(st).map((e) => e.ch).join(''));
  assert.deepEqual(outs, ['adcb', 'acdb']);
  assert.ok(!outs.includes('dacb'), 'd landed before its origin');
  assert.ok(!outs.includes('acbd'), 'd landed after its right origin');
});

test('insert preconditions: missing origin, duplicate id, origins out of order', () => {
  assert.equal(apply(initial(), ins(A, 'a', B)), null);
  const s = fold([ins(A, 'a', null), ins(B, 'b', A)]);
  assert.equal(apply(s, ins(A, 'z', null)), null);
  assert.equal(apply(s, ins(C, 'c', B, A), 'both'), null);
  // the one-sided rule ignores the right origin: c lands right after b
  assert.deepEqual(view(apply(s, ins(C, 'c', B, A), 'left')), plain('abc'));
  assert.notEqual(apply(s, ins(C, 'c', B, A), 'left'), null);
  assert.deepEqual(applyAll(s, ins(C, 'c', B, A), 'gap'), []);
  assert.notEqual(apply(s, ins(C, 'c', A, B)), null);
});

test('delete is idempotent and keeps the character as an anchor', () => {
  const s = fold([ins(A, 'a', null), ins(B, 'b', A)]);
  const s1 = apply(s, del(A));
  assert.deepEqual(view(s1), plain('b'));
  assert.deepEqual(apply(s1, del(A)), s1);
  assert.notEqual(apply(s1, del(A)), null);
  // insert after the deleted a lands before b under the left rule
  assert.deepEqual(view(apply(s1, ins(C, 'c', A), 'left')), plain('cb'));
  assert.notDeepEqual(view(apply(s1, ins(C, 'c', A), 'left')), plain('bc'));
  assert.equal(apply(s, del(X)), null);
});

test('mark sets a key on the identity interval, deleted characters included; unmark clears it', () => {
  // a b c, delete b, mark a..c bold: a(bold) c(bold); b carries bold too.
  const s = fold([ins(A, 'a', null), ins(B, 'b', A), ins(C, 'c', B), del(B), mark(A, C, 'bold')]);
  assert.deepEqual(view(s), v(['a', bold], ['c', bold]));
  assert.deepEqual(s[1].attrs, bold);
  assert.notDeepEqual(view(s), v(['a', bold], ['c']));
  const u = apply(s, mark(C, C, 'bold', null));
  assert.deepEqual(view(u), v(['a', bold], ['c']));
  assert.notDeepEqual(view(u), v(['a'], ['c']));
  assert.equal(apply(s, mark(C, A, 'bold')), null);
});

test('a mark covers a character inserted between its endpoints before it is applied', () => {
  // a b; x recorded (a, b); mark a..b link. x applied first: covered. Mark first: x keeps its own {}.
  const base = [ins(A, 'a', null), ins(B, 'b', A)];
  const xFirst = fold([...base, ins(X, 'x', A, B), mark(A, B, 'link')]);
  const mFirst = fold([...base, mark(A, B, 'link'), ins(X, 'x', A, B)]);
  assert.deepEqual(view(xFirst), v(['a', link], ['x', link], ['b', link]));
  assert.deepEqual(view(mFirst), v(['a', link], ['x'], ['b', link]));
  assert.notDeepEqual(view(xFirst), view(mFirst));
});

test('expandAttrs: one key of each expand type at each boundary', () => {
  const L = (attrs) => ({ ch: 'l', attrs });
  // end boundary (left neighbour styled, right not)
  assert.deepEqual(expandAttrs(L(bold), L({})), bold);
  assert.deepEqual(expandAttrs(L(hl), L({})), hl);
  assert.deepEqual(expandAttrs(L(link), L({})), {});
  assert.deepEqual(expandAttrs(L(sup), L({})), {});
  assert.notDeepEqual(expandAttrs(L(link), L({})), link);
  // start boundary (right neighbour styled, left not)
  assert.deepEqual(expandAttrs(L({}), L(bold)), {});
  assert.deepEqual(expandAttrs(L({}), L(sup)), sup);
  assert.deepEqual(expandAttrs(L({}), L(hl)), hl);
  assert.deepEqual(expandAttrs(L({}), L(link)), {});
  assert.notDeepEqual(expandAttrs(L({}), L(bold)), bold);
  // inside: both neighbours carry the same value
  assert.deepEqual(expandAttrs(L(link), L(link)), link);
  assert.deepEqual(expandAttrs(L({ ...link, ...bold }), L(link)), { bold: true, link: true });
  // ends of the text
  assert.deepEqual(expandAttrs(null, L(sup)), sup);
  assert.deepEqual(expandAttrs(L(bold), null), bold);
  assert.deepEqual(expandAttrs(null, L(bold)), {});
  assert.notDeepEqual(expandAttrs(null, L(bold)), bold);
  // different values on the two sides
  assert.deepEqual(expandAttrs(L({ bold: 'x' }), L({ bold: 'y' })), { bold: 'x' });
  assert.deepEqual(expandAttrs(L({ sup: 'x' }), L({ sup: 'y' })), { sup: 'y' });
  assert.deepEqual(expandAttrs(L({ link: 'x' }), L({ link: 'y' })), {});
});

test('localEdit: insert takes expandAttrs, mark and unmark change exactly the range', () => {
  const vw = v(['a', bold], ['b', bold], ['c']);
  assert.deepEqual(localEdit(vw, { kind: 'insert', index: 2, text: 'xy' }), v(['a', bold], ['b', bold], ['x', bold], ['y', bold], ['c']));
  assert.deepEqual(localEdit(vw, { kind: 'insert', index: 0, text: 'x' }), v(['x'], ['a', bold], ['b', bold], ['c']));
  assert.notDeepEqual(localEdit(vw, { kind: 'insert', index: 0, text: 'x' }), v(['x', bold], ['a', bold], ['b', bold], ['c']));
  assert.deepEqual(localEdit(vw, { kind: 'mark', index: 1, len: 2, key: 'link', value: true }), v(['a', bold], ['b', { bold: true, link: true }], ['c', link]));
  assert.notDeepEqual(localEdit(vw, { kind: 'mark', index: 1, len: 2, key: 'link', value: true }), v(['a', { bold: true, link: true }], ['b', { bold: true, link: true }], ['c', link]));
  assert.deepEqual(localEdit(vw, { kind: 'unmark', index: 0, len: 1, key: 'bold' }), v(['a'], ['b', bold], ['c']));
  assert.notDeepEqual(localEdit(vw, { kind: 'unmark', index: 0, len: 1, key: 'bold' }), v(['a'], ['b'], ['c']));
  assert.deepEqual(localEdit(vw, { kind: 'delete', index: 1, len: 1 }), v(['a', bold], ['c']));
  assert.throws(() => localEdit(vw, { kind: 'mark', index: 2, len: 2, key: 'bold', value: true }), RangeError);
  assert.throws(() => localEdit(vw, { kind: 'insert', index: 4, text: 'x' }), RangeError);
});

test('interpret: records become specification operations', () => {
  const r = { kind: 'insert', chars: [{ id: A, ch: 'a', origin: null, rightOrigin: C, attrs: bold, knownMarks: ['1:7'] }, { id: B, ch: 'b', origin: A, rightOrigin: C, attrs: bold, knownMarks: ['1:7'] }] };
  assert.deepEqual(interpret(r), [{ ...ins(A, 'a', null, C, bold), knownMarks: ['1:7'] }, { ...ins(B, 'b', A, C, bold), knownMarks: ['1:7'] }]);
  const u = { kind: 'unmark', markId: '2:4', styleKey: 'bold', value: null, range: { left: A, right: B, outerLeft: null, outerRight: C } };
  assert.deepEqual(interpret(u), [{ ...mark(A, B, 'bold', null, null, C), mid: '2:4' }]);
  assert.notDeepEqual(interpret(u), [{ ...mark(A, B, 'bold', true, null, C), mid: '2:4' }]);
  assert.deepEqual(interpret({ kind: 'delete', deleted: [A] }), [del(A)]);
});

test('applyPlaced keeps only placements in the target order', () => {
  // a b; d recorded (a, b), target a c d b with c already placed between a and b.
  const s = fold([ins(A, 'a', null), ins(B, 'b', A), ins(C, 'c', A, B)]);
  const target = [{ id: A, ch: 'a' }, { id: C, ch: 'c' }, { id: D, ch: 'd' }, { id: B, ch: 'b' }];
  const outs = applyPlaced(s, ins(D, 'd', A, B), placementOf(target)).map((st) => view(st).map((e) => e.ch).join(''));
  assert.deepEqual(outs, ['acdb']);
  assert.ok(!outs.includes('adcb'));
});

test('inherit reading: an insertion takes the expand rule from its visible neighbours when applied', () => {
  // a b, mark a..b bold, then x recorded (b, none) issued on a replica that saw no bold (carries {}).
  // carry: x stays plain. inherit: x lands after b(bold) at the end; bold expands after: x(bold).
  const ops = [ins(A, 'a', null), ins(B, 'b', A), mark(A, B, 'bold'), ins(X, 'x', B, null, {})];
  const carry = ops.reduce((s, op) => apply(s, op, 'left', { attrsMode: 'carry' }), initial());
  const inherit = ops.reduce((s, op) => apply(s, op, 'left', { attrsMode: 'inherit' }), initial());
  assert.deepEqual(view(carry), v(['a', bold], ['b', bold], ['x']));
  assert.deepEqual(view(inherit), v(['a', bold], ['b', bold], ['x', bold]));
  assert.notDeepEqual(view(inherit), view(carry));
  // The same with link (expand none): both readings leave x plain.
  const lops = [ins(A, 'a', null), ins(B, 'b', A), mark(A, B, 'link'), ins(X, 'x', B, null, {})];
  const linh = lops.reduce((s, op) => apply(s, op, 'left', { attrsMode: 'inherit' }), initial());
  assert.deepEqual(view(linh), v(['a', link], ['b', link], ['x']));
  assert.notDeepEqual(view(linh), v(['a', link], ['b', link], ['x', link]));
  // inherit skips deleted neighbours: a b, bold b, delete b, x after b: left visible neighbour a (plain), x plain.
  const dops = [ins(A, 'a', null), ins(B, 'b', A), mark(B, B, 'bold'), del(B), ins(X, 'x', B, null, {})];
  const dinh = dops.reduce((s, op) => apply(s, op, 'left', { attrsMode: 'inherit' }), initial());
  assert.deepEqual(view(dinh), v(['a'], ['x']));
  assert.notDeepEqual(view(dinh), v(['a'], ['x', bold]));
  // gap rule under inherit: each placement inherits from its own neighbours.
  const s0 = fold([ins(A, 'a', null), ins(B, 'b', A), mark(B, B, 'bold')]);
  const outs = applyAll(s0, ins(X, 'x', null, null, {}), 'gap', { attrsMode: 'inherit' }).map((st) => JSON.stringify(view(st)));
  assert.deepEqual(outs, [v(['x'], ['a'], ['b', bold]), v(['a'], ['x'], ['b', bold]), v(['a'], ['b', bold], ['x', bold])].map((w) => JSON.stringify(w)));
  assert.ok(!outs.includes(JSON.stringify(v(['a'], ['b', bold], ['x']))));
});

test('expand reading: a mark reaches the gaps its expand type extends to, an unmark by the reversed type', () => {
  // a b c; x inserted between b and c (recorded (b, c), carrying {}); then a
  // mark over b, issued without x, whose outer neighbours are a and c.
  const base = [ins(A, 'a', null), ins(B, 'b', A), ins(C, 'c', B), ins(X, 'x', B, C, {})];
  const run = (op) => view([...base, op].reduce((s, o) => apply(s, o, 'both', { attrsMode: 'expand' }), initial()));
  // bold expands after: x, in the gap after b, is covered; a is not.
  assert.deepEqual(run(mark(B, B, 'bold', true, A, C)), v(['a'], ['b', bold], ['x', bold], ['c']));
  assert.notDeepEqual(run(mark(B, B, 'bold', true, A, C)), v(['a'], ['b', bold], ['x'], ['c']));
  // link expands nowhere: only b.
  assert.deepEqual(run(mark(B, B, 'link', true, A, C)), v(['a'], ['b', link], ['x'], ['c']));
  assert.notDeepEqual(run(mark(B, B, 'link', true, A, C)), v(['a'], ['b', link], ['x', link], ['c']));
  // sup expands before: the gap between a and b is empty, x stays plain.
  assert.deepEqual(run(mark(B, B, 'sup', true, A, C)), v(['a'], ['b', sup], ['x'], ['c']));
  // carry ignores the outer neighbours: x plain under bold.
  assert.deepEqual(view([...base, mark(B, B, 'bold', true, A, C)].reduce((s, o) => apply(s, o, 'both', { attrsMode: 'carry' }), initial())), v(['a'], ['b', bold], ['x'], ['c']));
  // unmark of link extends both ways (none reversed is both): with x and b
  // linked, an unmark of b alone clears x too.
  const linked = [...base, mark(A, C, 'link', true, null, null)];
  const un = [...linked, mark(B, B, 'link', null, A, C)].reduce((s, o) => apply(s, o, 'both', { attrsMode: 'expand' }), initial());
  assert.deepEqual(view(un), v(['a', link], ['b'], ['x'], ['c', link]));
  assert.notDeepEqual(view(un), v(['a', link], ['b'], ['x', link], ['c', link]));
  // an outer neighbour missing from the state is a precondition failure
  assert.equal(apply(fold([ins(A, 'a', null)]), mark(A, A, 'bold', true, null, B), 'both', { attrsMode: 'expand' }), null);
});

test('anchors reading: a mark may extend over any adjoining part of its boundary gaps', () => {
  // a x y b c: x, y inserted between a and b without the mark's issuer seeing
  // them; mark b..b with outer neighbours a and c. Left extensions: b, y b,
  // x y b; the right gap (b, c) is empty. Expand type plays no part.
  const s0 = fold([ins(A, 'a', null), ins(B, 'b', A), ins(C, 'c', B), ins(X, 'x', A, B), ins(D, 'y', X, B)]);
  for (const key of ['bold', 'link']) {
    const outs = applyAll(s0, mark(B, B, key, true, A, C), 'gap', { attrsMode: 'anchors' }).map((st) => view(st).map((e) => e.ch + (e.attrs[key] ? '+' : '')).join(''));
    assert.deepEqual(outs.sort(), ['ax+y+b+c', 'axy+b+c', 'axyb+c'].sort());
    assert.ok(!outs.includes('ax+yb+c'), 'a non-adjoining part of the gap was covered');
    assert.ok(!outs.includes('a+xyb+c'), 'the outer neighbour was covered');
  }
  // under carry the same op has the single outcome b only
  assert.deepEqual(applyAll(s0, mark(B, B, 'bold', true, A, C), 'gap', { attrsMode: 'carry' }).length, 1);
});

test('persistent reading: marks are ranges between anchors; an insertion honours the marks it knew', () => {
  const P = anchored;
  const pmark = (mid, left, right, key, value, outerLeft = null, outerRight = null) => ({ kind: 'mark', mid, left, right, outerLeft, outerRight, key, value });
  const pins = (id, ch, origin, rightOrigin, attrs, knownMarks) => ({ kind: 'insert', id, ch, origin, rightOrigin, attrs, knownMarks });
  const one = (st, op) => {
    const outs = P.applyAll(st, op);
    assert.equal(outs.length, 1, `expected one outcome, got ${outs.length}`);
    return outs[0];
  };
  const shown = (st) => P.view(st).map((e) => e.ch + Object.keys(e.attrs).map((k) => '.' + k).join('')).join(' ');
  // a b; mark m1 bold over a with outer neighbours none and b: anchors around a, the end anchor
  // either just before b: a single placement each (gap (head, a) and (a, b) are empty of items).
  let st = one(one(P.initial(), pins(A, 'a', null, null, {}, [])), pins(B, 'b', A, null, {}, []));
  st = one(st, pmark('m1', A, A, 'bold', true, null, B));
  assert.equal(shown(st), 'a.bold b');
  assert.notEqual(shown(st), 'a.bold b.bold');
  // x after a, issued knowing m1 with attrs bold (bold expands after): it must sit inside m1.
  const inside = P.applyAll(st, pins(X, 'x', A, B, { bold: true }, ['m1'])).map(shown);
  assert.deepEqual(inside, ['a.bold x.bold b']);
  // the same insert issued knowing m1 but carrying {}: it must sit outside m1.
  assert.deepEqual(P.applyAll(st, pins(X, 'x', A, B, {}, ['m1'])).map(shown), ['a.bold x b']);
  // issued without knowing m1 and carrying {}: either side of m1's end anchor.
  assert.deepEqual(P.applyAll(st, pins(X, 'x', A, B, {}, [])).map(shown).sort(), ['a.bold x b', 'a.bold x.bold b']);
  // issued knowing nothing and carrying bold: no placement gives a known-mark attribute it never saw.
  assert.deepEqual(P.applyAll(st, pins(X, 'x', A, B, { bold: true }, [])), []);
  // a later mark wins over an earlier one of the same key: m2's anchors may sit on either side
  // of m1's (two choices at each end), and every placement shows a plain. Deleting a keeps its anchors.
  const us = P.applyAll(st, pmark('m2', A, A, 'bold', null, null, B));
  assert.equal(us.length, 4);
  assert.deepEqual([...new Set(us.map(shown))], ['a b']);
  assert.ok(!us.map(shown).includes('a.bold b'));
  const u = one(us[0], { kind: 'delete', ids: [A] });
  assert.equal(P.serialise(u).includes('"m1","start"'), true);
  assert.equal(shown(u), 'b');
  // preconditions: a mark id used twice, a missing endpoint
  assert.deepEqual(P.applyAll(st, pmark('m1', A, A, 'bold', true, null, B)), []);
  assert.deepEqual(P.applyAll(st, pmark('m3', X, X, 'bold', true, null, null)), []);
});

/*
 * Witness search over three events: x (3:0) and y (2:0) are concurrent head
 * inserts with no recorded neighbours; z (2:1) is recorded after y, with no
 * right origin, by y's issuer, so y precedes z. The linear extensions are
 * x y z, y x z and y z x.
 * Left rule (a head insert always lands at the head; z lands right after y):
 *   x y z: [x] [y x] [y z x]          -> y z x
 *   y x z: [y] [x y] [x y z]          -> x y z
 *   y z x: [y] [y z] [x y z]          -> x y z
 * Admitted { x y z, y z x }; y x z has no witness.
 * Gap rule: z may land anywhere after y, and x anywhere: y x z is admitted
 * (y, x after y, z at the end), as are x y z and y z x.
 */
test('witness search under the left and gap rules on three events', () => {
  const Y = [2, 0], Z = [2, 1];
  const events = [
    { key: 'x', deps: [], specOps: [ins(X, 'x', null)] },
    { key: 'y', deps: [], specOps: [ins(Y, 'y', null)] },
    { key: 'z', deps: ['y'], specOps: [ins(Z, 'z', Y)] },
  ];
  const keyed = (vs) => vs.map((w) => w.map((e) => e.ch).join('')).sort();
  assert.deepEqual(keyed(allFinalViews(events, { rule: 'left' })), ['xyz', 'yzx']);
  assert.ok(!keyed(allFinalViews(events, { rule: 'left' })).includes('yxz'));
  assert.deepEqual(keyed(allFinalViews(events, { rule: 'gap' })), ['xyz', 'yxz', 'yzx']);
  const target = [{ id: Y, ch: 'y', attrs: {} }, { id: X, ch: 'x', attrs: {} }, { id: Z, ch: 'z', attrs: {} }];
  assert.equal(findWitness(events, target, { rule: 'left' }).found, false);
  assert.equal(findWitness(events, target, { rule: 'gap' }).found, true);
  assert.ok(viewsEqual(plain('yxz'), target));
});

console.log(`${passed} spec tests passed`);
