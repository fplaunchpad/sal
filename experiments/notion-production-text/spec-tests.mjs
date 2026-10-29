/**
 * Hand-derived tests of the specification (ra-pbt/instances/notion-production-text/spec.js).
 * Every block asserts the derived value and, with notEqual, the tempting
 * wrong one. Expected values are written out by hand, not computed by the
 * module under test. The specification does not load the Notion library.
 *
 * Run: node experiments/notion-production-text/spec-tests.mjs
 */
import assert from 'node:assert/strict';
import { applyAll, initial, viewWithIds, viewKey, localEdit, parseView, renderView, anchorPosition } from '../../ra-pbt/instances/notion-production-text/spec.js';

const A = ['A', 1];
const B = ['A', 2];
const C = ['A', 3];
const D = ['B', 4];
const X = ['B', 5];
const Y = ['C', 6];

let blocks = 0;
const block = (name, fn) => {
  fn();
  blocks++;
  console.log('ok  ' + name);
};

/** Applies operations in order, requiring exactly one successor each (deterministic steps). */
function run(ops, opts, from = initial()) {
  let s = from;
  for (const op of ops) {
    const next = applyAll(s, op, opts);
    assert.equal(next.length, 1, `expected one successor for ${JSON.stringify(op)}, got ${next.length}`);
    s = next[0];
  }
  return s;
}
const ins = (id, ch, origin = null, rightOrigin = null, bold = false) => ({ kind: 'insert', id, ch, origin, rightOrigin, bold });
const del = (...ids) => ({ kind: 'delete', ids });
const ann = (id, start, end, value, left, right) => ({ kind: 'annotate', id, start, end, value, left, right });
const before = (id) => ({ id, anchor: 'before' });
const after = (id) => ({ id, anchor: 'after' });
const shown = (s, reading) => renderView(viewWithIds(s, reading));
const abc = [ins(A, 'a'), ins(B, 'b', A), ins(C, 'c', B)];
const allShown = (states, reading) => states.map((s) => shown(s, reading)).sort();

block('views: rendering and parsing are inverse, bold marked by *', () => {
  assert.equal(renderView(parseView('a*bc*')), 'a*bc*');
  assert.deepEqual(parseView('a*b'), [{ ch: 'a', bold: true }, { ch: 'b', bold: false }]);
  assert.notDeepEqual(parseView('a*b'), [{ ch: 'a', bold: true }, { ch: 'b', bold: true }]);
  assert.notEqual(viewKey(parseView('ab')), viewKey(parseView('a*b')));
});

block('insertion: a character with origin a and right neighbour b, over a tombstone d between them', () => {
  // a d(deleted) b: the gap rule admits x before or after d; left puts it right after a; both right before b.
  const s = run([ins(A, 'a'), ins(D, 'd', A), ins(B, 'b', D), del(D)], {});
  assert.equal(shown(s), 'ab');
  const op = ins(X, 'x', A, B);
  const gap = applyAll(s, op, { rule: 'gap' });
  assert.equal(gap.length, 2);
  assert.deepEqual(gap.map((t) => t.chars.map((c) => c.ch).join('')), ['axdb', 'adxb']);
  assert.deepEqual(applyAll(s, op, { rule: 'left' }).map((t) => t.chars.map((c) => c.ch).join('')), ['axdb']);
  assert.deepEqual(applyAll(s, op, { rule: 'both' }).map((t) => t.chars.map((c) => c.ch).join('')), ['adxb']);
  assert.notEqual(gap.length, 1);
});

block('insertion: the gap rule keeps the order of characters the issuer saw', () => {
  // a b; x recorded with origin a and right neighbour b, so x never lands after b or before a.
  const s = run([ins(A, 'a'), ins(B, 'b', A)], {});
  const out = applyAll(s, ins(X, 'x', A, B), { rule: 'gap' }).map((t) => shown(t));
  assert.deepEqual(out, ['axb']);
  assert.ok(!out.includes('abx') && !out.includes('xab'));
});

block('insertion: preconditions (absent origin, right neighbour before origin, duplicate id)', () => {
  const s = run([ins(A, 'a'), ins(B, 'b', A)], {});
  assert.deepEqual(applyAll(s, ins(X, 'x', C, null), {}), []);
  assert.deepEqual(applyAll(s, ins(X, 'x', B, A), {}), []);
  assert.deepEqual(applyAll(s, ins(A, 'z', null, null), {}), []);
  assert.notDeepEqual(applyAll(s, ins(X, 'x', B, null), {}), []);
});

block('anchored: bold from before a to before c covers a and b, not c', () => {
  const s = run([...abc, ann(X, before(A), before(C), true, A, B)], {});
  assert.equal(shown(s), 'a*b*c');
  assert.notEqual(shown(s), 'a*b*c*');
  assert.notEqual(shown(s), 'ab*c');
});

block('anchored: a character inserted later inside the range is covered; one at the left boundary is not', () => {
  // range [before a, before c); x inserted after b (inside), y at the head (before a's before anchor).
  const s = run([...abc, ann(X, before(A), before(C), true, A, B), ins(D, 'x', B, C), ins(Y, 'y', null, A)], {});
  assert.equal(shown(s), 'ya*b*x*c');
  assert.notEqual(shown(s), 'ya*b*xc');
  assert.notEqual(shown(s), 'y*a*b*x*c');
});

block('interval: the same history carries the issuer’s bold for inserted characters', () => {
  // interval reading: the annotation marks a..b when applied; x was issued plain, so stays plain.
  const s = run([...abc, ann(X, before(A), before(C), true, A, B), ins(D, 'x', B, C, false), ins(Y, 'y', null, A, false)], { reading: 'interval' });
  assert.equal(shown(s, 'interval'), 'ya*b*xc');
  assert.notEqual(shown(s, 'interval'), 'ya*b*x*c');
});

block('interval: a character inserted before the annotation applies, between its endpoints, is covered', () => {
  const s = run([...abc, ins(D, 'x', A, B, false), ann(X, before(A), before(C), true, A, B)], { reading: 'interval' });
  assert.equal(shown(s, 'interval'), 'a*x*b*c');
  assert.notEqual(shown(s, 'interval'), 'a*xb*c');
});

block('anchored: the last-applied annotation wins, in either order', () => {
  const add = ann(X, before(A), before(C), true, A, B);
  const remove = ann(Y, before(B), after(C), null, B, C);
  const addFirst = run([...abc, add, remove], {});
  const removeFirst = run([...abc, remove, add], {});
  assert.equal(shown(addFirst), 'a*bc');
  assert.equal(shown(removeFirst), 'a*b*c');
  assert.notEqual(shown(addFirst), shown(removeFirst));
});

block('anchored: after and before anchors, the text ends and a tombstone anchor', () => {
  // after a .. end covers b and c; start .. before b covers a; an end anchor on deleted b still bounds the range.
  assert.equal(shown(run([...abc, ann(X, after(A), { id: 'end', anchor: 'before' }, true, B, C)], {})), 'ab*c*');
  assert.notEqual(shown(run([...abc, ann(X, after(A), { id: 'end', anchor: 'before' }, true, B, C)], {})), 'a*b*c*');
  assert.equal(shown(run([...abc, ann(X, { id: 'start', anchor: 'after' }, before(B), true, A, A)], {})), 'a*bc');
  assert.equal(shown(run([...abc, ann(X, before(A), before(B), true, A, A), del(B)], {})), 'a*c');
  assert.notEqual(shown(run([...abc, ann(X, before(A), before(B), true, A, A), del(B)], {})), 'a*c*');
});

block('anchored: anchor positions and preconditions', () => {
  const s = run(abc, {});
  assert.equal(anchorPosition(s.chars, before(A)), -1);
  assert.equal(anchorPosition(s.chars, after(C)), 5);
  assert.equal(anchorPosition(s.chars, { id: 'end', anchor: 'before' }), 5);
  assert.notEqual(anchorPosition(s.chars, before(B)), anchorPosition(s.chars, after(B)));
  assert.equal(anchorPosition(s.chars, { id: 'end', anchor: 'after' }), null);
  assert.deepEqual(applyAll(s, ann(X, before(D), before(C), true, A, B), {}), []);
  assert.deepEqual(applyAll(s, ann(X, before(C), before(A), true, A, B), {}), []);
  assert.deepEqual(applyAll(s, ann(X, after(B), before(C), true, C, C), {}), []);
  assert.notDeepEqual(applyAll(s, ann(X, before(B), before(C), true, B, B), {}), []);
});

block('delete: by identity, idempotent, precondition on presence', () => {
  const once = run([...abc, del(B)], {});
  const twice = run([...abc, del(B), del(B)], {});
  assert.equal(shown(once), 'ac');
  assert.equal(shown(twice), 'ac');
  assert.notEqual(shown(once), 'ab');
  assert.deepEqual(applyAll(once, del(X), {}), []);
});

block('local meaning: positional insertion is plain; the inherit variant takes the left neighbour’s bold', () => {
  const v = parseView('a*b');
  assert.equal(renderView(localEdit(v, { kind: 'insert', index: 1, text: 'xy' })), 'a*xyb');
  assert.equal(renderView(localEdit(v, { kind: 'insert', index: 1, text: 'xy' }, 'inherit')), 'a*x*y*b');
  assert.equal(renderView(localEdit(v, { kind: 'insert', index: 0, text: 'x' }, 'inherit')), 'xa*b');
  assert.notEqual(renderView(localEdit(v, { kind: 'insert', index: 0, text: 'x' }, 'inherit')), 'x*a*b');
  assert.equal(renderView(localEdit(v, { kind: 'insert', index: 2, text: 'x' }, 'inherit')), 'a*bx');
});

block('local meaning: bold toggles (remove when all selected are bold), delete removes exactly the range', () => {
  const v = parseView('a*b*c');
  assert.equal(renderView(localEdit(v, { kind: 'bold', start: 0, end: 2 })), 'abc');
  assert.notEqual(renderView(localEdit(v, { kind: 'bold', start: 0, end: 2 })), 'a*b*c');
  assert.equal(renderView(localEdit(v, { kind: 'bold', start: 1, end: 3 })), 'a*b*c*');
  assert.notEqual(renderView(localEdit(v, { kind: 'bold', start: 1, end: 3 })), 'a*bc');
  assert.equal(renderView(localEdit(v, { kind: 'delete', start: 1, end: 2 })), 'a*c');
  assert.notEqual(renderView(localEdit(v, { kind: 'delete', start: 1, end: 2 })), 'a*b*');
  assert.throws(() => localEdit(v, { kind: 'delete', start: 2, end: 4 }), RangeError);
});

console.log(`${blocks} blocks passed`);
