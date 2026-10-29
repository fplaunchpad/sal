import test from 'node:test';
import assert from 'node:assert/strict';
import { findWitness, allFinalViews, normaliseSpec } from '../src/index.js';
import { rgaList, gapList } from './listspec.js';

const ins = (id, ch, after = null, before = null) => ({ kind: 'ins', id, ch, after, before });
const del = (id) => ({ kind: 'del', id });
const ev = (key, deps, ...specOps) => ({ key, deps, specOps });

// e0 inserts a; ex inserts x after a and ey inserts y after a, concurrently.
// Order e0 ex ey: "ax", then y lands immediately after a: "ayx".
// Order e0 ey ex: "ay", then x lands immediately after a: "axy".
const siblings = [ev('e0', [], ins('a', 'a')), ev('ex', ['e0'], ins('x', 'x', 'a')), ev('ey', ['e0'], ins('y', 'y', 'a'))];

test('concurrent inserts after one anchor admit exactly both arrangements', () => {
  assert.deepEqual(findWitness(rgaList, siblings, 'axy'), { found: true, order: ['e0', 'ey', 'ex'] });
  assert.deepEqual(findWitness(rgaList, siblings, 'ayx'), { found: true, order: ['e0', 'ex', 'ey'] });
  assert.deepEqual(allFinalViews(rgaList, siblings), ['axy', 'ayx']);
  // Negative: x before its anchor is reachable by no order.
  const w = findWitness(rgaList, siblings, 'xay');
  assert.equal(w.found, false);
  assert.equal(w.reachableViews, 2);
  assert.notDeepEqual(allFinalViews(rgaList, siblings), ['axy']);
});

test('the order respects causality through transitive dependencies', () => {
  // e2 deletes a and depends on e1 only; e0 reaches it through e1.
  const evs = [ev('e2', ['e1'], del('a')), ev('e1', ['e0'], ins('b', 'b', 'a')), ev('e0', [], ins('a', 'a'))];
  assert.deepEqual(findWitness(rgaList, evs, 'b'), { found: true, order: ['e0', 'e1', 'e2'] });
  // Negative: a survives in no linear extension.
  assert.equal(findWitness(rgaList, evs, 'ab').found, false);
  assert.deepEqual(allFinalViews(rgaList, evs), ['b']);
});

test('a failed precondition prunes every order', () => {
  // The anchor q is never inserted: no order folds. Explored pairs: the empty
  // subset and {e0} with "a"; e1 fails from both.
  const evs = [ev('e0', [], ins('a', 'a')), ev('e1', [], ins('b', 'b', 'q'))];
  assert.deepEqual(allFinalViews(rgaList, evs), []);
  assert.deepEqual(findWitness(rgaList, evs, 'a'), { found: false, explored: 2, reachableViews: 0 });
  // Negative: the same history with an existing anchor folds.
  const ok = [ev('e0', [], ins('a', 'a')), ev('e1', ['e0'], ins('b', 'b', 'a'))];
  assert.deepEqual(allFinalViews(rgaList, ok), ['ab']);
});

test('malformed histories are rejected', () => {
  assert.throws(() => findWitness(rgaList, [ev('p', ['q'])], ''), /unknown dependency q/);
  assert.throws(() => findWitness(rgaList, [ev('p', ['q']), ev('q', ['p'])], ''), /causal cycle/);
  assert.throws(() => findWitness(rgaList, [ev('p', []), ev('p', [])], ''), /duplicate event key/);
  // Negative: the empty history is linearised by the empty order.
  assert.deepEqual(findWitness(rgaList, [], ''), { found: true, order: [] });
  assert.equal(findWitness(rgaList, [], 'a').found, false);
});

// One base event inserting n lower-case letters, then n concurrent events each
// inserting the capital after its lower-case letter. They commute, so the only
// final view is aAbB...; a deterministic search keeps one state per subset.
function wideHistory(n) {
  const lower = 'abcdefghijklmnopqrstuvwxyz'.slice(0, n);
  const base = [...lower].map((ch, i) => ins(ch, ch, i === 0 ? null : lower[i - 1]));
  return [ev('base', [], ...base), ...[...lower].map((ch, i) => ev('u' + i, ['base'], ins(ch.toUpperCase(), ch.toUpperCase(), ch)))];
}

test('the search is exact up to 20 events and refuses more', () => {
  const evs = wideHistory(19);
  assert.equal(evs.length, 20);
  const neg = findWitness(rgaList, evs, 'x');
  assert.equal(neg.found, false);
  assert.equal(neg.reachableViews, 1);
  // The empty subset plus base with any subset of the 19 others.
  assert.equal(neg.explored, 1 + 2 ** 19);
  const w = findWitness(rgaList, wideHistory(11), 'aAbBcCdDeEfFgGhHiIjJkK');
  assert.equal(w.found, true);
  assert.equal(w.order[0], 'base');
  assert.throws(() => findWitness(rgaList, wideHistory(20), ''), RangeError);
});

// p, d and j are concurrent head inserts; t is issued after p and j, between
// them. Gap rule: p, d, j take any order with p before j (t's precondition),
// and t lands strictly between p and j. Orders with p before j: pdj, pjd, dpj;
// t between p and j: ptdj, pdtj | ptjd | dptj.
const ptdj = [
  ev('p', [], ins('p', 'p')),
  ev('d', [], ins('d', 'd')),
  ev('j', [], ins('j', 'j')),
  ev('t', ['p', 'j'], ins('t', 't', 'p', 'j')),
];

test('a relational specification admits every placement in the gap', () => {
  assert.deepEqual(allFinalViews(gapList, ptdj), ['dptj', 'pdtj', 'ptdj', 'ptjd']);
  assert.equal(findWitness(gapList, ptdj, 'ptdj').found, true);
  // Negatives: t outside its gap, and j before p.
  assert.equal(findWitness(gapList, ptdj, 'tpdj').found, false);
  assert.equal(findWitness(gapList, ptdj, 'jtpd').found, false);
  // The one-sided rule admits a different set: t immediately after p.
  const left = ptdj.map((e) => ({ ...e, specOps: e.specOps.map((o) => ({ ...o, before: null })) }));
  assert.equal(findWitness(rgaList, left, 'pdtj').found, false);
});

test('a directed search agrees with the undirected one', () => {
  const withIds = (s) => [...s].map((ch) => ({ id: ch, ch }));
  for (const v of ['dptj', 'pdtj', 'ptdj', 'ptjd']) assert.equal(findWitness(gapList, ptdj, withIds(v)).found, true, v);
  for (const v of ['tpdj', 'pjtd', 'djpt']) assert.equal(findWitness(gapList, ptdj, withIds(v)).found, false, v);
  // Directed by the target, only the target's order is enumerated.
  assert.deepEqual(allFinalViews(gapList, ptdj, { target: withIds('ptdj') }), ['ptdj']);
});

test('a witness search over the state cap is truncated, not judged', () => {
  const evs = wideHistory(6).map((e) => ({ ...e, specOps: e.specOps.map((o) => ({ ...o })) }));
  const some = allFinalViews(gapList, evs)[0];
  const capped = findWitness(gapList, evs, some, { limit: 20 });
  assert.equal(capped.found, false);
  assert.equal(capped.truncated, true);
  assert.equal(capped.explored, 20);
  // The same search without a cap finds the witness; a view no order reaches is rejected, not truncated.
  assert.equal(findWitness(gapList, evs, some).found, true);
  const rejected = findWitness(gapList, evs, 'x');
  assert.equal(rejected.found, false);
  assert.notEqual(rejected.truncated, true);
  // A deterministic specification stays within one state per subset: 2^6 + 1 at most.
  assert.notEqual(findWitness(rgaList, wideHistory(6), 'x', { limit: 65 }).truncated, true);
  assert.equal(findWitness(rgaList, wideHistory(6), 'x', { limit: 10 }).truncated, true);
});

test('the undirected enumeration of a relational specification is capped', () => {
  const evs = wideHistory(6).map((e) => ({ ...e, specOps: e.specOps.map((o) => ({ ...o })) }));
  const capped = allFinalViews(gapList, evs, { limit: 20 });
  assert.equal(capped.truncated, true);
  assert.notEqual(allFinalViews(gapList, wideHistory(2)).truncated, true);
  // A deterministic specification is never capped.
  assert.notEqual(allFinalViews(rgaList, wideHistory(6), { limit: 20 }).truncated, true);
});

test('normaliseSpec fills defaults and rejects incomplete specifications', () => {
  const s = normaliseSpec(rgaList);
  assert.equal(s.relational, false);
  assert.equal(s.directs('ab'), false);
  assert.deepEqual(s.applyAll([], ins('a', 'a', 'q')), []);
  assert.equal(normaliseSpec(s), s);
  assert.equal(normaliseSpec(gapList).relational, true);
  assert.throws(() => normaliseSpec({ init: () => [] }), /lacks apply, view, serialise, viewKey/);
});
