import test from 'node:test';
import assert from 'node:assert/strict';
import { Dag } from '../src/dag.js';
import { mcas, lca, CrissCrossError } from '../src/lca.js';

const op = (n) => ({ replica: 'r', seq: n, payload: n });

test('dag: ancestorSet is the reflexive ancestor closure', () => {
  const d = new Dag();
  const root = d.add({ state: 0 });
  const a = d.add({ parents: [root.id], op: op(0), state: 1 });
  const b = d.add({ parents: [root.id], op: op(1), state: 2 });
  const m = d.add({ parents: [a.id, b.id], state: 3 }); // merge commit: op null
  assert.deepEqual(d.ancestorSet(root.id), new Set([root.id]));
  assert.deepEqual(d.ancestorSet(a.id), new Set([a.id, root.id]));
  assert.deepEqual(d.ancestorSet(m.id), new Set([m.id, a.id, b.id, root.id]));
});

test('dag: events = ops along the ancestor closure (merge/root contribute none)', () => {
  const d = new Dag();
  const root = d.add({ state: 0 });
  const a = d.add({ parents: [root.id], op: op(0), state: 1 });
  const b = d.add({ parents: [root.id], op: op(1), state: 2 });
  const m = d.add({ parents: [a.id, b.id], state: 3 });
  assert.deepEqual(new Set(d.events(m.id).map((o) => o.seq)), new Set([0, 1]));
  assert.deepEqual(d.events(root.id), []);
});

test('dag: isAncestor subsumption check, both directions and reflexive', () => {
  const d = new Dag();
  const root = d.add({ state: 0 });
  const a = d.add({ parents: [root.id], op: op(0), state: 1 });
  const b = d.add({ parents: [a.id], op: op(1), state: 2 });
  const c = d.add({ parents: [root.id], op: op(2), state: 3 }); // sibling branch
  assert.equal(d.isAncestor(root.id, b.id), true);
  assert.equal(d.isAncestor(a.id, b.id), true);
  assert.equal(d.isAncestor(b.id, a.id), false);
  assert.equal(d.isAncestor(a.id, a.id), true);
  assert.equal(d.isAncestor(c.id, b.id), false);
  assert.equal(d.isAncestor(b.id, c.id), false);
});

test('dag: unknown parents and pruned lookups throw', () => {
  const d = new Dag();
  assert.throws(() => d.add({ parents: ['nope'], state: 0 }), /unknown parent/);
  assert.throws(() => d.get('nope'), /no such commit/);
});

test('lca: unique MCA on a diamond is returned', () => {
  const d = new Dag();
  const root = d.add({ state: 0 });
  const f = d.add({ parents: [root.id], op: op(0), state: 1 }); // fork point
  const a = d.add({ parents: [f.id], op: op(1), state: 2 });
  const b = d.add({ parents: [f.id], op: op(2), state: 3 });
  assert.equal(lca(d, a.id, b.id), f.id);
  assert.deepEqual(mcas(d, a.id, b.id), [f.id]);
  // reflexive / subsumed cases
  assert.equal(lca(d, a.id, a.id), a.id);
  assert.equal(lca(d, f.id, a.id), f.id);
});

test('lca: criss-cross yields ALL maximal common ancestors and lca throws the #90 gate', () => {
  // root -> x, y ; two rival merges m1, m2 both with parents {x, y};
  // heads c1 (on m1) and c2 (on m2). CA(c1,c2) = {root, x, y}; maximal = {x, y}.
  const d = new Dag();
  const root = d.add({ state: 0 });
  const x = d.add({ parents: [root.id], op: op(0), state: 1 });
  const y = d.add({ parents: [root.id], op: op(1), state: 2 });
  const m1 = d.add({ parents: [x.id, y.id], state: 3 });
  const m2 = d.add({ parents: [x.id, y.id], state: 4 });
  const c1 = d.add({ parents: [m1.id], op: op(2), state: 5 });
  const c2 = d.add({ parents: [m2.id], op: op(3), state: 6 });
  assert.deepEqual(new Set(mcas(d, c1.id, c2.id)), new Set([x.id, y.id]));
  assert.throws(() => lca(d, c1.id, c2.id), CrissCrossError);
  assert.throws(() => lca(d, c1.id, c2.id), /#90/); // message points at the task
  assert.throws(() => lca(d, c1.id, c2.id), /virtual LCA/i);
});

test('lca: no common ancestor throws a plain Error, not a silent pick', () => {
  const d = new Dag();
  const r1 = d.add({ state: 0 });
  const r2 = d.add({ state: 1 }); // second root: disjoint history
  assert.throws(() => lca(d, r1.id, r2.id), /no common ancestor/);
});
