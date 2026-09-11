import test from 'node:test';
import assert from 'node:assert/strict';
import { Runtime } from '../src/runtime.js';
import { orset } from '../src/datatypes/orset.js';
import { embedRGA } from '../src/datatypes/embedRGA.js';
import { keepSet } from '../src/gc.js';

test('gc genuinely prunes: linear history then sync collapses to one commit', () => {
  const rt = new Runtime(orset);
  const rA = rt.replica('A');
  const rB = rt.replica('B');
  for (let i = 0; i < 10; i++) rA.commit({ type: 'add', tag: `t${i}`, el: `e${i}` });
  rB.sync(rA); // fast-forward: both heads at rA's tip
  assert.equal(rt.dag.size, 11); // root + 10 op commits
  const { kept, dropped } = rt.gc();
  // both heads coincide: Keep = upward closure of that single head = itself
  assert.equal(kept, 1);
  assert.equal(dropped, 10);
  assert.equal(rt.dag.size, 1);
  assert.deepEqual(rt.dag.get(rA.head.id).parents, [],
    'retained head is a root-free parentless base');
  // the runtime keeps working after the prune
  assert.equal(rA.read().length, 10);
  rA.commit({ type: 'add', tag: 'post', el: 'post' });
  rB.sync(rA);
  assert.equal(rB.read().length, 11);
});

test('gc keeps the divergence cone: MCA of live branches and everything above it', () => {
  const rt = new Runtime(embedRGA);
  const rA = rt.replica('A');
  const rB = rt.replica('B');
  rA.commit({ type: 'ins', id: 1, el: 1, anchorId: null });
  rA.commit({ type: 'ins', id: 2, el: 2, anchorId: null });
  rB.sync(rA); // shared fork point f = rA.head
  const fork = rA.head.id;
  rA.commit({ type: 'ins', id: 3, el: 3, anchorId: 1 });
  rB.commit({ type: 'del', id: 2 });
  const keep = keepSet(rt.dag, [rA.head.id, rB.head.id]);
  assert.ok(keep.has(fork));                       // the pairwise MCA
  assert.ok(keep.has(rA.head.id) && keep.has(rB.head.id)); // i = j pairs
  const { dropped } = rt.gc();
  assert.equal(dropped, 2);                        // root + the ins-1 commit
  assert.equal(rt.dag.size, 3);                    // fork + two branch tips
  // post-gc merge still finds the (kept) LCA and agrees with a no-gc control
  const control = new Runtime(embedRGA);
  const cA = control.replica('A');
  const cB = control.replica('B');
  cA.commit({ type: 'ins', id: 1, el: 1, anchorId: null });
  cA.commit({ type: 'ins', id: 2, el: 2, anchorId: null });
  cB.sync(cA);
  cA.commit({ type: 'ins', id: 3, el: 3, anchorId: 1 });
  cB.commit({ type: 'del', id: 2 });
  rA.sync(rB);
  cA.sync(cB);
  assert.deepEqual(rA.read(), cA.read());
  assert.deepEqual(rA.read(), [1, 3]);
});

test('open-membership gate: no new replicas once the root is pruned', () => {
  const rt = new Runtime(orset);
  const rA = rt.replica('A');
  rA.commit({ type: 'add', tag: 't', el: 'x' });
  rt.gc(); // prunes the root (single head keeps only itself)
  assert.throws(() => rt.replica('late'), /open-membership/);
});
