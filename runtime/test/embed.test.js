// Embedded-chain RGA litmus fixtures.
//
// FIXTURE PROVENANCE: every expected read below was extracted by RUNNING
// the Python model, NOT derived from this port:
//
//   cd whiteboard/litmus && python3 - <<'EOF'
//   from embed_tree import EmbedTree, EmbedTreeCode
//   for D in (EmbedTree(), EmbedTreeCode()):
//       s = D.init()
//       for it in (('ins',1,0),('ins',2,0),('ins',3,1)): s = D.apply(s, it)
//       print(D.read(s)); print(D.read(D.apply(s, ('del',1))))
//       Ls = D.apply(D.init(), ('ins',1,0))
//       A  = D.apply(D.apply(D.copy(Ls),('ins',5,1)),('del',1))
//       B  = D.apply(D.copy(Ls),('ins',2,0))
//       print(D.read(D.merge(D.copy(Ls),D.copy(A),D.copy(B))))
//       A2 = D.apply(D.apply(D.copy(Ls),('del',1)),('ins',5,0))
//       print(D.read(D.merge(D.copy(Ls),D.copy(A2),D.copy(B))))
//   EOF
//
// Both model variants (EmbedTree fractions, EmbedTreeCode delta-code) agree:
//   L1 pre-del [2, 1, 3]; post-del [2, 3]; world1 [2, 5]; world2 [5, 2].
// If this port disagrees with these fixtures, the PORT is wrong.

import test from 'node:test';
import assert from 'node:assert/strict';
import { embedRGA as D } from '../src/datatypes/embedRGA.js';
import { Runtime } from '../src/runtime.js';

test('L1 delete-reorder, datatype level: [b,a,c] then del a -> [b,c]', () => {
  let s = D.init();
  s = D.apply(s, { type: 'ins', id: 1, el: 'a', anchorId: null });
  s = D.apply(s, { type: 'ins', id: 2, el: 'b', anchorId: null });
  s = D.apply(s, { type: 'ins', id: 3, el: 'c', anchorId: 1 });
  assert.deepEqual(D.read(s), ['b', 'a', 'c']);   // Python: [2, 1, 3]
  s = D.apply(s, { type: 'del', id: 1 });
  assert.deepEqual(D.read(s), ['b', 'c']);        // Python: [2, 3]
});

test('L1 through the runtime (single replica)', () => {
  const rt = new Runtime(D);
  const r = rt.replica('A');
  r.commit({ type: 'ins', id: 1, el: 'a', anchorId: null });
  r.commit({ type: 'ins', id: 2, el: 'b', anchorId: null });
  r.commit({ type: 'ins', id: 3, el: 'c', anchorId: 1 });
  assert.deepEqual(r.read(), ['b', 'a', 'c']);
  r.commit({ type: 'del', id: 1 });
  assert.deepEqual(r.read(), ['b', 'c']);
});

// The sibling-splice fooling pair: same final live sets {2, 5}, opposite
// orders, distinguished ONLY by the dead ancestor 1's coordinate prefix.
test('fooling-pair world 1: A = ins 5<-1; del 1, B = ins 2<-root  =>  [2, 5]', () => {
  const rt = new Runtime(D);
  const rA = rt.replica('A');
  const rB = rt.replica('B');
  rA.commit({ type: 'ins', id: 1, el: 1, anchorId: null }); // the shared LCA
  rB.sync(rA);                                              // fast-forward
  rA.commit({ type: 'ins', id: 5, el: 5, anchorId: 1 });    // 5 keeps 1's prefix
  rA.commit({ type: 'del', id: 1 });
  rB.commit({ type: 'ins', id: 2, el: 2, anchorId: null });
  rA.sync(rB);                                              // real merge via LCA
  assert.deepEqual(rA.read(), [2, 5]);                      // Python: [2, 5]
  assert.deepEqual(rB.read(), [2, 5]);
});

test('fooling-pair world 2: A = del 1; ins 5<-root, same B  =>  [5, 2]', () => {
  const rt = new Runtime(D);
  const rA = rt.replica('A');
  const rB = rt.replica('B');
  rA.commit({ type: 'ins', id: 1, el: 1, anchorId: null });
  rB.sync(rA);
  rA.commit({ type: 'del', id: 1 });
  rA.commit({ type: 'ins', id: 5, el: 5, anchorId: null }); // root-anchored: no prefix
  rB.commit({ type: 'ins', id: 2, el: 2, anchorId: null });
  rA.sync(rB);
  assert.deepEqual(rA.read(), [5, 2]);                      // Python: [5, 2]
  assert.deepEqual(rB.read(), [5, 2]);
});

test('fast-forward sync adds no merge commit; symmetric sync is idempotent', () => {
  const rt = new Runtime(D);
  const rA = rt.replica('A');
  const rB = rt.replica('B');
  rA.commit({ type: 'ins', id: 1, el: 'a', anchorId: null });
  const size = rt.dag.size;
  rB.sync(rA);
  assert.equal(rt.dag.size, size);                // fast-forward, no new commit
  assert.equal(rB.head.id, rA.head.id);
  rA.sync(rB);                                    // equal heads: no-op
  assert.equal(rt.dag.size, size);
});

test('honesty preconditions throw: dead anchor, non-positive delta, duplicate id', () => {
  let s = D.init();
  s = D.apply(s, { type: 'ins', id: 3, el: 'a', anchorId: null });
  assert.throws(() => D.apply(s, { type: 'ins', id: 9, el: 'x', anchorId: 7 }), /not live/);
  assert.throws(() => D.apply(s, { type: 'ins', id: 2, el: 'x', anchorId: 3 }), /positive/);
  assert.throws(() => D.apply(s, { type: 'ins', id: 3, el: 'x', anchorId: null }), /duplicate/);
  assert.deepEqual(D.read(D.apply(s, { type: 'del', id: 99 })), ['a']); // absent del: no-op
});
