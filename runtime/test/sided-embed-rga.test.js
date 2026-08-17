import test from 'node:test';
import assert from 'node:assert/strict';

import { Runtime } from '../src/runtime.js';
import { DistributedReplica } from '../src/replica.js';
import { sharedSidedPeritextExperimental } from '../src/datatypes/sidedPeritext.js';
import {
  sidedEmbedRGAExperimental,
  sharedSidedEmbedRGAExperimental,
} from '../src/datatypes/sidedEmbedRGA.js';

const ins = (id, el, anchorId = null) => ({ type: 'ins', id, el, anchorId });
const del = (id) => ({ type: 'del', id });

function fold(dt, ops) {
  let state = dt.init();
  const prepared = [];
  for (const op of ops) {
    const p = dt.prepare(state, op);
    prepared.push(p);
    state = dt.apply(state, p);
  }
  return { state, prepared };
}

test('sided mint decision is immutable and keeps a deleted successor chain', () => {
  for (const dt of [sidedEmbedRGAExperimental, sharedSidedEmbedRGAExperimental]) {
    let { state } = fold(dt, [ins(1, 'a'), ins(2, 'b', 1)]);
    state = dt.apply(state, del(2));
    const op = dt.prepare(state, ins(3, 'c', 1));
    assert.equal(op.side, 'L');
    assert.equal(op.parentId, 2);
    assert.deepEqual(op.chain, [['R', 1], ['R', 1], ['L', 1]]);
    state = dt.apply(state, op);
    assert.deepEqual(dt.read(state), ['a', 'c']);
  }
});

test('absolute and prefix-shared sided representations agree through fork/join', () => {
  const run = (dt) => {
    const rt = new Runtime(dt), a = rt.replica('a'), b = rt.replica('b');
    a.commit(ins(1, 'a'));
    a.sync(b);
    a.commit(ins(4, 'x', 1));
    b.commit(ins(2, 'y', 1));
    a.sync(b);
    a.commit(ins(7, 'p', 2));
    b.commit(ins(8, 'q', 4));
    a.sync(b);
    return { read: a.read(), ids: dt.readIds(a.head.state) };
  };
  assert.deepEqual(run(sidedEmbedRGAExperimental), run(sharedSidedEmbedRGAExperimental));
});

test('runtime stores prepared sided evidence in single and batched commits', () => {
  const rt = new Runtime(sidedEmbedRGAExperimental), r = rt.replica('r');
  r.commit(ins(1, 'a'));
  assert.equal(r.head.op.payload.side, 'R');
  const d = new DistributedReplica(sidedEmbedRGAExperimental, 'd');
  d.commitBatch([ins(1, 'a'), ins(2, 'b', 1)]);
  assert.deepEqual(d.head.op.payload.map((op) => op.side), ['R', 'R']);
  assert.deepEqual(d.read(), ['a', 'b']);
});

test('Peritext can use the experimental sided kernel without changing its API', () => {
  const dt = sharedSidedPeritextExperimental;
  const rt = new Runtime(dt), r = rt.replica('r');
  r.commit(ins(1, 'a'));
  r.commit(ins(2, 'b', 1));
  r.commit({ type: 'addMark', mid: 3, mtype: 'bold', value: true,
    startId: 1, endId: 2, startSide: 'before', endSide: 'after' });
  assert.deepEqual(r.read().map(({ char, marks }) => [char, marks.length]),
    [['a', 1], ['b', 1]]);
  assert.equal(r.head.parents.length, 1);
});
