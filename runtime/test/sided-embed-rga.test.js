import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';

import { Runtime } from '../src/runtime.js';
import { DistributedReplica } from '../src/replica.js';
import { sharedSidedPeritextExperimental } from '../src/datatypes/sidedPeritext.js';
import {
  sidedEmbedRGAExperimental,
  sharedSidedEmbedRGAExperimental,
} from '../src/datatypes/sidedEmbedRGA.js';
import { unifiedSidedEmbedRGAExperimental } from '../src/datatypes/unifiedSidedEmbedRGA.js';

const ins = (id, el, anchorId = null) => ({ type: 'ins', id, el, anchorId });
const del = (id) => ({ type: 'del', id });
const fromIntent = ([tag, id, anchor]) => tag === 'ins'
  ? ins(id, String(id), anchor === 0 ? null : anchor) : del(id);

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
  for (const dt of [sidedEmbedRGAExperimental, sharedSidedEmbedRGAExperimental,
    unifiedSidedEmbedRGAExperimental]) {
    let { state } = fold(dt, [ins(1, 'a'), ins(2, 'b', 1)]);
    state = dt.apply(state, del(2));
    const op = dt.prepare(state, ins(3, 'c', 1));
    assert.equal(op.side, 'L');
    assert.equal(op.parentId, 2);
    assert.equal('chain' in op, false);
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

test('merge traversal retains a live descendant of a branch-deleted parent', () => {
  const dt = sharedSidedEmbedRGAExperimental;
  const l = fold(dt, [ins(1, 'a')]).state;
  let a = l;
  for (const raw of [ins(2, 'b', 1), ins(3, 'c', 2), del(2)]) {
    const op = raw.type === 'ins' ? dt.prepare(a, raw) : raw;
    a = dt.apply(a, op);
  }
  const b = dt.apply(l, dt.prepare(l, ins(4, 'd', 1)));
  const merged = dt.merge3(l, a, b);
  assert.equal(merged.live.size, 3);
  assert.deepEqual(new Set(dt.readIds(merged)), new Set([1, 3, 4]));
});

test('JavaScript sided kernel is lockstep with the full-policy Fugue oracle', () => {
  const raw = execFileSync('python3', ['../whiteboard/litmus/js_sided_oracle.py'],
    { cwd: new URL('..', import.meta.url), encoding: 'utf8' });
  const cases = JSON.parse(raw);
  for (const dt of [sidedEmbedRGAExperimental, sharedSidedEmbedRGAExperimental,
    unifiedSidedEmbedRGAExperimental]) {
    for (const c of cases) {
      if (c.kind === 'seq') {
        const { state } = fold(dt, c.ops.map(fromIntent));
        assert.deepEqual(dt.readIds(state), c.read, `${dt.name}: ${c.name}`);
      } else {
        const l = fold(dt, c.lca.map(fromIntent)).state;
        const branch = (ops) => {
          let state = l;
          for (const rawOp of ops.map(fromIntent)) {
            const op = dt.prepare(state, rawOp);
            state = dt.apply(state, op);
          }
          return state;
        };
        const merged = dt.merge3(l, branch(c.a), branch(c.b));
        assert.deepEqual(dt.readIds(merged), c.read, `${dt.name}: ${c.name}`);
      }
    }
  }
  const l19 = cases.find((c) => c.name.startsWith('L19'));
  assert.deepEqual(l19.read, [50, 30, 10, 61, 41, 21, 1]);
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

test('candidate snapshots round-trip and remain editable', () => {
  for (const dt of [sidedEmbedRGAExperimental, sharedSidedEmbedRGAExperimental]) {
    const original = fold(dt, [ins(1, 'a'), ins(2, 'b', 1), ins(3, 'c', 1)]).state;
    let restored = dt.decodeState(JSON.parse(JSON.stringify(dt.encodeState(original))));
    assert.equal(dt.fingerprint(restored), dt.fingerprint(original));
    const op = dt.prepare(restored, ins(4, 'd', 2));
    restored = dt.apply(restored, op);
    assert.deepEqual(dt.read(restored), ['a', 'c', 'b', 'd']);
    const bytes = dt.encodeSnapshot(original, { validate: true });
    restored = dt.decodeSnapshot(bytes);
    assert.equal(dt.fingerprint(restored), dt.fingerprint(original));
  }
});

test('binary sided snapshot preserves variable-width UTF-8 elements', () => {
  const dt = sharedSidedEmbedRGAExperimental;
  const original = fold(dt, [ins(1, 'é'), ins(2, '🙂', 1), ins(3, 'x', 2)]).state;
  const restored = dt.decodeSnapshot(dt.encodeSnapshot(original));
  assert.deepEqual(dt.read(restored), ['é', '🙂', 'x']);
});

test('unified-map candidate stays lockstep with split-map sided oracle', () => {
  const run = (dt) => {
    const rt = new Runtime(dt), a = rt.replica('a'), b = rt.replica('b');
    a.commit(ins(1, 'a')); a.sync(b);
    a.commit(ins(4, 'x', 1)); a.commit(ins(6, 'z', 4)); a.commit(del(4));
    b.commit(ins(2, 'y', 1)); b.commit(ins(3, 'q', 2));
    a.sync(b); a.commit(ins(8, 'w', 3)); b.commit(ins(9, 'v', 6)); a.sync(b);
    return dt.readIds(a.head.state);
  };
  assert.deepEqual(run(unifiedSidedEmbedRGAExperimental), run(sharedSidedEmbedRGAExperimental));
  let s = unifiedSidedEmbedRGAExperimental.init();
  for (const raw of [ins(1, 'é'), ins(2, '🙂', 1), ins(3, 'x', 2)]) {
    const op = unifiedSidedEmbedRGAExperimental.prepare(s, raw);
    s = unifiedSidedEmbedRGAExperimental.apply(s, op);
  }
  const restored = unifiedSidedEmbedRGAExperimental.decodeSnapshot(
    unifiedSidedEmbedRGAExperimental.encodeSnapshot(s));
  assert.deepEqual(unifiedSidedEmbedRGAExperimental.read(restored), ['é', '🙂', 'x']);
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
