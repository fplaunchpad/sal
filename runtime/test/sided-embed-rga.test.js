import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

import { Runtime } from '../src/runtime.js';
import { DistributedReplica } from '../src/replica.js';
import { syncReplicas } from '../src/replica.js';
import { peritext } from '../src/datatypes/peritext.js';
import { sharedSidedPeritextExperimental, sidedPeritextReleaseCandidate } from '../src/datatypes/sidedPeritext.js';
import {
  sidedEmbedRGAExperimental,
  sharedSidedEmbedRGAExperimental,
} from '../src/datatypes/sidedEmbedRGA.js';
import { unifiedSidedEmbedRGAExperimental } from '../src/datatypes/unifiedSidedEmbedRGA.js';
import { liveGapSidedEmbedRGA } from '../src/datatypes/liveGapSidedEmbedRGA.js';

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

test('JavaScript sided kernel matches the reviewed Fugue conformance corpus', () => {
  const cases = JSON.parse(readFileSync(
    new URL('fixtures/fugue-conformance.json', import.meta.url), 'utf8'));
  for (const dt of [sidedEmbedRGAExperimental, sharedSidedEmbedRGAExperimental,
    unifiedSidedEmbedRGAExperimental, liveGapSidedEmbedRGA]) {
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

test('unified release candidate survives randomized split-oracle fork/join and recovery', () => {
  let seed = 0x51ded;
  const rnd = () => { seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; return seed / 2 ** 32; };
  for (let trial = 0; trial < 40; trial++) {
    const make = (dt) => { const rt = new Runtime(dt); return { dt, a: rt.replica('a'), b: rt.replica('b') }; };
    let x = make(sharedSidedEmbedRGAExperimental), y = make(unifiedSidedEmbedRGAExperimental), next = 1;
    for (let step = 0; step < 80; step++) {
      const side = rnd() < 0.5 ? 'a' : 'b', sync = rnd() < 0.18;
      if (sync) { x.a.sync(x.b); y.a.sync(y.b); }
      else {
        const ids = x.dt.readIds(x[side].head.state);
        if (ids.length && rnd() < 0.28) {
          const id = ids[Math.floor(rnd() * ids.length)]; x[side].commit(del(id)); y[side].commit(del(id));
        } else {
          const pos = Math.floor(rnd() * (ids.length + 1));
          const op = ins(next++, String.fromCharCode(97 + (next % 26)), pos ? ids[pos - 1] : null);
          x[side].commit(op); y[side].commit(op);
        }
      }
      assert.deepEqual(y.dt.readIds(y.a.head.state), x.dt.readIds(x.a.head.state), `trial ${trial} step ${step} a`);
      assert.deepEqual(y.dt.readIds(y.b.head.state), x.dt.readIds(x.b.head.state), `trial ${trial} step ${step} b`);
      if (step === 40) {
        const restored = y.dt.decodeSnapshot(y.dt.encodeSnapshot(y.a.head.state));
        assert.deepEqual(y.dt.readIds(restored), y.dt.readIds(y.a.head.state));
      }
    }
    x.a.sync(x.b); y.a.sync(y.b);
    assert.deepEqual(y.dt.readIds(y.a.head.state), x.dt.readIds(x.a.head.state));
  }
});

test('unified policy GC drops a settled irrelevant branch leaf and preserves future mints', () => {
  const dt = unifiedSidedEmbedRGAExperimental, rt = new Runtime(dt);
  const a = rt.replica('a'), b = rt.replica('b');
  a.commit(ins(1, 'a')); a.sync(b);
  a.commit(ins(2, 'b', 1)); b.commit(ins(3, 'c', 1)); a.sync(b);
  const ids = dt.readIds(a.head.state), victim = ids.find((id) => id !== 1 &&
    a.head.state.rootGap.succId !== id && a.head.state.nodes.get(1).gap.succId !== id) ?? 2;
  a.commit(del(victim)); b.sync(a);
  const before = a.head.state;
  const { state: compacted, stats } = dt.compact(before,
    { settledIds: new Set([1, 2, 3]), settledDelIds: new Set([victim]) });
  assert.ok(stats.recordsDropped >= 1);
  assert.deepEqual(dt.readIds(compacted), dt.readIds(before));
  const raw = ins(4, 'd', 1);
  const x = dt.apply(before, dt.prepare(before, raw));
  const y = dt.apply(compacted, dt.prepare(compacted, raw));
  assert.deepEqual(dt.readIds(y), dt.readIds(x));
});

test('unified sided GC fires only with frontier evidence and round-trips its epoch state', () => {
  const dt = unifiedSidedEmbedRGAExperimental;
  const a = new DistributedReplica(dt, 'A'), b = new DistributedReplica(dt, 'B');
  a.register('B'); b.register('A');
  a.commit(ins(1, 'a')); syncReplicas(a, b);
  a.commit(ins(2, 'b', 1)); b.commit(ins(3, 'c', 1)); syncReplicas(a, b);
  const g = a.head.state.nodes.get(1).gap;
  const victim = [2, 3].find((id) => id !== g.succId);
  a.commit(del(victim));
  assert.equal(a.compactStable().compacted, false, 'must refuse before B acknowledges the delete frontier');
  syncReplicas(a, b);
  b.commit(ins(4, 'd', 1)); syncReplicas(a, b);
  const before = a.read(), result = a.compactStable();
  assert.equal(result.compacted, true);
  assert.ok(result.stats.recordsDropped > 0);
  assert.deepEqual(a.read(), before);
  const restored = dt.decodeState(dt.encodeState(a.head.state));
  assert.deepEqual(dt.read(restored), before);
});

test('offline old-epoch sided replica returns after certified policy GC', () => {
  const dt = unifiedSidedEmbedRGAExperimental;
  const a = new DistributedReplica(dt, 'A'), b = new DistributedReplica(dt, 'B'),
    c = new DistributedReplica(dt, 'C');
  for (const x of [a, b, c]) for (const name of ['A', 'B', 'C']) x.register(name);
  a.commit(ins(1, 'a')); syncReplicas(a, b); syncReplicas(a, c);
  a.commit(ins(2, 'b', 1)); b.commit(ins(3, 'c', 1));
  syncReplicas(a, b); syncReplicas(a, c); syncReplicas(b, c);
  const victim = [2, 3].find((id) => id !== a.head.state.nodes.get(1).gap.succId);
  a.commit(del(victim)); syncReplicas(a, b); syncReplicas(a, c);
  b.commit(ins(4, 'd', 1)); c.commit(ins(5, 'e', 1));
  syncReplicas(a, b); syncReplicas(a, c); // A now has post-delete evidence from B and C.
  const compacted = a.compactStable();
  assert.equal(compacted.compacted, true);
  assert.ok(compacted.stats.recordsDropped > 0);
  assert.equal(dt.fingerprint(dt.decodeState(dt.encodeState(a.head.state))),
    dt.fingerprint(a.head.state), 'compaction wire state must be fingerprint-stable');
  // C remains in the parent epoch and mints a future operation there.
  const anchor = dt.readIds(c.head.state).at(-1) ?? 1;
  c.commit(ins(6, 'f', anchor));
  syncReplicas(a, c);
  assert.deepEqual(a.read(), c.read());
  assert.ok(a.read().includes('f'));
});

test('Peritext can use the experimental sided kernel without changing its API', () => {
  for (const dt of [sharedSidedPeritextExperimental, sidedPeritextReleaseCandidate, peritext]) {
    const rt = new Runtime(dt), r = rt.replica('r');
    r.commit(ins(1, 'a'));
    r.commit(ins(2, 'b', 1));
    r.commit({ type: 'addMark', mid: 3, mtype: 'bold', value: true,
      startId: 1, endId: 2, startSide: 'before', endSide: 'after' });
    assert.deepEqual(r.read().map(({ char, marks }) => [char, marks.length]),
      [['a', 1], ['b', 1]]);
    assert.equal(r.head.parents.length, 1);
  }
});

test('LiveGap kernel stays mint/read-lockstep with the full Fugue policy', () => {
  const full = unifiedSidedEmbedRGAExperimental, compact = liveGapSidedEmbedRGA;
  let a = full.init(), b = compact.init(), next = 1, seed = 0x51ded;
  const rnd = () => (seed = (seed * 1664525 + 1013904223) >>> 0) / 2 ** 32;
  for (let step = 0; step < 1200; step++) {
    const ids = full.readIds(a);
    let op;
    if (!ids.length || rnd() < .72) {
      const pos = Math.floor(rnd() * (ids.length + 1));
      op = ins(next++, 'x', pos ? ids[pos - 1] : null);
      const pa = full.prepare(a, op), pb = compact.prepare(b, op);
      assert.deepEqual([pb.side, pb.parentId], [pa.side, pa.parentId]);
      a = full.apply(a, pa); b = compact.apply(b, pb);
    } else {
      op = del(ids[Math.floor(rnd() * ids.length)]);
      a = full.apply(a, op); b = compact.apply(b, op);
    }
    if (step % 50 === 0) assert.deepEqual(compact.read(b), full.read(a));
  }
  assert.deepEqual(compact.read(b), full.read(a));
  const back = compact.decodeState(compact.encodeState(b));
  assert.deepEqual(compact.read(back), compact.read(b));
  const anchorId = compact.readIds(back).at(-1) ?? null;
  const op = ins(next, 'z', anchorId);
  assert.deepEqual(
    (({ side, parentId }) => [side, parentId])(compact.prepare(back, op)),
    (({ side, parentId }) => [side, parentId])(full.prepare(a, op)));
});

test('LiveGap fork/join matches the full Fugue policy and remains editable', () => {
  const full = unifiedSidedEmbedRGAExperimental, compact = liveGapSidedEmbedRGA;
  const build = (dt) => fold(dt, [ins(1, 'a'), ins(2, 'b', 1)]).state;
  const lf = build(full), lc = build(compact);
  const af = full.apply(lf, full.prepare(lf, ins(5, 'x', 1)));
  const ac = compact.apply(lc, compact.prepare(lc, ins(5, 'x', 1)));
  let bf = full.apply(lf, full.prepare(lf, ins(4, 'y', 1)));
  let bc = compact.apply(lc, compact.prepare(lc, ins(4, 'y', 1)));
  bf = full.apply(bf, del(2)); bc = compact.apply(bc, del(2));
  const mf = full.merge3(lf, af, bf), mc = compact.merge3(lc, ac, bc);
  assert.deepEqual(compact.read(mc), full.read(mf));
  const op = ins(7, 'z', 1), pf = full.prepare(mf, op), pc = compact.prepare(mc, op);
  assert.deepEqual([pc.side, pc.parentId], [pf.side, pf.parentId]);
  assert.deepEqual(compact.read(compact.apply(mc, pc)), full.read(full.apply(mf, pf)));
});
