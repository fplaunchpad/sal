import test from 'node:test';
import assert from 'node:assert/strict';
import { embedRGA } from '../src/datatypes/embedRGA.js';
import { sharedEmbedRGA, pathDeltas, encodeSharedState, decodeSharedState,
  encodeSharedRuns, decodeSharedRuns } from '../src/datatypes/sharedEmbedRGA.js';
import { decodeChain } from '../src/compact.js';
import { compactSharedEliasDelta, compactSharedDirect,
  compactibleSharedEmbedRGA, sharedToAbsolute,
  buildSharedInverseTranslate } from '../src/shared-compact.js';
import { buildInverseTranslate } from '../src/epoch.js';
import { eliasDeltaCode } from '../src/datatypes/embedRGA.js';
import { DistributedReplica, syncReplicas } from '../src/replica.js';

const applyBoth = (a, b, op) => [embedRGA.apply(a, op), sharedEmbedRGA.apply(b, op)];

test('typing run shares prefixes and reads exactly like EmbedRGA', () => {
  let a = embedRGA.init(), b = sharedEmbedRGA.init(), anchorId = null;
  for (let id = 1; id <= 1000; id++) {
    [a, b] = applyBoth(a, b, { type: 'ins', id, anchorId, el: String(id % 10) });
    anchorId = id;
  }
  assert.deepEqual(sharedEmbedRGA.read(b), embedRGA.read(a));
  assert.equal(sharedEmbedRGA.nodeCount(b), 1000);
  assert.deepEqual(pathDeltas(b.get(1000)), decodeChain(a.get(1000).coord));
});

test('deletion retains only path nodes needed by live descendants', () => {
  let a = embedRGA.init(), b = sharedEmbedRGA.init(), anchorId = null;
  for (let id = 1; id <= 20; id++) {
    [a, b] = applyBoth(a, b, { type: 'ins', id, anchorId, el: `${id}` }); anchorId = id;
  }
  for (let id = 1; id < 20; id++) [a, b] = applyBoth(a, b, { type: 'del', id });
  assert.deepEqual(sharedEmbedRGA.read(b), embedRGA.read(a));
  assert.equal(sharedEmbedRGA.nodeCount(b), 20, 'the sole survivor needs its complete path');
  [a, b] = applyBoth(a, b, { type: 'del', id: 20 });
  assert.equal(sharedEmbedRGA.nodeCount(b), 0, 'an empty document releases every path');
});

test('directed concurrent merge matches EmbedRGA', () => {
  let l1 = embedRGA.init(), l2 = sharedEmbedRGA.init();
  [l1, l2] = applyBoth(l1, l2, { type: 'ins', id: 1, anchorId: null, el: 'a' });
  let a1 = l1, a2 = l2, b1 = l1, b2 = l2;
  [a1, a2] = applyBoth(a1, a2, { type: 'ins', id: 4, anchorId: 1, el: 'x' });
  [b1, b2] = applyBoth(b1, b2, { type: 'ins', id: 3, anchorId: 1, el: 'y' });
  const m1 = embedRGA.merge3(l1, a1, b1), m2 = sharedEmbedRGA.merge3(l2, a2, b2);
  assert.deepEqual(sharedEmbedRGA.read(m2), embedRGA.read(m1));
});

test('merge canonicalizes independently constructed common prefixes', () => {
  const ins1 = { type: 'ins', id: 1, anchorId: null, el: 'a' };
  const l = sharedEmbedRGA.apply(sharedEmbedRGA.init(), ins1);
  let a = sharedEmbedRGA.apply(l, { type: 'ins', id: 4, anchorId: 1, el: 'x' });
  let independent = sharedEmbedRGA.apply(sharedEmbedRGA.init(), ins1);
  independent = sharedEmbedRGA.apply(independent,
    { type: 'ins', id: 3, anchorId: 1, el: 'y' });
  const merged = sharedEmbedRGA.merge3(l, a, independent);
  assert.equal(merged.get(4).path.parent, merged.get(3).path.parent,
    'logical common prefix is physically shared after merge');
  assert.deepEqual(sharedEmbedRGA.read(merged), ['a', 'x', 'y']);
});

test('deterministic random sequential histories match EmbedRGA', () => {
  let a = embedRGA.init(), b = sharedEmbedRGA.init(), next = 1, seed = 7;
  const rnd = () => (seed = (seed * 1664525 + 1013904223) >>> 0) / 2 ** 32;
  for (let k = 0; k < 2000; k++) {
    const ids = embedRGA.readIds(a);
    let op;
    if (ids.length === 0 || rnd() < .7) {
      const pos = Math.floor(rnd() * (ids.length + 1));
      op = { type: 'ins', id: next++, anchorId: pos ? ids[pos - 1] : null, el: 'x' };
    } else op = { type: 'del', id: ids[Math.floor(rnd() * ids.length)] };
    [a, b] = applyBoth(a, b, op);
    if (k % 100 === 0) assert.deepEqual(sharedEmbedRGA.read(b), embedRGA.read(a));
  }
  assert.deepEqual(sharedEmbedRGA.read(b), embedRGA.read(a));
  const bytes = encodeSharedState(b), back = decodeSharedState(bytes);
  assert.deepEqual(sharedEmbedRGA.read(back), embedRGA.read(a));
  assert.equal(sharedEmbedRGA.nodeCount(back), sharedEmbedRGA.nodeCount(b));
  const runBytes = encodeSharedRuns(b), runBack = decodeSharedRuns(runBytes);
  assert.deepEqual(sharedEmbedRGA.read(runBack), embedRGA.read(a));
  assert.equal(sharedEmbedRGA.nodeCount(runBack), sharedEmbedRGA.nodeCount(b));
  assert.ok(runBytes.length > 0, 'run encoding is nonempty');
});

test('run snapshot supports future editing and independently decoded merge', () => {
  let s = sharedEmbedRGA.init();
  for (let id = 1; id <= 50; id++) s = sharedEmbedRGA.apply(s,
    { type: 'ins', id, anchorId: id === 1 ? null : id - 1, el: 'a' });
  const a = decodeSharedRuns(encodeSharedRuns(s));
  const b = decodeSharedRuns(encodeSharedRuns(s));
  const aa = sharedEmbedRGA.apply(a, { type: 'ins', id: 60, anchorId: 50, el: 'x' });
  const bb = sharedEmbedRGA.apply(b, { type: 'ins', id: 55, anchorId: 50, el: 'y' });
  const merged = sharedEmbedRGA.merge3(s, aa, bb);
  assert.equal(sharedEmbedRGA.read(merged).join(''), 'a'.repeat(50) + 'xy');
});

test('compacted shared state uses explicit live IDs and remains editable', () => {
  let s = sharedEmbedRGA.init();
  for (let id = 1; id <= 30; id++) s = sharedEmbedRGA.apply(s,
    { type: 'ins', id, anchorId: id === 1 ? null : id - 1, el: 'a' });
  for (let id = 2; id < 30; id += 2) s = sharedEmbedRGA.apply(s, { type: 'del', id });
  const settledIds = new Set(Array.from({ length: 30 }, (_, i) => i + 1));
  const compacted = compactSharedEliasDelta(s, { settledIds }, { fuseSpines: true }).state;
  const back = decodeSharedRuns(encodeSharedRuns(compacted));
  assert.deepEqual(sharedEmbedRGA.read(back), sharedEmbedRGA.read(s));
  const last = sharedEmbedRGA.readIds(back).at(-1);
  const edited = sharedEmbedRGA.apply(back, { type: 'ins', id: 40, anchorId: last, el: 'x' });
  assert.equal(sharedEmbedRGA.read(edited).at(-1), 'x');
});

test('direct shared compactor matches the compatibility oracle', () => {
  let s = sharedEmbedRGA.init(), seed = 17;
  const rnd = () => (seed = (seed * 1664525 + 1013904223) >>> 0) / 2 ** 32;
  const settledIds = new Set();
  for (let id = 1; id <= 300; id++) {
    const ids = sharedEmbedRGA.readIds(s), pos = Math.floor(rnd() * (ids.length + 1));
    s = sharedEmbedRGA.apply(s, { type: 'ins', id,
      anchorId: pos ? ids[pos - 1] : null, el: String(id % 10) });
    settledIds.add(id);
  }
  for (const id of sharedEmbedRGA.readIds(s)) if (rnd() < .55)
    s = sharedEmbedRGA.apply(s, { type: 'del', id });
  const cut = { settledIds };
  const oracle = compactSharedEliasDelta(s, cut, { fuseSpines: true });
  const direct = compactSharedDirect(s, cut, { fuseSpines: true });
  assert.deepEqual(sharedEmbedRGA.read(direct.state), sharedEmbedRGA.read(oracle.state));
  assert.equal(sharedEmbedRGA.fingerprint(direct.state), sharedEmbedRGA.fingerprint(oracle.state));
});

test('direct guarded compactor matches oracle for frozen anchor and in-flight path', () => {
  let s = sharedEmbedRGA.init();
  for (const op of [
    { type: 'ins', id: 2, anchorId: null, el: 'a' },
    { type: 'ins', id: 7, anchorId: 2, el: 'b' },
    { type: 'ins', id: 9, anchorId: 2, el: 'c' },
    { type: 'ins', id: 12, anchorId: 7, el: 'd' },
  ]) s = sharedEmbedRGA.apply(s, op);
  const abs = sharedToAbsolute(s), anchor = abs.get(2).coord;
  const inflight = anchor + eliasDeltaCode.enc(8); // hypothetical id 10 after anchor 2
  const cut = { settledIds: new Set([2, 7, 9, 12]),
    frozenAnchorCoords: [anchor], inflight: [inflight] };
  const oracle = compactSharedEliasDelta(s, cut, { fuseSpines: true });
  const direct = compactSharedDirect(s, cut, { fuseSpines: true });
  assert.equal(sharedEmbedRGA.fingerprint(direct.state), sharedEmbedRGA.fingerprint(oracle.state));
  assert.deepEqual(sharedEmbedRGA.read(direct.state), sharedEmbedRGA.read(oracle.state));
  assert.ok(direct.stats.groupsSkippedInflight > 0);
});

test('native shared inverse translation matches the absolute oracle', () => {
  let pre = sharedEmbedRGA.init();
  for (const op of [
    { type: 'ins', id: 2, anchorId: null, el: 'a' },
    { type: 'ins', id: 8, anchorId: 2, el: 'b' },
    { type: 'ins', id: 5, anchorId: 2, el: 'c' },
    { type: 'ins', id: 11, anchorId: 8, el: 'd' },
  ]) pre = sharedEmbedRGA.apply(pre, op);
  pre = sharedEmbedRGA.apply(pre, { type: 'del', id: 5 });
  const post = compactSharedDirect(pre,
    { settledIds: new Set([2, 5, 8, 11]) }).state;
  const preAbs = sharedToAbsolute(pre), postAbs = sharedToAbsolute(post);
  const oracle = buildInverseTranslate(preAbs, postAbs);
  const native = buildSharedInverseTranslate(pre, post);
  for (const [, rec] of postAbs) {
    assert.equal(native(rec.coord), oracle(rec.coord));
    const extension = rec.coord + eliasDeltaCode.enc(3);
    assert.equal(native(extension), oracle(extension));
  }
});

test('DistributedReplica certified GC: shared representation matches no-GC twin', () => {
  const a = new DistributedReplica(compactibleSharedEmbedRGA, 'A');
  const b = new DistributedReplica(compactibleSharedEmbedRGA, 'B');
  a.register('B'); b.register('A');
  const control = new DistributedReplica(compactibleSharedEmbedRGA, 'C');
  let anchorId = null;
  for (let id = 1; id <= 40; id++) {
    const op = { type: 'ins', id, anchorId, el: String(id % 10) };
    a.commit(op); control.commit(op); anchorId = id;
  }
  for (let id = 1; id < 40; id++) {
    const op = { type: 'del', id }; a.commit(op); control.commit(op);
  }
  syncReplicas(a, b);
  b.commit({ type: 'del', id: 0 }); syncReplicas(a, b);
  const c = a.compactStable({ fuseSpines: true });
  assert.equal(c.compacted, true, c.reason);
  assert.deepEqual(a.read(), control.read());
  syncReplicas(a, b);
  assert.deepEqual(a.read(), b.read());
  const restored = compactibleSharedEmbedRGA.decodeState(
    compactibleSharedEmbedRGA.encodeState(a.head.state));
  assert.deepEqual(compactibleSharedEmbedRGA.read(restored), a.read());
});

test('returning pre-compaction peer rebases by birth identity and converges', () => {
  const a = new DistributedReplica(compactibleSharedEmbedRGA, 'A');
  const b = new DistributedReplica(compactibleSharedEmbedRGA, 'B');
  a.register('B'); b.register('A');
  let anchorId = null;
  for (let id = 1; id <= 20; id++) { a.commit({ type: 'ins', id, anchorId, el: 'a' }); anchorId = id; }
  for (let id = 1; id < 20; id++) a.commit({ type: 'del', id });
  syncReplicas(a, b); b.commit({ type: 'del', id: 0 }); syncReplicas(a, b);
  assert.equal(a.compactStable({ fuseSpines: true }).compacted, true);
  b.commit({ type: 'ins', id: 30, anchorId: 20, el: 'z' });
  syncReplicas(a, b);
  assert.deepEqual(a.read(), b.read());
  assert.equal(a.read().at(-1), 'z');
});

test('cross-epoch twin PBT: returning edits converge with never-compacted control', () => {
  let seed = 91;
  const rnd = () => (seed = (seed * 1664525 + 1013904223) >>> 0) / 2 ** 32;
  for (let trial = 0; trial < 40; trial++) {
    const a = new DistributedReplica(compactibleSharedEmbedRGA, 'A');
    const b = new DistributedReplica(compactibleSharedEmbedRGA, 'B');
    a.register('B'); b.register('A');
    const control = new DistributedReplica(compactibleSharedEmbedRGA, 'C');
    let anchorId = null;
    for (let id = 1; id <= 35; id++) {
      const op = { type: 'ins', id, anchorId, el: String(id % 10) };
      a.commit(op); control.commit(op); anchorId = id;
    }
    for (let id = 1; id < 35; id++) if (rnd() < .65) {
      const op = { type: 'del', id }; a.commit(op); control.commit(op);
    }
    syncReplicas(a, b); b.commit({ type: 'del', id: 0 }); syncReplicas(a, b);
    const compacted = a.compactStable({ fuseSpines: true });
    if (!compacted.compacted) continue;
    const live = compactibleSharedEmbedRGA.readIds(b.head.state);
    const parent = live.at(-1) ?? null, fresh = 100 + trial;
    const op = { type: 'ins', id: fresh, anchorId: parent, el: 'z' };
    b.commit(op); control.commit(op); syncReplicas(a, b);
    assert.deepEqual(a.read(), control.read(), `trial ${trial}`);
    assert.deepEqual(a.read(), b.read(), `peer convergence trial ${trial}`);
  }
});
