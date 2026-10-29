import test from 'node:test';
import assert from 'node:assert/strict';
import { Execution, execute, generate, checkAdapter, eventsAt } from '../src/index.js';
import { gset } from './gset.js';

const add = (replica, value) => ({ type: 'edit', replica, kind: 'add', value });
const deliver = (from, to) => ({ type: 'deliver', from, to });
const send = (from, to, op) => ({ type: 'send', from, to, op });

function run(steps, n = 2) {
  const ex = new Execution(gset, n, { checks: [] });
  for (const s of steps) ex.apply(s);
  return ex;
}

test('records get per-replica keys and the integrated past as deps', () => {
  const ex = run([add(1, 'a'), add(2, 'b'), deliver(1, 2), add(2, 'c')]);
  assert.deepEqual(ex.ops.map((o) => o.key), ['r1#0', 'r2#0', 'r2#1']);
  // b is concurrent with a; c is issued after both reached replica 2.
  assert.deepEqual(ex.byKey.get('r2#0').deps, []);
  assert.deepEqual(ex.byKey.get('r2#1').deps, ['r1#0', 'r2#0']);
  assert.notDeepEqual(ex.byKey.get('r2#0').deps, ['r1#0']);
  assert.deepEqual([...ex.integrated[1]], ['r1#0']);
  assert.deepEqual([...ex.integrated[2]].sort(), ['r1#0', 'r2#0', 'r2#1']);
  assert.deepEqual(eventsAt(ex, 1).events.map((e) => e.key), ['r1#0']);
});

test('a record sent ahead of its predecessor is pending until the predecessor arrives', () => {
  const ex = run([add(1, 'a'), add(1, 'b'), send(1, 2, 1)]);
  assert.equal(ex.snapshots[2].pending, true);
  assert.deepEqual([...ex.integrated[2]], []);
  assert.deepEqual(ex.adapter.view(ex.replica(2)), []);
  ex.apply(send(1, 2, 0));
  assert.equal(ex.snapshots[3].pending, false);
  assert.deepEqual([...ex.integrated[2]].sort(), ['r1#0', 'r1#1']);
  assert.deepEqual(ex.adapter.view(ex.replica(2)), ['a', 'b']);
  assert.equal(ex.stats.pendingSends, 1);
});

test('an opened replica holds the state it was opened from', () => {
  const ex = run([add(1, 'a'), { type: 'open', replica: 2, from: 1 }, add(2, 'b')]);
  assert.deepEqual(ex.snapshots[1], { step: 1, replica: 2, opened: true, visible: ['a'] });
  assert.ok(ex.opened.has(2));
  assert.deepEqual(ex.byKey.get('r2#0').deps, ['r1#0']);
  assert.deepEqual(ex.adapter.view(ex.replica(1)), ['a']);
});

test('invalid steps are rejected with RangeError', () => {
  assert.throws(() => run([add(1, 'a'), add(2, 'b'), { type: 'open', replica: 2, from: 1 }]), RangeError);
  assert.throws(() => run([{ type: 'open', replica: 2, from: 1 }]), RangeError);
  assert.throws(() => run([add(1, 'a'), deliver(1, 1)]), RangeError);
  assert.throws(() => run([add(1, 'a'), send(1, 2, 3)]), RangeError);
  assert.throws(() => run([add(1, '')]), RangeError);
  assert.throws(() => run([add(3, 'a')]), RangeError);
  // Negative: the same steps in a valid form execute.
  assert.equal(run([add(1, 'a'), send(1, 2, 0)]).stats.sends, 1);
});

test('the final sync brings every replica to the same state and runs the final checks', () => {
  const trace = execute(gset, { replicas: 3, steps: [add(1, 'a'), add(2, 'b'), add(3, 'c')] });
  for (const c of ['convergence', 'raLinearizability', 'localMeaning', 'determinism', 'conservation']) assert.equal(trace.checks[c].pass, true, c);
  const last = trace.snapshots.slice(-3).map((s) => s.visible);
  assert.deepEqual(last, [['a', 'b', 'c'], ['a', 'b', 'c'], ['a', 'b', 'c']]);
  // Three edits plus one round over the six ordered pairs.
  assert.equal(trace.snapshots.length, 9);
  assert.equal(trace.stats.deliveries, 6);
  assert.notDeepEqual(trace.snapshots[2].visible, ['a', 'b', 'c']);
});

test('generation is a function of the seed, and generated schedules replay', () => {
  const a = generate(gset, 7, { steps: 10, replicas: 3 });
  const b = generate(gset, 7, { steps: 10, replicas: 3 });
  assert.deepEqual(a, b);
  assert.equal(a.steps.length, 10);
  assert.equal(a.replicas, 3);
  assert.notDeepEqual(generate(gset, 8, { steps: 10, replicas: 3 }).steps, a.steps);
  const trace = execute(gset, a);
  assert.equal(trace.schedule, a);
  // With opened replicas the generator opens every waiting replica.
  const o = generate(gset, 7, { steps: 10, replicas: 3, openedReplicas: true });
  assert.ok(o.steps.some((s) => s.type === 'open'));
  assert.ok(!a.steps.some((s) => s.type === 'open'));
});

test('checkAdapter names missing members and fills defaults', () => {
  assert.throws(() => checkAdapter({ createReplica() {} }), /adapter lacks issue, deliver, sync, view, stateVector, hasPending, validRequest/);
  const a = checkAdapter(gset.adapter);
  assert.equal(a.supportsOpen, true);
  assert.equal(a.supportsConservation, true);
  assert.deepEqual(a.requestOf({ type: 'edit', replica: 1, kind: 'add', value: 'a' }), { kind: 'add', value: 'a' });
  assert.equal(checkAdapter(a), a);
});
