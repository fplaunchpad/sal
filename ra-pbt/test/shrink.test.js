import test from 'node:test';
import assert from 'node:assert/strict';
import { Execution, shrink } from '../src/index.js';
import { gset } from './gset.js';

const add = (replica, value) => ({ type: 'edit', replica, kind: 'add', value });
const deliver = (from, to) => ({ type: 'deliver', from, to });
const send = (from, to, op) => ({ type: 'send', from, to, op });

/** Whether replica 2 shows a value starting with q, without the final sync. */
function showsQ(schedule) {
  const ex = new Execution(gset, schedule.replicas, { checks: [] });
  for (const s of schedule.steps) ex.apply(s);
  return ex.adapter.view(ex.replica(2)).some((v) => v.startsWith('q'));
}

test('steps the failure does not need are removed', () => {
  const schedule = { replicas: 2, steps: [add(1, 'a'), add(1, 'q'), add(2, 'b'), deliver(1, 2), add(1, 'c')] };
  const res = shrink(gset, schedule, showsQ);
  assert.deepEqual(res.schedule.steps, [add(1, 'q'), deliver(1, 2)]);
  assert.notDeepEqual(res.schedule.steps, schedule.steps);
  assert.equal(res.reductions.filter((r) => r.reduction === 'remove-step').length, 3);
});

test('a send follows its record when earlier records are removed', () => {
  // q is replica 1's record 1; once a is removed it becomes record 0.
  const schedule = { replicas: 2, steps: [add(1, 'a'), add(1, 'q'), send(1, 2, 0), send(1, 2, 1)] };
  const res = shrink(gset, schedule, showsQ);
  assert.deepEqual(res.schedule.steps, [add(1, 'q'), send(1, 2, 0)]);
  assert.notDeepEqual(res.schedule.steps, [add(1, 'q'), send(1, 2, 1)]);
});

test('requests are reduced by the instance reducer', () => {
  const schedule = { replicas: 2, steps: [add(1, 'qzz'), deliver(1, 2)] };
  const res = shrink(gset, schedule, showsQ);
  assert.deepEqual(res.schedule.steps, [add(1, 'q'), deliver(1, 2)]);
  assert.deepEqual(res.reductions.map((r) => r.reduction), ['reduce-request', 'reduce-request']);
  // Negative: a value that must stay long is not cut.
  const keepsZ = (s) => showsQ(s) && s.steps[0].value.includes('z');
  assert.deepEqual(shrink(gset, schedule, keepsZ).schedule.steps, [add(1, 'qz'), deliver(1, 2)]);
});

test('a schedule that does not fail is returned unchanged', () => {
  const schedule = { replicas: 2, steps: [add(1, 'a'), deliver(1, 2)] };
  const res = shrink(gset, schedule, showsQ);
  assert.equal(res.schedule, schedule);
  assert.deepEqual(res.reductions, []);
  assert.ok(res.executions > 0);
});
