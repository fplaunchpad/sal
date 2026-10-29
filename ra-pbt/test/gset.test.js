import test from 'node:test';
import assert from 'node:assert/strict';
import { execute, runCampaign, runRegressions, failuresOf } from '../src/index.js';
import { gset, droppingGSet } from './gset.js';

const add = (replica, value) => ({ type: 'edit', replica, kind: 'add', value });
const deliver = (from, to) => ({ type: 'deliver', from, to });

// Replica 1 adds a, replica 2 adds b concurrently, then replica 2 receives a.
// Every linear extension of {a, b} folds to [a, b], so that is the only
// admitted view at replica 2.
const concurrentAdds = { replicas: 2, steps: [add(1, 'a'), add(2, 'b'), deliver(1, 2)] };

test('a correct grow-only set passes every check', () => {
  const trace = execute(gset, concurrentAdds, { finalSync: false });
  for (const [name, res] of Object.entries(trace.checks)) assert.equal(res.pass, true, name);
  assert.deepEqual(trace.snapshots[2].visible, ['a', 'b']);
  assert.equal(trace.checks.raLinearizability.details.runs, 3);
  assert.ok(trace.checks.determinism.details.runs > 0);
});

test('a set that drops an element on merge fails RA-linearizability', () => {
  const trace = execute(droppingGSet, concurrentAdds, { finalSync: false });
  const f = trace.checks.raLinearizability.details.failures;
  assert.equal(f.length, 1);
  assert.equal(f[0].replica, 2);
  assert.equal(f[0].step, 2);
  assert.deepEqual(f[0].actual, ['a']);
  assert.deepEqual(f[0].expected.admittedViews, [['a', 'b']]);
  assert.equal(f[0].signature, 'raLinearizability:add');
  // The local edits themselves are right; the defect is in the merge.
  assert.equal(trace.checks.localMeaning.pass, true);
});

test('a campaign finds and shrinks the dropping merge, and passes the correct set', () => {
  const good = runCampaign(gset, { seed: 3, trials: 15, options: { steps: 10 } });
  assert.equal(good.summary.failingTrials, 0);
  assert.ok(good.summary.versionsChecked > 0);
  assert.deepEqual(good.shrunk, []);
  const bad = runCampaign(droppingGSet, { seed: 3, trials: 15, options: { steps: 10 } });
  assert.ok(bad.summary.failingTrials > 0);
  assert.ok(bad.summary.trialsFailingByCheck.raLinearizability > 0);
  const rep = bad.shrunk.find((s) => s.signature === 'raLinearizability:add');
  // A failure needs an add at each of two replicas; the final sync supplies
  // the transfer. Its first step, deliver 1->2 (step 2), makes replica 2
  // forget its own element.
  const steps = rep.schedule.steps;
  assert.equal(steps.length, 2);
  assert.deepEqual(steps.map((s) => [s.type, s.replica]), [['edit', 1], ['edit', 2]]);
  assert.equal(rep.failure.step, 2);
  assert.deepEqual(rep.failure.actual, [steps[0].value]);
  assert.deepEqual(rep.failure.expected.admittedViews, [[steps[0].value, steps[1].value].sort()]);
  assert.notDeepEqual(rep.failure.actual, rep.failure.expected.admittedViews[0]);
});

test('declared regressions hold with a failing case and its passing control', () => {
  const out = runRegressions(
    [
      {
        name: 'dropping merge',
        schedule: concurrentAdds,
        replicas: [2],
        observed: ['a', 'b'],
        notObserved: [['a']],
        admitted: [['a', 'b']],
        witness: true,
      },
    ],
    gset,
  );
  assert.deepEqual(out.map((r) => r.pass), [true]);
  assert.deepEqual(out[0].results, { observed: ['a', 'b'], admitted: [['a', 'b']] });
  const wrong = { spec: gset.spec, adapter: droppingGSet.adapter };
  const failing = runRegressions(
    [
      {
        name: 'dropping merge observed',
        schedule: concurrentAdds,
        replicas: [2],
        observed: ['a'],
        admitted: [['a', 'b']],
        witness: false,
        controls: [{ name: 'no concurrent add', schedule: { replicas: 2, steps: [add(1, 'a'), deliver(1, 2)] }, observed: ['a'], admitted: [['a']], witness: true }],
      },
    ],
    wrong,
  );
  assert.equal(failing[0].pass, true, failing[0].error);
  // Negative: claiming the correct set shows the dropped view is refuted.
  const refuted = runRegressions([{ name: 'claims a drop', schedule: concurrentAdds, replicas: [2], observed: ['a'], admitted: [['a', 'b']], witness: false }], gset);
  assert.equal(refuted[0].pass, false);
  assert.match(refuted[0].error, /replica 2: observed/);
});

test('failuresOf lists failures in check order', () => {
  const trace = execute(droppingGSet, concurrentAdds);
  const order = ['convergence', 'raLinearizability', 'localMeaning', 'determinism', 'conservation'];
  const checks = failuresOf(trace).map((f) => f.check);
  const ranks = checks.map((c) => order.indexOf(c));
  assert.deepEqual(ranks, [...ranks].sort((a, b) => a - b));
  assert.ok(checks.includes('raLinearizability'));
  assert.equal(failuresOf(execute(gset, concurrentAdds)).length, 0);
});
