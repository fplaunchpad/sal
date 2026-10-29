import test from 'node:test';
import assert from 'node:assert/strict';
import { execute, runCampaign, runRegressions, findWitness, allFinalViews, eventsAt, Execution } from '../src/index.js';
import {
  orsetReplicated,
  brokenOrsetReplicated,
  rgaReplicated,
  rgaLiveAnchorReplicated,
} from '../instances/sal-runtime/endtoend.js';

// Identities are minted with stride 100 and slot = replica number: a
// replica whose clock has seen counter c mints (c + 1) * 100 + r. RGA ids
// advance the clock on receipt; OR-set tags do not.

const add = (replica, el) => ({ type: 'edit', replica, kind: 'add', el });
const rm = (replica, el) => ({ type: 'edit', replica, kind: 'rm', el });
const ins = (replica, index, el) => ({ type: 'edit', replica, kind: 'insert', index, el });
const del = (replica, index) => ({ type: 'edit', replica, kind: 'delete', index });
const deliver = (from, to) => ({ type: 'deliver', from, to });
const send = (from, to, op) => ({ type: 'send', from, to, op });

const visible = (trace) => trace.snapshots.map((s) => s.visible);

function assertAllPass(trace) {
  for (const [name, res] of Object.entries(trace.checks)) {
    if (name === 'determinism') continue;
    assert.equal(res.pass, true, `${name}: ${JSON.stringify(res.details.failures[0])}`);
  }
  assert.equal(trace.checks.raLinearizability.details.runs, trace.snapshots.length);
  assert.ok(trace.checks.conservation.details.runs > 0);
  assert.equal(trace.checks.determinism.details.runs, 0);
  assert.ok(trace.stats.skipped.determinism > 0);
}

/** The view a replica shows after the steps, and the witness verdict for another view. */
function witnessAt(instance, schedule, replica, view) {
  const ex = new Execution(instance, schedule.replicas, { checks: [] });
  for (const s of schedule.steps) ex.apply(s);
  return findWitness(ex.spec, eventsAt(ex, replica).events, view).found;
}

// ---------------------------------------------------------------- OR-set

// Replica 1 adds a (tag 101) and replica 2 receives it; then replica 1
// removes a (killing tag 101) while replica 2 adds a again (tag 102). The
// removal names only the tag it observed, so a survives at both replicas.
// The set specification admits [] (add 102 before the removal) and [a]
// (after it); the runtime shows [a].
const orsetAddRm = {
  replicas: 2,
  steps: [add(1, 'a'), deliver(1, 2), rm(1, 'a'), add(2, 'a'), deliver(1, 2), deliver(2, 1)],
};

// Two replicas each add one element and remove the other's, without having
// seen it; the runtime shows both elements. The search here asks for a
// linear extension of the whole causal order, program order included, and
// none exists: every extension removes one element. The paper's order
// omits edges between commuting operations, so under it the removals
// precede the additions and the view is explained. The end-to-end check is
// therefore RA-linearizability with respect to the causal order, which is
// stricter here than the paper's criterion; the law layer, not this check,
// evaluates the paper's order.
const orsetCrossRemoval = {
  replicas: 2,
  steps: [add(1, 'x'), rm(1, 'y'), add(2, 'y'), rm(2, 'x'), deliver(1, 2)],
};

test('OR-set: cross removals of unseen elements have no causal-order witness, though the paper admits the view', () => {
  const trace = execute(orsetReplicated, orsetCrossRemoval);
  assert.deepEqual(trace.ops.map((o) => o.specOps.map((x) => x.tags ?? null)), [[null], [[]], [null], [[]]]);
  assert.deepEqual(trace.snapshots[4].visible, ['x', 'y']);
  const ra = trace.checks.raLinearizability;
  assert.equal(ra.pass, false);
  const f = ra.details.failures[0];
  assert.equal(f.replica, 2);
  assert.deepEqual(f.actual, ['x', 'y']);
  assert.deepEqual(f.expected.admittedViews.map((v) => v.join('')).sort(), ['', 'x', 'y']);
  assert.equal(trace.checks.convergence.pass, true);
});

test('OR-set: a removal concurrent with an addition of the same element keeps it', () => {
  const trace = execute(orsetReplicated, orsetAddRm);
  assertAllPass(trace);
  assert.deepEqual(visible(trace).slice(0, 6), [['a'], ['a'], [], ['a'], ['a'], ['a']]);
  assert.deepEqual(trace.ops.map((o) => o.specOps), [
    [{ type: 'add', el: 'a', tag: 101 }],
    [{ type: 'rm', el: 'a', tags: [101] }],
    [{ type: 'add', el: 'a', tag: 102 }],
  ]);
  // Negative: the removal does not win at replica 2.
  assert.notDeepEqual(visible(trace)[4], []);
  const out = runRegressions(
    [
      { name: 'add wins', schedule: orsetAddRm, replicas: [1, 2], observed: ['a'], notObserved: [[]], admitted: [[], ['a']], witness: true },
      { name: 'claims the removal wins', schedule: orsetAddRm, replicas: [2], observed: [], admitted: [[], ['a']], witness: true },
    ],
    orsetReplicated,
  );
  assert.equal(out[0].pass, true, out[0].error);
  assert.equal(out[1].pass, false);
  assert.match(out[1].error, /replica 2: observed \["a"\], expected \[\]/);
});

// Replica 1 adds a (tag 101) and both others receive it. Replicas 2 and 3
// each remove a (both kill tag 101) while replica 1 adds a again (tag 201).
// Replica 3 merges replica 2's removal: []. Replica 1 then merges replica
// 3's state: tag 201 survives, so [a].
const orsetThree = {
  replicas: 3,
  steps: [add(1, 'a'), deliver(1, 2), deliver(1, 3), rm(2, 'a'), rm(3, 'a'), add(1, 'a'), deliver(2, 3), deliver(3, 1)],
};

test('OR-set: two concurrent removals and a concurrent addition over three replicas', () => {
  const trace = execute(orsetReplicated, orsetThree);
  assertAllPass(trace);
  const v = visible(trace);
  assert.deepEqual(v.slice(0, 8), [['a'], ['a'], ['a'], [], [], ['a'], [], ['a']]);
  assert.deepEqual(trace.ops.map((o) => o.specOps[0].tag ?? o.specOps[0].tags), [101, [101], [101], 201]);
  assert.deepEqual(v[v.length - 1], ['a']);
  // Negatives: replica 3 does not keep a after both removals, and a view
  // with an element never added has no witness.
  assert.notDeepEqual(v[6], ['a']);
  assert.equal(witnessAt(orsetReplicated, orsetThree, 1, ['a']), true);
  assert.equal(witnessAt(orsetReplicated, orsetThree, 1, ['a', 'b']), false);
});

// ---------------------------------------------------------------- RGA

// Replica 1 inserts a (id 101), both others receive it, then replicas 2 and
// 3 insert b and c after a (ids 202 and 203). Siblings show newest id first,
// so replica 1 shows a c b. The specification admits a c b (202 applied
// before 203) and a b c (203 before 202).
const rgaSiblings = {
  replicas: 3,
  steps: [ins(1, 0, 'a'), deliver(1, 2), deliver(1, 3), ins(2, 1, 'b'), ins(3, 1, 'c'), deliver(2, 1), deliver(3, 1)],
};
const acb = [[101, 'a'], [203, 'c'], [202, 'b']];
const abc = [[101, 'a'], [202, 'b'], [203, 'c']];

test('RGA: concurrent insertions after one anchor over three replicas', () => {
  const trace = execute(rgaReplicated, rgaSiblings);
  assertAllPass(trace);
  const v = visible(trace);
  assert.deepEqual(v.slice(0, 7), [[[101, 'a']], [[101, 'a']], [[101, 'a']], [[101, 'a'], [202, 'b']], [[101, 'a'], [203, 'c']], [[101, 'a'], [202, 'b']], acb]);
  assert.deepEqual(v[v.length - 1], acb);
  // The specification admits a c b and a b c; the runtime shows a c b.
  const ex = new Execution(rgaReplicated, rgaSiblings.replicas, { checks: [] });
  for (const s of rgaSiblings.steps) ex.apply(s);
  assert.deepEqual(allFinalViews(ex.spec, eventsAt(ex, 1).events).map((x) => JSON.stringify(x)).sort(), [abc, acb].map((x) => JSON.stringify(x)).sort());
  // Negatives: a b c is admitted but not shown; c a b is not admitted.
  assert.notDeepEqual(v[6], abc);
  assert.equal(witnessAt(rgaReplicated, rgaSiblings, 1, acb), true);
  assert.equal(witnessAt(rgaReplicated, rgaSiblings, 1, [[203, 'c'], [101, 'a'], [202, 'b']]), false);
});

// Replica 1 inserts a (101), replica 2 receives it; replica 1 deletes a while
// replica 2 inserts b after a (202). After exchange both show b alone.
const rgaDeleteAnchor = {
  replicas: 2,
  steps: [ins(1, 0, 'a'), deliver(1, 2), del(1, 0), ins(2, 1, 'b'), deliver(1, 2), deliver(2, 1)],
};

test('RGA: a deletion concurrent with an insertion after the deleted element', () => {
  for (const instance of [rgaReplicated, rgaLiveAnchorReplicated]) {
    const trace = execute(instance, rgaDeleteAnchor);
    assertAllPass(trace);
    const v = visible(trace);
    assert.deepEqual(v.slice(0, 6), [[[101, 'a']], [[101, 'a']], [], [[101, 'a'], [202, 'b']], [[202, 'b']], [[202, 'b']]]);
    // Negatives: the deletion is not lost, and b is not lost with its anchor.
    assert.equal(witnessAt(instance, rgaDeleteAnchor, 2, [[202, 'b']]), true);
    assert.equal(witnessAt(instance, rgaDeleteAnchor, 2, [[101, 'a'], [202, 'b']]), false);
    assert.equal(witnessAt(instance, rgaDeleteAnchor, 2, []), false);
  }
});

// Replica 1 inserts a (101) then b after it (201). Sending b alone leaves it
// pending at replica 2; sending a then integrates both.
const rgaPending = { replicas: 2, steps: [ins(1, 0, 'a'), ins(1, 1, 'b'), send(1, 2, 1), send(1, 2, 0)] };

test('RGA: a record sent ahead of its causal past is held', () => {
  const trace = execute(rgaReplicated, rgaPending);
  assertAllPass(trace);
  const v = visible(trace);
  assert.deepEqual(v.slice(0, 4), [[[101, 'a']], [[101, 'a'], [201, 'b']], [], [[101, 'a'], [201, 'b']]]);
  assert.deepEqual(trace.snapshots.slice(2, 4).map((s) => s.pending), [true, false]);
  // Negative: b is not shown without its anchor.
  assert.notDeepEqual(v[2], [[201, 'b']]);
});

// Replica 1 inserts a (101); replica 2 receives it. Replica 1 deletes a and
// inserts b at the front (201); replica 2 inserts c at the front (202) and d
// after a (302). Replica 2 then receives replica 1's edits and shows c b d:
// root children newest id first (202, 201, 101), d under the deleted a.
// In the live-anchor list d must precede the deletion of a (its anchor must
// be live), so c (before d at replica 2) precedes the deletion, which
// precedes b: b is applied last and goes to the front, giving b c d only.
// The anchor-retaining list admits c b d (for instance a, del a, b, c, d).
const rgaDeletedAnchorOrder = {
  replicas: 2,
  steps: [ins(1, 0, 'a'), deliver(1, 2), del(1, 0), ins(1, 0, 'b'), ins(2, 0, 'c'), ins(2, 2, 'd'), deliver(1, 2)],
};
const cbd = [[202, 'c'], [201, 'b'], [302, 'd']];
const bcd = [[201, 'b'], [202, 'c'], [302, 'd']];

test('RGA: the runtime is RA-linearizable for the anchor-retaining list but not for the live-anchor list', () => {
  const good = execute(rgaReplicated, rgaDeletedAnchorOrder);
  assertAllPass(good);
  assert.deepEqual(good.snapshots[5].visible, [[202, 'c'], [101, 'a'], [302, 'd']]);
  assert.deepEqual(good.snapshots[6].visible, cbd);
  const bad = execute(rgaLiveAnchorReplicated, rgaDeletedAnchorOrder);
  const f = bad.checks.raLinearizability.details.failures[0];
  assert.equal(f.replica, 2);
  assert.equal(f.step, 6);
  assert.deepEqual(f.actual, cbd);
  assert.deepEqual(f.expected.admittedViews, [bcd]);
  assert.notDeepEqual(f.actual, bcd);
  assert.equal(bad.checks.convergence.pass, true);
  assert.equal(bad.checks.localMeaning.pass, true);
  // Without the deletion both lists admit the runtime's view.
  const noDelete = { replicas: 2, steps: [ins(1, 0, 'a'), deliver(1, 2), ins(1, 0, 'b'), ins(2, 0, 'c'), ins(2, 2, 'd'), deliver(1, 2)] };
  assertAllPass(execute(rgaLiveAnchorReplicated, noDelete));
});

// ---------------------------------------------------------------- campaigns

const MODES = [
  ['whole-state delivery', { partialDelivery: false }],
  ['per-record delivery', { partialDelivery: true }],
];

const brief = (s) => ({
  edits: s.edits,
  deliveries: s.deliveries,
  sends: s.sends,
  pendingSends: s.pendingSends,
  versionsChecked: s.versionsChecked,
  witnessSkips: s.witnessSkips,
  witnessSkipsPartial: s.witnessSkipsPartial,
  causalGaps: s.causalGaps,
  failingTrials: s.failingTrials,
  failuresByCheck: s.failuresByCheck,
  skipped: s.skipped,
});

for (const [name, instance] of [
  ['OR-set', orsetReplicated],
  ['RGA', rgaReplicated],
]) {
  for (const [mode, options] of MODES) {
    test(`${name} campaign, ${mode}: 100 trials, no failure`, () => {
      const { summary } = runCampaign(instance, { seed: 1, trials: 100, options });
      console.log(`${name}, ${mode}:`, JSON.stringify(brief(summary)));
      for (const [check, n] of Object.entries(summary.failuresByCheck)) assert.equal(n, 0, check);
      assert.equal(summary.failingTrials, 0);
      assert.equal(summary.anomalies, 0);
      assert.ok(summary.versionsChecked > 1000);
      assert.equal(summary.witnessSkips + summary.witnessSkipsPartial, 0);
      if (options.partialDelivery) assert.ok(summary.pendingSends > 0);
    });
  }
}

test('RGA campaign against the live-anchor list, per-record delivery: RA-linearizability fails', () => {
  const { summary } = runCampaign(rgaLiveAnchorReplicated, { seed: 1, trials: 100, options: { partialDelivery: true }, shrink: false });
  console.log('RGA, live-anchor list, per-record delivery:', JSON.stringify(brief(summary)));
  assert.ok(summary.trialsFailingByCheck.raLinearizability > 0);
  assert.equal(summary.failuresByCheck.convergence, 0);
  assert.equal(summary.failuresByCheck.conservation, 0);
});

test('negative control: the broken OR-set merge fails and shrinks to at most four steps', () => {
  const { summary, shrunk } = runCampaign(brokenOrsetReplicated, { seed: 1, trials: 100 });
  console.log('broken OR-set:', JSON.stringify(brief(summary)));
  assert.ok(summary.trialsFailingByCheck.raLinearizability + summary.trialsFailingByCheck.convergence > 0);
  const reps = shrunk.filter((s) => /^(convergence|raLinearizability):/.test(s.signature));
  assert.ok(reps.length > 0);
  const best = reps.reduce((a, b) => (b.schedule.steps.length < a.schedule.steps.length ? b : a));
  console.log('broken OR-set, shortest shrunk schedule:', best.signature, JSON.stringify(best.schedule.steps), JSON.stringify({ actual: best.failure.actual, expected: best.failure.expected, step: best.failure.step, replica: best.failure.replica }));
  assert.ok(best.schedule.steps.length <= 4);
  for (const r of reps) assert.ok(r.schedule.steps.length <= 4, `${r.signature}: ${r.schedule.steps.length} steps`);
  // The two-addition failure: replica 2 merges replica 1's addition into its
  // own head with the broken merge, which keeps only its own branch.
  const two = reps.find((s) => s.signature === 'raLinearizability:add');
  assert.deepEqual(two.schedule.steps.map((s) => [s.type, s.replica, s.kind]), [['edit', 1, 'add'], ['edit', 2, 'add']]);
  const [a, b] = two.schedule.steps.map((s) => s.el);
  assert.notEqual(a, b);
  assert.deepEqual(two.failure.actual, [b]);
  assert.deepEqual(two.failure.expected.admittedViews, [[a, b].sort()]);
  // The same schedule passes on the runtime's own merge.
  assertAllPass(execute(orsetReplicated, two.schedule));
});

test('the runtime has no opened replicas', () => {
  assert.throws(() => orsetReplicated.adapter.createReplica(1, { opened: true }), /no replica constructed from a stored state/);
  assert.equal(orsetReplicated.generateOptions({}).openedReplicas, false);
  assert.equal(rgaReplicated.generateOptions({ openedReplicas: true }).openedReplicas, false);
});
