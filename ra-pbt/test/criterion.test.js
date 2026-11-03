import test from 'node:test';
import assert from 'node:assert/strict';
import { execute, findWitness, allFinalViews, evaluator, makeConfiguration, normaliseSpec, eventsAt,
  newCheckState, raLinearizabilityStep } from '../src/index.js';
import { orsetReplicated } from '../instances/sal-runtime/endtoend.js';
import { orsetDatatype, orsetInstance, setSpec } from '../instances/sal-runtime/orset.js';

test('full causal-history rejection is not a paper-order rejection: crossed OR-set removals', () => {
  const trace = execute(orsetReplicated, { replicas: 2, steps: [
    { type: 'edit', replica: 1, kind: 'add', el: 'x' },
    { type: 'edit', replica: 1, kind: 'rm', el: 'y' },
    { type: 'edit', replica: 2, kind: 'add', el: 'y' },
    { type: 'edit', replica: 2, kind: 'rm', el: 'x' },
    { type: 'deliver', from: 1, to: 2 },
  ] });
  // Hand-derived: each removal observes no tag of its element; both adds survive.
  assert.deepEqual(trace.snapshots[4].visible, ['x', 'y']);
  const check = trace.checks.raLinearizability;
  assert.equal(check.pass, false);
  assert.equal(check.criterion.id, 'causal-history-conformance');
  assert.equal(check.criterion.paperRaVerdict, 'not-checked');
  const failure = check.details.failures[0];
  assert.equal(failure.causalGaps, 0);
  assert.equal(failure.criterion.paperRaVerdict, 'not-checked');
  const events = trace.ops.map((o) => ({ key: o.key, deps: o.deps, specOps: o.specOps }));
  assert.equal(findWitness(orsetReplicated.spec, events, ['x', 'y']).found, false);
  assert.deepEqual(allFinalViews(orsetReplicated.spec, events).map(JSON.stringify).sort(),
    [[], ['x'], ['y']].map(JSON.stringify).sort());
  // The ordinary-OR-set paper order has only same-element rm-before-add edges.
  const cfg = makeConfiguration(trace.ops.map((o) => ({ id: o.key, replica: o.replica,
    seq: o.seq, op: o.specOps[0], vis: o.deps })));
  const paper = evaluator(orsetDatatype, orsetInstance, cfg);
  const ids = trace.ops.map((o) => o.key);
  assert.deepEqual(paper.lo(ids).sort(), [['r1#1', 'r2#0'], ['r2#1', 'r1#0']]);
  assert.deepEqual(orsetDatatype.read(paper.can(ids)), ['x', 'y']);
  const paperWitness = [trace.ops[1], trace.ops[3], trace.ops[0], trace.ops[2]];
  const view = paperWitness.reduce((s, o) => setSpec.step(s, o.specOps[0]), setSpec.init());
  assert.deepEqual(view, ['x', 'y']);
  assert.notDeepEqual(view, []);
});

test('spec.rc does not weaken causal dependencies or enforce a directed implementation policy', () => {
  let rcCalls = 0;
  const rc = () => { rcCalls++; return true; };
  const spec = { init: () => null, apply: (_s, op) => op, view: (s) => s,
    serialise: JSON.stringify, viewKey: JSON.stringify, rc };
  assert.equal(normaliseSpec(spec).rc, rc);
  const concurrent = [{ key: 'a', deps: [], specOps: ['a'] }, { key: 'b', deps: [], specOps: ['b'] }];
  // An implementation policy a rc b would forbid this accepted b,a order.
  assert.deepEqual(findWitness(spec, concurrent, 'a'), { found: true, order: ['b', 'a'] });
  const causal = [concurrent[0], { ...concurrent[1], deps: ['a'] }];
  assert.equal(findWitness(spec, causal, 'a').found, false);
  assert.equal(findWitness(spec, causal, 'b').found, true);
  assert.equal(rcCalls, 0);
});

test('missing causal dependencies are dropped and counted; partial records skip the check', () => {
  const ops = [{ key: 'a', deps: [], specOps: [1] }, { key: 'b', deps: ['a'], specOps: [2] }];
  const ex = {
    ops, integrated: { 1: new Set(['b']) }, partial: { 1: [] },
    byKey: new Map(ops.map((o) => [o.key, o])), replicas: { 1: {} },
    adapter: { view: () => 2 },
    spec: { init: () => 0, apply: (_s, op) => op, view: (s) => s,
      serialise: JSON.stringify, viewKey: JSON.stringify },
    checkState: newCheckState(['raLinearizability'], { witnessBound: 12 }),
  };
  assert.deepEqual(eventsAt(ex, 1), { events: [{ key: 'b', deps: [], specOps: [2] }], gaps: 1 });
  raLinearizabilityStep(ex, 1, 0);
  assert.equal(ex.checkState.stats.causalGaps, 1);
  assert.equal(ex.checkState.per.raLinearizability.runs, 1);
  assert.equal(ex.checkState.results().raLinearizability.criterion.paperRaVerdict, 'not-checked');
  ex.partial[1] = ['b'];
  raLinearizabilityStep(ex, 1, 1);
  assert.equal(ex.checkState.stats.witnessSkipsPartial, 1);
  assert.equal(ex.checkState.per.raLinearizability.runs, 1);
});
