import test from 'node:test';
import assert from 'node:assert/strict';

import * as L from '../src/laws.js';
import {
  orsetDatatype, orsetInstance, orsetObservedTagsDatatype, orsetObservedTagsInstance,
  orsetObservedTagsElementRcInstance, brokenOrsetDatatype, brokenOrsetInstance,
} from '../instances/sal-runtime/orset.js';
import {
  rgaDatatype, rgaInstance, rgaOrderingRcInstance, brokenRgaDatatype, brokenRgaInstance,
  listSpec, listSpecCommutes,
} from '../instances/sal-runtime/rga.js';

const OPTS = { seed: 1, trials: 150, maxSize: 12 };
const fp = (s) => orsetDatatype.serialise(s);
const run = (s, ops, dt) => ops.reduce((x, o) => dt.apply(x, o), s);
const specRun = (ops) => ops.reduce((phi, o) => (phi === undefined ? undefined : listSpec.step(phi, o)), listSpec.init());

function report(t, results) {
  for (const r of results) {
    const verdict = r.status === 'fail' ? `FAIL ${r.failures[0].kind}` : r.status;
    t.diagnostic(`${r.name}: runs=${r.runs} vacuous=${r.vacuous} inconclusive=${r.inconclusive} ${verdict}`);
    for (const f of r.failures) t.diagnostic(L.formatCounterexample(f));
  }
}
const byName = (results) => Object.fromEntries(results.map((r) => [r.name, r]));

// The execution of the paper's defeater figure: A_p, A_q add a at p and q,
// R_p and R_q remove a after seeing only their own replica's addition; v6
// holds E1 = {A_p, R_p, A_q} and v7 holds E2 = {A_q, R_q, A_p}.
const defeater = () => L.makeConfiguration([
  { id: 'Ap', replica: 'p', seq: 1, op: { type: 'add', el: 'a', tag: 1 }, vis: [] },
  { id: 'Aq', replica: 'q', seq: 1, op: { type: 'add', el: 'a', tag: 2 }, vis: [] },
  { id: 'Rp', replica: 'p', seq: 2, op: { type: 'rm', el: 'a' }, vis: ['Ap'] },
  { id: 'Rq', replica: 'q', seq: 2, op: { type: 'rm', el: 'a' }, vis: ['Aq'] },
]);
const E1 = ['Ap', 'Rp', 'Aq'], E2 = ['Aq', 'Rq', 'Ap'], U = ['Ap', 'Aq', 'Rp', 'Rq'];

test('defeater execution: lo, canonical states and the join match the worked example', () => {
  const ev = L.evaluator(orsetDatatype, orsetInstance, defeater());
  assert.deepEqual(ev.lo(E1).sort(), [['Ap', 'Rp'], ['Rp', 'Aq']]);
  assert.deepEqual(ev.lo(U).sort(), [['Ap', 'Rp'], ['Aq', 'Rq']]);
  assert.notDeepEqual(ev.lo(U).sort(), ev.lo(E1).sort());
  assert.equal(fp(ev.can(['Ap', 'Aq'])), '[[1,"a"],[2,"a"]]');
  assert.equal(fp(ev.can(E1)), '[[2,"a"]]');
  assert.equal(fp(ev.can(E2)), '[[1,"a"]]');
  assert.notEqual(fp(ev.can(E1)), fp(ev.can(['Ap', 'Aq'])));
  const merged = ev.merge(ev.can(['Ap', 'Aq']), ev.can(E1), ev.can(E2));
  assert.equal(fp(merged), '[]');
  assert.equal(fp(ev.can(U)), '[]');
  assert.notEqual(fp(merged), fp(ev.can(E1)));
  assert.notEqual(fp(merged), fp(ev.can(E2)));
});

test('defeater execution: the VC3 and VC5 states of the worked example', () => {
  const ev = L.evaluator(orsetDatatype, orsetInstance, defeater());
  // VC3 with e = R_p, maximal in U and only in E1.
  assert.equal(ev.maximal(U, 'Rp'), true);
  assert.equal(ev.maximal(E1, 'Rp'), false);
  const m = ev.can(ev.down('Rp').filter((x) => x !== 'Rp')), x = ev.can(['Ap', 'Aq']), l = ev.can(['Ap', 'Aq']), y = ev.can(E2);
  assert.equal(fp(m), '[[1,"a"]]');
  assert.equal(fp(x), '[[1,"a"],[2,"a"]]');
  assert.equal(fp(y), '[[1,"a"]]');
  const em = ev.apply(m, 'Rp');
  assert.equal(fp(em), '[]');
  const lhs = ev.merge(l, ev.merge(m, x, em), y), rhs = ev.merge(m, ev.merge(l, x, y), em);
  assert.equal(fp(lhs), '[]');
  assert.equal(fp(rhs), '[]');
  assert.equal(fp(ev.merge(l, x, y)), '[[1,"a"]]');
  assert.notEqual(fp(ev.merge(l, x, y)), fp(rhs));
  // VC5 with e = A_p on F1 = {A_p, A_q}, F2 = {A_q, R_q, A_p}.
  const F1 = ['Ap', 'Aq'], F2 = ['Aq', 'Rq', 'Ap'];
  assert.equal(ev.maximal([...new Set([...F1, ...F2])], 'Ap'), true);
  assert.equal(ev.maximal(U, 'Ap'), false);
  assert.equal(fp(ev.can(['Aq'])), '[[2,"a"]]');
  assert.equal(fp(ev.can(['Aq', 'Rq'])), '[]');
  const m5 = ev.can([]), x0 = ev.can(['Aq']), x1 = ev.can(['Aq']), x2 = ev.can(['Aq', 'Rq']), e5 = ev.apply(m5, 'Ap');
  const lhs5 = ev.merge(ev.merge(m5, x0, e5), ev.merge(m5, x1, e5), ev.merge(m5, x2, e5));
  const rhs5 = ev.merge(m5, ev.merge(x0, x1, x2), e5);
  assert.equal(fp(lhs5), '[[1,"a"]]');
  assert.equal(fp(rhs5), '[[1,"a"]]');
  assert.equal(fp(rhs5), fp(ev.can(['Ap', 'Aq', 'Rq'])));
  assert.notEqual(fp(rhs5), fp(ev.can(F1)));
});

test('orset (paper semantics): concrete checks pass; unresolved commutation is explicit', (t) => {
  const results = L.checkAll(orsetDatatype, orsetInstance, OPTS);
  report(t, results);
  for (const r of results) {
    assert.equal(r.failures.length, 0, `${r.name} failed`);
    assert.ok(r.runs > 0, `${r.name} ran no instances`);
    if (r.name === 'rcNonComm') {
      assert.equal(r.status, 'inconclusive');
      assert.ok(r.inconclusive > 0);
      assert.equal(r.pass, false);
    } else assert.equal(r.status, 'pass', r.name);
  }
});

test('orset with observed-tag removals: passes everything except spec-non-comm', (t) => {
  const results = byName(L.checkAll(orsetObservedTagsDatatype, orsetObservedTagsInstance, OPTS));
  report(t, Object.values(results));
  for (const r of Object.values(results)) if (r.name !== 'specNonComm') assert.equal(r.status, 'pass', `${r.name} did not pass`);
  const f = results.specNonComm.failures[0];
  assert.equal(f.kind, 'spec-non-commuting-pair-commutes');
  assert.equal(f.detail.semanticOracle, true);
  assert.ok(f.size <= 2);
  // Hand-derived: add_b with tag 1 and rm_b naming no tag commute in the
  // implementation, but not in the set specification.
  const add = { type: 'add', el: 'b', tag: 1 }, rm = { type: 'rm', el: 'b', tags: [] };
  const s0 = orsetObservedTagsDatatype.init();
  assert.equal(fp(run(s0, [add, rm], orsetObservedTagsDatatype)), '[[1,"b"]]');
  assert.equal(fp(run(s0, [rm, add], orsetObservedTagsDatatype)), '[[1,"b"]]');
  assert.deepEqual(run([], [add, rm], { apply: orsetInstance.spec.step }), []);
  assert.deepEqual(run([], [rm, add], { apply: orsetInstance.spec.step }), ['b']);
  // The paper's element-level removal does not commute with that addition.
  assert.notEqual(fp(run(s0, [add, { type: 'rm', el: 'b' }], orsetDatatype)), fp(run(s0, [{ type: 'rm', el: 'b' }, add], orsetDatatype)));
});

test('orset with observed-tag removals and the element-level rc: rc-non-comm fails', (t) => {
  const r = L.rcNonComm(orsetObservedTagsDatatype, orsetObservedTagsElementRcInstance, OPTS);
  report(t, [r]);
  assert.equal(r.failures[0]?.kind, 'rc-on-commuting-pair');
  assert.ok(r.failures[0].size <= 2);
  const ok = L.rcNonComm(orsetObservedTagsDatatype, orsetObservedTagsInstance, OPTS);
  assert.equal(ok.status, 'pass');
});

test('rga (runtime RGA with total effects): passes every law except spec-non-comm', (t) => {
  const results = byName(L.checkAll(rgaDatatype, rgaInstance, OPTS));
  report(t, Object.values(results));
  assert.equal(results.noRcChain.notApplicable, true);
  assert.equal(results.condComm.notApplicable, true);
  for (const r of Object.values(results)) {
    if (r.name === 'specNonComm' || r.notApplicable) continue;
    assert.equal(r.failures.length, 0, `${r.name} failed`);
    assert.equal(r.status, 'pass', `${r.name} did not pass`);
    assert.ok(r.runs > 0);
  }
  const f = results.specNonComm.failures[0];
  assert.equal(f.kind, 'spec-non-commuting-pair-commutes');
  assert.equal(f.detail.semanticOracle, true);
  assert.ok(f.size <= 2);
  // Hand-derived: ins(1, root) and del(1) commute in the grow-only
  // implementation; in the list specification del-then-ins leaves [1] and
  // ins-then-del leaves [].
  const ins1 = { type: 'ins', id: 1, el: 'x', anchorId: null }, del1 = { type: 'del', id: 1 };
  const s0 = rgaDatatype.init();
  assert.equal(rgaDatatype.serialise(run(s0, [ins1, del1], rgaDatatype)), rgaDatatype.serialise(run(s0, [del1, ins1], rgaDatatype)));
  assert.deepEqual(specRun([ins1, del1]).B, []);
  assert.deepEqual(specRun([del1, ins1]).B, [1]);
  assert.equal(listSpecCommutes(ins1, del1), false);
  // Sibling insertions: the implementation orders them by id either way;
  // the specification places the later-applied one first.
  const ins2 = { type: 'ins', id: 2, el: 'y', anchorId: null };
  assert.deepEqual(rgaDatatype.read(run(s0, [ins1, ins2], rgaDatatype)), ['y', 'x']);
  assert.deepEqual(rgaDatatype.read(run(s0, [ins2, ins1], rgaDatatype)), ['y', 'x']);
  assert.deepEqual(specRun([ins1, ins2]).B, [2, 1]);
  assert.deepEqual(specRun([ins2, ins1]).B, [1, 2]);
  assert.equal(listSpecCommutes(ins1, ins2), false);
  assert.equal(listSpecCommutes(ins1, { type: 'ins', id: 3, el: 'z', anchorId: 2 }), true);
});

test('rga with an ordering rc on commuting operations: rc-non-comm and no-rc-chain fail', (t) => {
  const rc = L.rcNonComm(rgaDatatype, rgaOrderingRcInstance, OPTS);
  const chain = L.noRcChain(rgaDatatype, rgaOrderingRcInstance, OPTS);
  report(t, [rc, chain]);
  assert.equal(rc.failures[0]?.kind, 'rc-on-commuting-pair');
  assert.ok(rc.failures[0].size <= 2);
  assert.equal(chain.failures[0]?.kind, 'rc-chain');
  assert.ok(chain.failures[0].size <= 3);
  // Hand-derived chain: ins(1) rc ins(2) rc ins(3), all at the root.
  const i = (id) => ({ type: 'ins', id, el: 'x', anchorId: null });
  assert.equal(rgaOrderingRcInstance.rc(i(1), i(2)) && rgaOrderingRcInstance.rc(i(2), i(3)), true);
  assert.equal(rgaOrderingRcInstance.rc(i(2), i(1)), false);
});

test('negative control brokenOrset: VC1 and the join fail on one event; folds stay deterministic', (t) => {
  const vc1 = L.vc1MergeComm(brokenOrsetDatatype, brokenOrsetInstance, OPTS);
  const join = L.eventSetDeterminesState(brokenOrsetDatatype, brokenOrsetInstance, { ...OPTS, parts: ['join'] });
  const ext = L.eventSetDeterminesState(brokenOrsetDatatype, brokenOrsetInstance, { ...OPTS, parts: ['extensions'] });
  report(t, [vc1, join, ext]);
  assert.equal(vc1.failures[0]?.kind, 'merge-not-commutative');
  assert.ok(vc1.failures[0].size <= 4);
  assert.equal(join.failures[0]?.kind, 'merge-not-canonical');
  assert.ok(join.failures[0].size <= 4);
  assert.equal(ext.status, 'pass');
  assert.ok(ext.runs > 0);
  // Hand-derived: l = a = ∅, b = {1:a}. (A ∩ B) ∪ (A ∖ L) = ∅ while the
  // swapped merge keeps the instance; the runtime merge keeps it both ways.
  const s0 = orsetDatatype.init(), b = orsetDatatype.apply(s0, { type: 'add', el: 'a', tag: 1 });
  assert.equal(fp(brokenOrsetDatatype.merge3(s0, s0, b)), '[]');
  assert.equal(fp(brokenOrsetDatatype.merge3(s0, b, s0)), '[[1,"a"]]');
  assert.equal(fp(orsetDatatype.merge3(s0, s0, b)), '[[1,"a"]]');
  assert.equal(fp(orsetDatatype.merge3(s0, b, s0)), '[[1,"a"]]');
});

test('negative control brokenRga: linear extensions of one event set disagree', (t) => {
  const r = L.eventSetDeterminesState(brokenRgaDatatype, brokenRgaInstance, { ...OPTS, parts: ['extensions'] });
  report(t, [r]);
  const f = r.failures[0];
  assert.equal(f?.kind, 'linear-extensions-disagree');
  assert.ok(f.size <= 4);
  assert.notDeepEqual(f.detail.state1, f.detail.state2);
  // Hand-derived: two root insertions of 'b' (ids 1, 2) and 'a' after 2.
  // Siblings ordered by element with equal elements in arrival order give
  // b a b for 1,2,3 and b b a for 2,3,1; the runtime RGA orders siblings by
  // id and reads b a b for both orders.
  const ops = [{ type: 'ins', id: 1, el: 'b', anchorId: null }, { type: 'ins', id: 2, el: 'b', anchorId: null }, { type: 'ins', id: 3, el: 'a', anchorId: 2 }];
  const other = [ops[1], ops[2], ops[0]];
  assert.deepEqual(brokenRgaDatatype.read(run(brokenRgaDatatype.init(), ops, brokenRgaDatatype)), ['b', 'a', 'b']);
  assert.deepEqual(brokenRgaDatatype.read(run(brokenRgaDatatype.init(), other, brokenRgaDatatype)), ['b', 'b', 'a']);
  assert.deepEqual(rgaDatatype.read(run(rgaDatatype.init(), ops, rgaDatatype)), ['b', 'a', 'b']);
  assert.deepEqual(rgaDatatype.read(run(rgaDatatype.init(), other, rgaDatatype)), ['b', 'a', 'b']);
  // The runtime RGA passes the same property on the same seeds.
  const ok = L.eventSetDeterminesState(rgaDatatype, rgaInstance, { ...OPTS, parts: ['extensions'] });
  assert.equal(ok.status, 'pass');
});

test('the PRNG is deterministic and seed-sensitive', () => {
  const a = L.mulberry32(7), b = L.mulberry32(7), c = L.mulberry32(8);
  const xs = [a(), a(), a()], ys = [b(), b(), b()], zs = [c(), c(), c()];
  assert.deepEqual(xs, ys);
  assert.notDeepEqual(xs, zs);
  assert.ok(xs.every((x) => x >= 0 && x < 1));
});

test('finite absence of a noncommutation witness is inconclusive, regardless of policy', () => {
  const datatype = {
    init: () => 0,
    apply: (s, o) => s < 10 ? s + 1 : o === 'a' ? 0 : 1,
    merge3: (_l, a, b) => Math.max(a, b),
    read: (s) => s,
  };
  // Hand-derived: ten a's reach 10. There a;b gives 1 and b;a gives 2.
  // A pool built from just the two generated events never reaches that state.
  const ten = run(0, Array(10).fill('a'), datatype);
  assert.equal(ten, 10);
  assert.equal(run(ten, ['a', 'b'], datatype), 1);
  assert.equal(run(ten, ['b', 'a'], datatype), 2);
  const opts = { trials: 1, maxSize: 2, perTrial: 4 };
  for (const related of [false, true]) {
    const instance = {
      replicas: 1, syncProbability: 0,
      genEvent: (_rnd, _s, ctx) => ctx.fresh() % 2 ? 'a' : 'b',
      rc: (a, b) => related && a === 'a' && b === 'b',
      // A declared policy is deliberately wrong and must not certify semantics.
      commutes: () => true,
      specCommutes: (a, b) => a === b,
    };
    for (const r of [L.rcNonComm(datatype, instance, opts), L.specNonComm(datatype, instance, opts)]) {
      assert.equal(r.status, 'inconclusive');
      assert.equal(r.pass, false);
      assert.equal(r.runs, 0);
      assert.equal(r.vacuous, 0);
      assert.equal(r.inconclusive, 1);
      assert.deepEqual(r.failures, []);
      assert.equal(r.inconclusiveExamples[0].kind, 'commutation-unresolved');
      assert.equal(r.inconclusiveExamples[0].detail.statesSearched, 5);
    }
    const aggregate = L.checkAll(datatype, instance, opts);
    for (const r of aggregate.filter((r) => ['rcNonComm', 'specNonComm'].includes(r.name))) {
      assert.equal(r.pass, false);
      assert.equal(r.status, 'inconclusive');
    }
  }
});

test('specification search exhaustion is inconclusive; a completed search can pass or fail', () => {
  const datatype = { init: () => 0, apply: (s) => s + 1, merge3: Math.max, read: (s) => s };
  const instance = {
    replicas: 1, syncProbability: 0,
    genEvent: (_rnd, _s, ctx) => ctx.fresh(),
    spec: { init: () => 0, step: (s) => s + 1, observe: (s) => s },
    observe: (s) => s,
  };
  const opts = { trials: 1, maxSize: 1, perTrial: 4 };
  const bounded = L.specConformance(datatype, instance, { ...opts, maxSpecPrefixes: 0 });
  assert.equal(bounded.status, 'inconclusive');
  assert.equal(bounded.pass, false);
  assert.ok(bounded.inconclusive > 0);
  assert.equal(bounded.runs + bounded.inconclusive, 4);
  assert.equal(bounded.vacuous, 0);
  assert.deepEqual(bounded.failures, []);
  assert.equal(bounded.inconclusiveExamples[0].kind, 'spec-search-bound-exhausted');
  assert.equal(bounded.inconclusiveExamples[0].detail.maxPrefixes, 0);
  const complete = L.specConformance(datatype, instance, opts);
  assert.equal(complete.status, 'pass');
  assert.equal(complete.pass, true);
  assert.equal(complete.inconclusive, 0);
  const wrong = L.specConformance(datatype, { ...instance, observe: () => -1 }, opts);
  assert.equal(wrong.status, 'fail');
  assert.equal(wrong.failures[0].kind, 'no-admitted-linear-extension');
});

test('maxSize bounds generation steps, including a one-event configuration', () => {
  for (const maxSize of [1, 3]) {
    let issued = 0;
    const datatype = { init: () => 0, apply: (s) => s + 1, merge3: (_l, a, b) => a + b, read: (s) => s };
    const instance = { replicas: 1, syncProbability: 0, genEvent: () => ++issued };
    const r = L.vc1MergeComm(datatype, instance, { trials: 1, maxSize });
    assert.equal(r.status, 'pass');
    assert.equal(issued, maxSize);
  }
});
