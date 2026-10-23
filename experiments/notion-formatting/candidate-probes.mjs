// A separate experiment: planner output is applied as ordinary source ops in
// temporary modules. The original toggleBold implementation is never replaced.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {planToggle} from './candidate-planner.mjs';

const key = id => typeof id === 'string' ? id : `${id.sessionId}:${id.counter}`;
const block = (r, i = 0) => r.document().aliveBlocks()[i].id;
const view = r => { const d = r.document(); return d.aliveBlocks().map(b =>
  [d.blockText(b.id), d.blockCharacters(b.id).map(c => +c.bold).join('')]); };
function fresh(text = 'abc') {
  const r = new Replica('S', 'S', []), id = r.createBlock().newBlockId;
  r.insertText(id, 0, text); return r;
}
const rows = [];
function applyCandidate(r, target, start, end) {
  const d = r.document(), selected = d.blockCharacters(target).slice(start, end);
  const instances = [...d.instances.values()].map(i => ({id: i.id,
    visibleIds: i.rga.visibleItems().map(c => c.id)}));
  const selection = selected.map(c => ({instanceId: c.textInstanceId, itemId: c.item.id, bold: c.bold}));
  const plan = planToggle(instances, selection);
  if (!plan) return undefined;
  // Finite coverage check uses literal current traversal coordinates directly,
  // independently from the planner's maximal-run construction.
  const wanted = new Set(selection.map(c => `${c.instanceId}/${key(c.itemId)}`)), covered = new Set();
  for (const i of d.instances.values()) {
    const t = i.rga.traversal();
    for (const c of i.rga.visibleItems()) {
      const at = t.entryById.get(key(c.id));
      if (plan.segments.filter(s => s.textInstanceId === i.id).some(s => {
        const a = t.entryById.get(key(s.start.id));
        const b = s.end.id === 'end' ? t.items.length : t.entryById.get(key(s.end.id));
        return a <= at && at < b;
      })) covered.add(`${i.id}/${key(c.id)}`);
    }
  }
  assert.deepEqual([...covered].sort(), [...wanted].sort(), 'finite exact coverage');
  const operations = plan.segments.map(s => ({command: plan.value ? 'addAnnotation' : 'removeAnnotation',
    pointer: {table: 'block', id: target}, path: [], opVersion: 2,
    args: {...s, searchLabel: selected.find(c => c.textInstanceId === s.textInstanceId).searchLabel,
      id: r.clock.reserve(), ...(plan.value ? {annotation: ['b']} : {annotationKey: 'b'})}}));
  const transaction = {id: operations[0].args.id, operations};
  r.receive(transaction);
  return {plan, selection, finiteExactCoverage: true, transaction};
}
function check(name, r, expected, rejected, preparation, extra = {}) {
  const actual = view(r); assert.deepEqual(actual, expected, name); assert.notDeepEqual(actual, rejected, name);
  rows.push({name, implementation: 'candidate-planner', evidence: 'measured', expected, rejected,
    actual, controlsHold: true, preparation, ...extra, transactions: r.transactions()});
}
for (const [name, at, expected, rejected] of [
  ['candidate insertion at left boundary', 1, [['aXbc', '0010']], [['aXbc', '0110']]],
  ['candidate insertion at right boundary', 2, [['abXc', '0110']], [['abXc', '0100']]],
]) {
  const r = fresh(), preparation = applyCandidate(r, block(r), 1, 2);
  r.insertText(block(r), at, 'X'); check(name, r, expected, rejected, preparation);
}
{
  const r = fresh('abcd'), preparation = applyCandidate(r, block(r), 1, 3);
  r.insertText(block(r), 2, 'X');
  check('candidate interior insertion', r, [['abXcd', '01110']], [['abXcd', '01010']], preparation);
}
{
  const r = fresh(), preparation = applyCandidate(r, block(r), 2, 3);
  r.insertText(block(r), 3, 'X');
  check('candidate END growth', r, [['abcX', '0011']], [['abcX', '0010']], preparation);
}
for (const which of ['start', 'successor']) {
  const r = fresh(), preparation = applyCandidate(r, block(r), 1, 2);
  if (which === 'start') {
    r.deleteText(block(r), 1, 2); r.insertText(block(r), 1, 'X');
    check('candidate deleted start', r, [['aXc', '000']], [['aXc', '010']], preparation);
  } else {
    r.deleteText(block(r), 2, 3); r.insertText(block(r), 2, 'X');
    check('candidate deleted successor', r, [['abX', '011']], [['abX', '010']], preparation);
  }
}
{
  const s = fresh('ab'), id = block(s), a = new Replica('A', 'A', s.transactions()),
    b = new Replica('B', 'B', s.transactions());
  const left = a.splitBlock(id, 0), right = b.splitBlock(id, 1);
  a.receive(right.transaction); a.mergeBlock(left.newBlockId);
  const preparation = applyCandidate(a, right.newBlockId, 0, 2);
  assert.equal(preparation.plan.segments.length, 1);
  check('candidate N-002 coverage', a, [['', ''], ['ba', '11']], [['', ''], ['ba', '00']], preparation);
}
{
  const s = fresh(), id = block(s), a = new Replica('A', 'A', s.transactions()),
    b = new Replica('B', 'B', s.transactions());
  a.splitBlock(id, 1); const right = b.splitBlock(id, 2); a.receive(right.transaction);
  a.mergeBlock(right.newBlockId);
  const preparation = applyCandidate(a, id, 0, 2);
  assert.equal(preparation.plan.segments.length, 2);
  check('candidate N-003 coverage', a, [['ac', '11'], ['b', '0']], [['ac', '11'], ['b', '1']], preparation);
  // Display end of ac is physically after c, inside c..END.
  a.insertText(id, 2, 'X');
  check('candidate N-003 right boundary grows without selecting b', a,
    [['acX', '111'], ['b', '0']], [['acX', '110'], ['b', '0']], preparation);
  // Display between a,c is physically after a and before unselected b: it
  // belongs to the a..before(b) run and inherits there as well.
  a.insertText(id, 1, 'Y');
  check('candidate N-003 internal displayed gap grows before b', a,
    [['aYcX', '1111'], ['b', '0']], [['aYcX', '1011'], ['b', '0']], preparation);
}
{
  const r = fresh('ab'), other = r.createBlock(block(r)).newBlockId; r.insertText(other, 0, 'cd');
  r.mergeBlock(other); r.toggleBold(block(r), 1, 2);
  const preparation = applyCandidate(r, block(r), 0, 4);
  assert.equal(preparation.plan.segments.length, 2);
  check('candidate mixed multi-instance add', r, [['abcd', '1111']], [['abcd', '1011']], preparation);
  const removal = applyCandidate(r, block(r), 0, 4);
  check('candidate multi-instance remove', r, [['abcd', '0000']], [['abcd', '1111']], removal);
}

{
  const r = fresh('ab'); r.splitBlock(block(r), 1);
  const middle = r.createBlock(block(r)).newBlockId; r.insertText(middle, 0, 'X');
  r.mergeBlock(block(r, 1)); r.mergeBlock(block(r, 1));
  const preparation = applyCandidate(r, block(r), 0, 3);
  // The legacy planner emits A,B,A. Canonical physical runs need only A,B.
  assert.equal(preparation.plan.segments.length, 2);
  check('candidate repeated-instance selection', r, [['aXb', '111']], [['aXb', '101']], preparation);
}
for (const order of ['mark-first', 'insert-first']) {
  const seed = fresh(), a = new Replica('A', 'A', seed.transactions()), b = new Replica('B', 'B', seed.transactions());
  const preparation = applyCandidate(a, block(a), 1, 2), insertion = b.insertText(block(b), 2, 'X');
  const r = new Replica('R', 'R', seed.transactions());
  for (const tx of order === 'mark-first' ? [preparation.transaction, insertion] : [insertion, preparation.transaction]) r.receive(tx);
  check('candidate unobserved right-boundary insertion ' + order, r,
    [['abXc', '0110']], [['abXc', '0100']], preparation);
}

// Concurrent structural requests see the same initial document as the issuer
// of the mark. Test both causal delivery orders, not just a local edit suffix.
for (const scenario of ['delete', 'split', 'merge']) {
  for (const markFirst of [true, false]) {
    const seed = fresh(scenario === 'merge' ? 'ab' : 'abcd');
    let selectedBlock = block(seed);
    if (scenario === 'merge') {
      selectedBlock = seed.createBlock(block(seed)).newBlockId;
      seed.insertText(selectedBlock, 0, 'cd');
    }
    const a = new Replica('A', 'A', seed.transactions());
    const b = new Replica('B', 'B', seed.transactions());
    const preparation = applyCandidate(a, selectedBlock,
      scenario === 'merge' ? 0 : 1, scenario === 'merge' ? 1 : 3);
    const structural = scenario === 'delete' ? b.deleteText(block(b), 1, 2)
      : scenario === 'split' ? b.splitBlock(block(b), 2)
        : b.mergeBlock(selectedBlock);
    const structuralTransaction = scenario === 'delete' ? structural : structural.transaction;
    const r = new Replica('R', 'R', seed.transactions());
    for (const tx of markFirst ? [preparation.transaction, structuralTransaction]
      : [structuralTransaction, preparation.transaction]) r.receive(tx);
    const expected = scenario === 'delete' ? [['acd', '010']]
      : scenario === 'split' ? [['ab', '01'], ['cd', '10']]
        : [['abcd', '0010']];
    const rejected = scenario === 'delete' ? [['acd', '000']]
      : scenario === 'split' ? [['ab', '01'], ['cd', '00']]
        : [['abcd', '0000']];
    check(`candidate concurrent ${scenario} ${markFirst ? 'mark-first' : 'structure-first'}`,
      r, expected, rejected, preparation);
  }
}

// A bounded combinatorial coverage gate: every nonempty subset, every display
// permutation of that subset, every deletion mask on the other IDs. Values
// change the globally chosen Boolean, never the interval partition.
let enumerated = 0;
const ids = ['a', 'b', 'c', 'd'];
function permutations(xs) { return xs.length ? xs.flatMap((x, i) =>
  permutations(xs.filter((_, j) => i !== j)).map(ys => [x, ...ys])) : [[]]; }
for (let chosen = 1; chosen < 16; chosen++) {
  const selected = ids.filter((_, i) => chosen & (1 << i)), unselected = ids.filter(x => !selected.includes(x));
  for (let deleted = 0; deleted < (1 << unselected.length); deleted++) {
    const visible = ids.filter(x => !unselected.some((y, i) => x === y && (deleted & (1 << i))));
    for (const order of permutations(selected)) for (const allBold of [false, true]) {
      const plan = planToggle([{id: 'I', visibleIds: visible}],
        order.map(x => ({instanceId: 'I', itemId: x, bold: allBold})));
      const covered = visible.filter((x, i) => plan.segments.some(s => visible.indexOf(s.start.id) <= i &&
        i < (s.end.id === 'end' ? visible.length : visible.indexOf(s.end.id))));
      assert.deepEqual(covered, selected);
      assert.equal(plan.value, !allBold);
      assert.notDeepEqual(covered, []); // reject the empty planner on every case
      enumerated++;
    }
  }
}
console.log(JSON.stringify({schema: 'notion-formatting-candidate-v1',
  status: 'finite-tests-only; no general refinement or RA theorem', cases: rows,
  summary: {sourceAppliedCases: rows.length, positiveAndNegativeControls: rows.length,
    finiteExactCoverageCases: enumerated}}));
