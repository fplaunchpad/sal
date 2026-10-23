// Offline source oracle. Expectations and rival outputs below are hand-derived.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {RgaText} from './rga.js';
import {resolveRichText} from './rich-text.js';
import {START, END, idKey, compareOpIds} from './ids.js';

const typedId = id => typeof id === 'string' ? {kind: id} : {kind: 'op', ...id};
const anchorPosition = (a, t) => a.id === START ? 0 : a.id === END ? t.items.length :
  ((a.anchor ?? a.affinity) === 'before' ? t.entryById : t.exitById).get(idKey(a.id)) ?? null;
const exportedAnchor = (a, t) => ({id: typedId(a.id), side: a.anchor ?? a.affinity,
  position: anchorPosition(a, t)});
export function exportInstance(instance) {
  const t = instance.rga.traversal();
  return {id: instance.id, traversal: t.items.map((x, index) => ({index, id: typedId(x.id),
    origin: typedId(x.originId), kind: x.kind, text: x.content ?? '', deleted: x.deleted,
    entry: t.entryById.get(idKey(x.id)), exit: t.exitById.get(idKey(x.id))})),
  operations: [...instance.annotationOperations].sort((a, b) => compareOpIds(a.id, b.id)).map(o => {
    const start = exportedAnchor(o.start, t), end = exportedAnchor(o.end, t);
    return {id: typedId(o.id), value: o.value, start, end,
      coveredIndices: t.items.flatMap((_, i) => start.position !== null && end.position !== null &&
        start.position <= i && i < end.position ? [i] : [])};
  }), resolved: resolveRichText(instance.rga, instance.annotationOperations).map(c =>
    ({id: typedId(c.id), text: c.text, bold: c.bold}))};
}
const view = r => { const d = r.document(); return d.aliveBlocks().map(b => ({block: b.id,
  text: d.blockText(b.id), bits: d.blockCharacters(b.id).map(c => +c.bold).join('')})); };
const plainView = r => view(r).map(({text, bits}) => [text, bits]);
const exportReplica = r => ({transactions: r.transactions(), display: view(r),
  instances: [...r.document().instances.values()].map(exportInstance)});
const fresh = (texts = ['abc']) => { const r = new Replica('S', 'S', []); let last;
  for (const text of texts) { last = r.createBlock(last).newBlockId; r.insertText(last, 0, text); }
  return r; };
const block = (r, i = 0) => r.document().aliveBlocks()[i].id;
const cases = [];
function check(name, r, expected, rejected, extra = {}) {
  const actual = plainView(r);
  assert.deepEqual(actual, expected, name);
  assert.notDeepEqual(actual, rejected, name + ': negative control must distinguish rival');
  cases.push({name, evidence: 'measured', expected, rejected, controlsHold: true,
    ...extra, fixture: exportReplica(r)});
}

// The interval starts before b and ends before its original successor c.
for (const [name, at, expected, rejected] of [
  ['insert before selection', 1, [['aXbc', '0010']], [['aXbc', '0110']]],
  ['insert at right boundary', 2, [['abXc', '0110']], [['abXc', '0100']]],
  ['insert before whole text', 0, [['Xabc', '0010']], [['Xabc', '1010']]],
]) {
  const r = fresh(); r.toggleBold(block(r), 1, 2); r.insertText(block(r), at, 'X');
  check(name, r, expected, rejected);
}
{
  const r = fresh(['abcd']); r.toggleBold(block(r), 1, 3); r.insertText(block(r), 2, 'X');
  check('insert inside selection', r, [['abXcd', '01110']], [['abXcd', '01010']]);
}
{
  const r = fresh(); r.toggleBold(block(r), 2, 3); r.insertText(block(r), 3, 'X');
  check('END boundary grows', r, [['abcX', '0011']], [['abcX', '0010']]);
}
{
  const r = fresh(); r.toggleBold(block(r), 1, 2); r.deleteText(block(r), 1, 2);
  check('selected tombstone disappears', r, [['ac', '00']], [['abc', '010']]);
  r.insertText(block(r), 1, 'X');
  check('deleted start anchor stays after newer sibling', r, [['aXc', '000']], [['aXc', '010']]);
}
{
  const r = fresh(); r.toggleBold(block(r), 1, 2); r.deleteText(block(r), 2, 3);
  r.insertText(block(r), 2, 'X');
  check('deleted successor still bounds inherited insertion', r, [['abX', '011']], [['abX', '010']]);
}
{
  const r = fresh(['abcd']); r.toggleBold(block(r), 1, 3); r.splitBlock(block(r), 2);
  check('split preserves existing instance marks', r, [['ab', '01'], ['cd', '10']], [['ab', '00'], ['cd', '00']]);
  r.insertText(block(r, 1), 0, 'X');
  check('insertion after split marker inherits', r, [['ab', '01'], ['Xcd', '110']], [['ab', '01'], ['Xcd', '010']]);
  r.mergeBlock(block(r, 1));
  check('merge preserves existing instance marks', r, [['abXcd', '01110']], [['abXcd', '00000']]);
}
{
  const r = fresh(['ab', 'cd']); r.mergeBlock(block(r, 1)); r.toggleBold(block(r), 1, 2);
  const before = plainView(r), transaction = r.toggleBold(block(r), 0, 4);
  assert.equal(transaction.operations.length, 2);
  assert.deepEqual(transaction.operations.map(o => o.command), ['addAnnotation', 'addAnnotation']);
  assert.equal(idKey(transaction.id), idKey(transaction.operations[0].args.id));
  assert.ok(compareOpIds(transaction.operations[0].args.id, transaction.operations[1].args.id) < 0);
  check('mixed selection adds across two instances atomically', r, [['abcd', '1111']], [['abcd', '1011']],
    {before, transaction, operationCount: 2});
  const remove = r.toggleBold(block(r), 0, 4);
  assert.deepEqual(remove.operations.map(o => o.command), ['removeAnnotation', 'removeAnnotation']);
  check('all-bold selection removes across two instances', r, [['abcd', '0000']], [['abcd', '1111']],
    {transaction: remove, operationCount: 2});
}
{
  const r = fresh(['ab']); r.splitBlock(block(r), 1);
  const middle = r.createBlock(block(r)).newBlockId; r.insertText(middle, 0, 'X');
  r.mergeBlock(block(r, 1)); r.mergeBlock(block(r, 1));
  const transaction = r.toggleBold(block(r), 0, 3);
  const instances = transaction.operations.map(o => o.args.textInstanceId);
  assert.equal(instances.length, 3); assert.equal(instances[0], instances[2]);
  assert.notEqual(instances[0], instances[1]);
  check('one instance revisited produces three adjacent segments', r, [['aXb', '111']], [['aXb', '101']],
    {transaction, operationCount: 3, segmentInstanceIds: instances});
}

const sourceFailures = [];
function sourceFailure(name, r, expected, observed, transaction) {
  assert.deepEqual(plainView(r), observed, name + ': recorded source failure');
  assert.notDeepEqual(plainView(r), expected, name + ': refutes exact selected effect');
  sourceFailures.push({name, evidence: 'refuted-by-execution', expected, observed,
    controlsHold: true, transaction, fixture: exportReplica(r)});
}
{
  const s = fresh(['ab']), id = block(s), a = new Replica('A', 'A', s.transactions()),
    b = new Replica('B', 'B', s.transactions());
  const left = a.splitBlock(id, 0), right = b.splitBlock(id, 1);
  a.receive(right.transaction); a.mergeBlock(left.newBlockId);
  const transaction = a.toggleBold(right.newBlockId, 0, 2);
  sourceFailure('N-002 reordered selection produces equal endpoints', a, [['', ''], ['ba', '11']],
    [['', ''], ['ba', '00']], transaction);
}
{
  const s = fresh(), id = block(s), a = new Replica('A', 'A', s.transactions()),
    b = new Replica('B', 'B', s.transactions());
  a.splitBlock(id, 1); const right = b.splitBlock(id, 2); a.receive(right.transaction);
  a.mergeBlock(right.newBlockId);
  const transaction = a.toggleBold(id, 0, 2);
  sourceFailure('N-003 interval crosses unselected displayed slot', a,
    [['ac', '11'], ['b', '0']], [['ac', '11'], ['b', '1']], transaction);
}

// Reordering receipt does not change the same Lamport-ID annotation winner.
for (const names of [['A', 'B'], ['B', 'A']]) {
  const seed = fresh(), a = new Replica(names[0], names[0], seed.transactions()),
    b = new Replica(names[1], names[1], seed.transactions());
  const addA = a.toggleBold(block(a), 1, 2), addB = b.toggleBold(block(b), 1, 2);
  // Both start by adding. B's second operation removes and has a larger counter.
  const removeB = b.toggleBold(block(b), 1, 2);
  a.receive(removeB); a.receive(addB); b.receive(addA);
  assert.deepEqual(plainView(a), plainView(b));
  check('larger-counter removal wins ' + names.join('/'), a, [['abc', '000']], [['abc', '010']]);
}

const rawCases = [];
function raw(name, rga, operations, expected, rejected, positions) {
  const instance = {id: 'raw', rga, annotationOperations: operations};
  const fixture = exportInstance(instance), actual = fixture.resolved.map(c => [c.text, c.bold]);
  assert.deepEqual(actual, expected, name); assert.notDeepEqual(actual, rejected, name);
  if (positions) assert.deepEqual(fixture.operations.map(o => [o.start.position, o.end.position]), positions);
  rawCases.push({name, evidence: 'measured', expected, rejected, controlsHold: true, fixture});
}
const op = (s, c) => ({sessionId: s, counter: c});
const anchor = (id, side = 'before') => ({id, anchor: side});
const mark = (id, start, end, value) => ({id, start, end, value});
{
  // a's subtree is a,b,c; X is a following root sibling. after(a)=3, not 1.
  const rga = new RgaText(); rga.insertRun(op('A', 2), START, 'abc');
  rga.insertRun(op('B', 1), START, 'X');
  raw('after means subtree exit', rga, [mark(op('M', 9), anchor(START), anchor(op('A', 2), 'after'), true)],
    [['a', true], ['b', true], ['c', true], ['X', false]],
    [['a', true], ['b', false], ['c', false], ['X', false]], [[0, 3]]);
  raw('after start excludes descendants', rga, [mark(op('M', 9), anchor(op('A', 2), 'after'), anchor(END), true)],
    [['a', false], ['b', false], ['c', false], ['X', true]],
    [['a', false], ['b', true], ['c', true], ['X', true]], [[3, 4]]);
}
{
  const rga = new RgaText(); rga.insertRun(op('A', 1), START, 'ab');
  const add = mark(op('A', 8), anchor(START), anchor(END), true),
    remove = mark(op('B', 8), anchor(START), anchor(END), false);
  raw('ID sort beats list order and session breaks tie', rga, [remove, add],
    [['a', false], ['b', false]], [['a', true], ['b', true]], [[0, 2], [0, 2]]);
  raw('missing anchor covers nothing', rga, [mark(op('M', 9), anchor(op('Z', 99)), anchor(END), true)],
    [['a', false], ['b', false]], [['a', true], ['b', true]], [[null, 2]]);
  raw('reversed interval covers nothing', rga, [mark(op('M', 9), anchor(op('A', 2)), anchor(op('A', 1)), true)],
    [['a', false], ['b', false]], [['a', true], ['b', true]], [[1, 0]]);
}

// Concurrent insertion at the original right boundary inherits even if the
// inserting replica did not observe the mark. Receipt orders are reversed.
for (const order of ['mark-first', 'insert-first']) {
  const s = fresh(), a = new Replica('A', 'A', s.transactions()), b = new Replica('B', 'B', s.transactions());
  const m = a.toggleBold(block(a), 1, 2), i = b.insertText(block(b), 2, 'X');
  const r = new Replica('R', 'R', s.transactions());
  for (const t of order === 'mark-first' ? [m, i] : [i, m]) r.receive(t);
  check('unobserved right-boundary insertion ' + order, r, [['abXc', '0110']], [['abXc', '0100']]);
}
console.log(JSON.stringify({schema: 'notion-formatting-fixture-v1', cases, rawCases, sourceFailures,
  summary: {clientCases: cases.length, rawCases: rawCases.length, sourceFailures: sourceFailures.length,
    positiveAndNegativeControls: cases.length + rawCases.length + sourceFailures.length}}));
