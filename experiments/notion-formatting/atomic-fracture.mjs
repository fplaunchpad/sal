// Finite source oracle for the corrected maximal-run formatting candidate.
// This is an atomicity obstruction, not a new original-demo regression.
// Public source requests create every displayed selection and clock value.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {compareOpIds, idKey} from './ids.js';
import {planToggle} from './candidate-planner.mjs';

const copy = value => structuredClone(value);
const view = replica => {
  const document = replica.document();
  return document.aliveBlocks().map(block => ({id: block.id,
    text: document.blockText(block.id),
    bits: document.blockCharacters(block.id).map(character => +character.bold).join('')}));
};
const nonempty = replica => view(replica).filter(block => block.text.length)
  .map(({text, bits}) => [text, bits]);
const characters = replica => {
  const document = replica.document();
  return document.aliveBlocks().flatMap(block => document.blockCharacters(block.id));
};
const identity = character => `${character.textInstanceId}/${idKey(character.item.id)}`;
const byIdentity = replica => characters(replica).map(character =>
  [identity(character), character.bold]).sort((left, right) => left[0].localeCompare(right[0]));

// Local copy of candidate-probes.mjs's source-operation adapter. The original
// replica.toggleBold and the independent planner remain untouched. Additional
// checks pin positional guards, whole-document exactness and normal clocks.
function applyCandidate(replica, target, start, end) {
  const document = replica.document();
  assert(document.aliveBlocks().some(block => block.id === target), 'live target block');
  const blockCharacters = document.blockCharacters(target);
  assert(Number.isSafeInteger(start) && Number.isSafeInteger(end));
  assert(0 <= start && start < end && end <= blockCharacters.length, 'valid displayed range');
  const selected = blockCharacters.slice(start, end);
  const selection = selected.map(character => ({instanceId: character.textInstanceId,
    itemId: character.item.id, bold: character.bold}));
  const instances = [...document.instances.values()].map(instance => ({id: instance.id,
    visibleIds: instance.rga.visibleItems().map(item => item.id)}));
  const plan = planToggle(instances, selection);
  assert(plan && plan.segments.length > 0, 'nonempty maximal-run plan');
  const wanted = new Set(selected.map(identity)), covered = new Set();
  for (const instance of document.instances.values()) {
    const traversal = instance.rga.traversal();
    for (const item of instance.rga.visibleItems()) {
      const at = traversal.entryById.get(idKey(item.id));
      if (plan.segments.filter(segment => segment.textInstanceId === instance.id).some(segment => {
        const lower = traversal.entryById.get(idKey(segment.start.id));
        const upper = segment.end.id === 'end' ? traversal.items.length
          : traversal.entryById.get(idKey(segment.end.id));
        return lower <= at && at < upper;
      })) covered.add(`${instance.id}/${idKey(item.id)}`);
    }
  }
  assert.deepEqual([...covered].sort(), [...wanted].sort(), 'exact current visible coverage');
  const before = byIdentity(replica), clockBefore = replica.clock.counter;
  const operations = plan.segments.map(segment => ({
    command: plan.value ? 'addAnnotation' : 'removeAnnotation',
    pointer: {table: 'block', id: target}, path: [], opVersion: 2,
    args: {...segment,
      searchLabel: selected.find(character => character.textInstanceId === segment.textInstanceId).searchLabel,
      id: replica.clock.reserve(), ...(plan.value ? {annotation: ['b']} : {annotationKey: 'b'})},
  }));
  const transaction = {id: operations[0].args.id, operations};
  replica.receive(transaction);
  assert.deepEqual(operations.map(operation => operation.args.id), operations.map((_, index) =>
    ({sessionId: replica.sessionId, counter: clockBefore + index + 1})), 'actual consecutive reservations');
  assert.equal(replica.clock.counter, clockBefore + operations.length);
  const expected = before.map(([address, bold]) => [address, wanted.has(address) ? plan.value : bold]);
  assert.deepEqual(byIdentity(replica), expected, 'locally exact whole-document update');
  assert.notDeepEqual(byIdentity(replica), before, 'local format is not a no-op');
  return {request: {target, start, end}, selectedText: selected.map(character => character.text).join(''),
    selection: copy(selection), value: plan.value, segments: copy(plan.segments),
    clockBefore, clockAfter: replica.clock.counter, operationIds: operations.map(operation => copy(operation.args.id)),
    guards: {liveTarget: true, boundedDisplayedRange: true, finiteExactCoverage: true,
      locallyExact: true, effectNotNoop: true, actualConsecutiveReservations: true}, transaction};
}

const seed = new Replica('S', 'S', []);
const root = seed.createBlock().newBlockId;
seed.insertText(root, 0, 'abcde');
assert.deepEqual(nonempty(seed), [['abcde', '00000']]);
const initialMark = seed.toggleBold(root, 1, 4);
assert.equal(idKey(initialMark.id), 'S:7');
assert.deepEqual(nonempty(seed), [['abcde', '01110']]);
assert.notDeepEqual(nonempty(seed), [['abcde', '11111']]);
const base = copy(seed.transactions());
const A = new Replica('A', 'A', base), B = new Replica('B', 'B', base), C = new Replica('C', 'C', base);

const splitA = A.splitBlock(root, 2), splitC = C.splitBlock(root, 3);
assert.equal(idKey(splitA.transaction.id), 'A:8');
assert.equal(idKey(splitC.transaction.id), 'C:8');
A.receive(splitC.transaction);
assert.deepEqual(nonempty(A), [['ab', '01'], ['de', '10'], ['c', '1']]);
const beforeMerge = view(A), merge = A.mergeBlock(splitC.newBlockId);
assert(merge && merge.targetBlockId === root, 'actual previous block is ab');
assert.equal(idKey(merge.transaction.id), 'A:9');
assert.deepEqual(nonempty(A), [['abde', '0110'], ['c', '1']]);
const paddingA = A.createBlock();
assert.equal(idKey(paddingA.transaction.id), 'A:10');
const paddingB = [B.createBlock(), B.createBlock(), B.createBlock()];
assert.deepEqual(paddingB.map(padding => idKey(padding.transaction.id)), ['B:8', 'B:9', 'B:10']);
assert.deepEqual(nonempty(B), [['abcde', '01110']]);
assert.equal(A.clock.counter, 10);
assert.equal(B.clock.counter, 10);
const beforeA = view(A), beforeB = view(B);
const preparedA = applyCandidate(A, root, 0, 4);
const preparedB = applyCandidate(B, root, 1, 4);
assert.equal(preparedA.selectedText, 'abde');
assert.equal(preparedB.selectedText, 'bcd');
assert.deepEqual(preparedA.operationIds.map(idKey), ['A:11', 'A:12']);
assert.deepEqual(preparedB.operationIds.map(idKey), ['B:11']);
assert.equal(preparedA.value, true);
assert.equal(preparedB.value, false);
assert.equal(preparedA.segments.length, 2);
assert.equal(preparedB.segments.length, 1);
assert.deepEqual(nonempty(A), [['abde', '1111'], ['c', '1']]);
assert.deepEqual(nonempty(B), [['abcde', '00000']]);

const annotationIds = [...preparedA.operationIds, ...preparedB.operationIds];
assert.equal(new Set(annotationIds.map(idKey)).size, 3, 'fresh disjoint annotation IDs');
assert(annotationIds.every(id => id.counter > 7), 'new annotations follow initial marking');
assert.deepEqual([...annotationIds].sort(compareOpIds).map(idKey), ['A:11', 'B:11', 'A:12']);
const seedCharacters = characters(seed);
const sourceIdentityOrder = seedCharacters.map(identity);
assert.deepEqual(seedCharacters.map(character => idKey(character.item.id)), ['S:2', 'S:3', 'S:4', 'S:5', 'S:6']);
const physicalFlags = replica => {
  const current = new Map(byIdentity(replica));
  assert(sourceIdentityOrder.every(address => current.has(address)), 'all five original identities remain visible');
  return sourceIdentityOrder.map(address => +current.get(address)).join('');
};
const expectedFlags = '10011';
const deliveries = [];
for (const order of ['A-then-B', 'B-then-A']) {
  const receiver = new Replica('R', 'R', []);
  const archives = order === 'A-then-B' ? [A.transactions(), B.transactions()] : [B.transactions(), A.transactions()];
  for (const archive of archives) for (const transaction of archive) receiver.receive(transaction);
  assert.equal(physicalFlags(receiver), expectedFlags);
  assert.deepEqual(nonempty(receiver), [['abde', '1011'], ['c', '0']]);
  assert.notEqual(physicalFlags(receiver), '10001', 'reject atomic A-before-B result');
  assert.notEqual(physicalFlags(receiver), '11011', 'reject atomic B-before-A result');
  deliveries.push({order, physicalByOriginalIdentity: sourceIdentityOrder.map((address, index) =>
    ({address, character: 'abcde'[index], bold: expectedFlags[index] === '1'})),
    flags: physicalFlags(receiver), view: view(receiver),
    nonemptyView: nonempty(receiver), transactions: copy(receiver.transactions())});
}

// Independent exact-selection atomic oracle. No planner, anchor evaluator or
// source renderer computes these expected outcomes. Reordering a complete
// operation always writes one verdict to every one of its selected IDs.
const targets = {M: [1, 2, 3], A: [0, 1, 3, 4], B: [1, 2, 3]};
const issuedVerdicts = {M: true, A: true, B: false};
const orders = ['MAB', 'MBA', 'AMB', 'ABM', 'BMA', 'BAM'];
function atomic(order, prepared) {
  const flags = [false, false, false, false, false];
  for (const event of order) {
    const selected = targets[event];
    const value = prepared ? issuedVerdicts[event] : !selected.every(index => flags[index]);
    for (const index of selected) flags[index] = value;
  }
  return flags.map(Number).join('');
}
const serialOrders = orders.map(order => ({order, recomputedToggle: atomic(order, false),
  retainedIssuerVerdict: atomic(order, true)}));
assert.deepEqual([...new Set(serialOrders.map(row => row.recomputedToggle))].sort(), ['10001', '11011']);
for (const row of serialOrders) {
  assert.notEqual(row.recomputedToggle, expectedFlags);
  assert.notEqual(row.retainedIssuerVerdict, expectedFlags);
  assert.equal(row.recomputedToggle[1], row.recomputedToggle[3], 'atomic b,d invariant');
  assert.equal(row.retainedIssuerVerdict[1], row.retainedIssuerVerdict[3], 'prepared atomic b,d invariant');
}

console.log(JSON.stringify({schema: 'notion-formatting-atomic-fracture-v1',
  evidence: 'measured finite source execution plus independent finite atomic oracle',
  subject: 'corrected maximal-run interval candidate with per-segment Lamport priorities',
  classification: 'atomic-selection refinement obstruction; not a new original-demo N-number',
  sourcePolicy: 'hash-pinned modules; corrected merge variant only; original toggleBold unchanged; separate candidate planner',
  normalisation: {source: 'create S:1; text S:2..S:6; initial mark S:7; format A:11,A:12 and B:11',
    lean: 'atomic bootstrap chars 1..5 session UTF16 [65]; initial mark6; format A:10,A:11 and B:10',
    instance: 'source S-block-1 corresponds to Lean initial instance 0',
    correspondence: 'manual correspondence of character IDs and later operations: subtract one from counters and rename seed session S to Lean bootstrap A; source create+insert is represented by one typed factory bootstrap, not a proved full-trace extraction'},
  trace: {root, base, initialMark, splitA, splitC, beforeMerge, merge,
    paddingA, paddingB, beforeA, beforeB, preparedA, preparedB,
    publicRequests: [
      {replica: 'S', request: 'createBlock', result: root},
      {replica: 'S', request: 'insertText', block: root, index: 0, text: 'abcde'},
      {replica: 'S', request: 'toggleBold', block: root, start: 1, end: 4},
      {request: 'fork', from: 'S', to: ['A', 'B', 'C']},
      {replica: 'A', request: 'splitBlock', block: root, index: 2},
      {replica: 'C', request: 'splitBlock', block: root, index: 3},
      {replica: 'A', request: 'receive', transaction: idKey(splitC.transaction.id)},
      {replica: 'A', request: 'mergeBlock', block: splitC.newBlockId, actualPrevious: root},
      {replica: 'A', request: 'createBlock', after: null},
      ...paddingB.map(() => ({replica: 'B', request: 'createBlock', after: null})),
      {replica: 'A', request: 'candidateToggle', block: root, start: 0, end: 4},
      {replica: 'B', request: 'candidateToggle', block: root, start: 1, end: 4},
      {request: 'receiveCompleteArchives', orders: ['A-then-B', 'B-then-A']},
    ],
    archiveA: copy(A.transactions()), archiveB: copy(B.transactions())},
  deliveries, serialOrders,
  controls: {actualDisplayedSelections: true, actualClockReservations: true,
    initialMarkLocallyExact: true, bothCandidatesLocallyExact: true,
    freshDisjointReservedRuns: true, perSegmentPriorityInterleaving: ['A:11', 'B:11', 'A:12'],
    deliveryOrdersAgree: true, preservesFiveVisibleCharacters: true,
    differsFromAllSixAtomicOrders: true, differsWithRetainedIssuerVerdicts: true,
    fractureIsSharedIntersection: {b: false, d: true}},
  summary: {sourceReceivers: deliveries.length, atomicOrdersChecked: serialOrders.length,
    flags: expectedFlags, nonemptyView: [['abde', '1011'], ['c', '0']], passFailControlsHold: true}}));
