// Corrected maximal-run planner plus one transaction priority. The patched
// document dispatcher derives that priority from transaction.id, never an
// independently supplied per-segment field. Segment args.id remain distinct.
import assert from 'node:assert/strict';
import {idKey} from './ids.js';
import {planToggle} from './candidate-planner.mjs';

export const identity = character => `${character.textInstanceId}/${idKey(character.item.id)}`;
export const view = replica => {
  const document = replica.document();
  return document.aliveBlocks().map(block => [document.blockText(block.id),
    document.blockCharacters(block.id).map(character => +character.bold).join('')]);
};
export const nonemptyView = replica => view(replica).filter(([text]) => text.length);
export const byIdentity = replica => {
  const document = replica.document();
  return document.aliveBlocks().flatMap(block => document.blockCharacters(block.id))
    .map(character => [identity(character), character.bold]).sort((a, b) => a[0].localeCompare(b[0]));
};

export function atomicToggle(replica, target, start, end) {
  const document = replica.document();
  assert(document.aliveBlocks().some(block => block.id === target), 'live target');
  const characters = document.blockCharacters(target);
  assert(Number.isSafeInteger(start) && Number.isSafeInteger(end));
  assert(0 <= start && start < end && end <= characters.length, 'valid positional selection');
  const selected = characters.slice(start, end);
  const plan = planToggle([...document.instances.values()].map(instance => ({id: instance.id,
    visibleIds: instance.rga.visibleItems().map(item => item.id)})), selected.map(character => ({
      instanceId: character.textInstanceId, itemId: character.item.id, bold: character.bold})));
  assert(plan && plan.segments.length > 0);
  const wanted = new Set(selected.map(identity)), covered = new Set();
  for (const instance of document.instances.values()) {
    const traversal = instance.rga.traversal();
    for (const item of instance.rga.visibleItems()) {
      const index = traversal.entryById.get(idKey(item.id));
      if (plan.segments.some(segment => {
        if (segment.textInstanceId !== instance.id) return false;
        const lower = traversal.entryById.get(idKey(segment.start.id));
        const upper = segment.end.id === 'end' ? traversal.items.length
          : traversal.entryById.get(idKey(segment.end.id));
        return lower <= index && index < upper;
      })) covered.add(`${instance.id}/${idKey(item.id)}`);
    }
  }
  assert.deepEqual([...covered].sort(), [...wanted].sort(), 'independent current-coverage check');
  const previous = byIdentity(replica), clockBefore = replica.clock.counter;
  const operations = plan.segments.map(segment => ({
    command: plan.value ? 'addAnnotation' : 'removeAnnotation',
    pointer: {table: 'block', id: target}, path: [], opVersion: 2,
    args: {...segment,
      searchLabel: selected.find(character => character.textInstanceId === segment.textInstanceId).searchLabel,
      id: replica.clock.reserve(), ...(plan.value ? {annotation: ['b']} : {annotationKey: 'b'})},
  }));
  const transaction = {id: operations[0].args.id, operations};
  replica.receive(transaction);
  assert.equal(replica.clock.counter, clockBefore + operations.length);
  assert.deepEqual(operations.map(operation => operation.args.id), operations.map((_, i) =>
    ({sessionId: replica.sessionId, counter: clockBefore + i + 1})));
  const expected = previous.map(([address, bold]) => [address, wanted.has(address) ? plan.value : bold]);
  assert.deepEqual(byIdentity(replica), expected, 'one complete locally exact assignment');
  for (const instance of replica.document().instances.values()) {
    for (const operation of instance.annotationOperations.filter(op =>
      operations.some(segment => idKey(segment.args.id) === idKey(op.id)))) {
      assert.equal(idKey(operation.priority), idKey(transaction.id), 'all parts share outer priority');
    }
  }
  return {transaction, selectedText: selected.map(character => character.text).join(''),
    selectedIds: selected.map(identity), value: plan.value,
    segments: plan.segments.length, priority: transaction.id,
    segmentIds: operations.map(operation => operation.args.id), clockBefore, clockAfter: replica.clock.counter};
}
