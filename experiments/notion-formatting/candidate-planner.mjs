// SPECIFIED CANDIDATE, exercised below only by finite source-module probes.
// No demo imports: the caller supplies visible order, selection, and stable IDs.
const key = id => typeof id === 'string' ? id : `${id.sessionId}:${id.counter}`;
const before = id => ({id: structuredClone(id), anchor: 'before'});

/**
 * @param {{id: string, visibleIds: (string | {sessionId: string, counter: number})[]}[]} instances
 * @param {{instanceId: string, itemId: string | {sessionId: string, counter: number}, bold: boolean}[]} selected
 * @returns {{value: boolean, segments: {textInstanceId: string, start: object, end: object}[]} | undefined}
 */
export function planToggle(instances, selected) {
  if (!selected.length) return undefined;
  const pending = new Map();
  for (const c of selected) {
    const group = pending.get(c.instanceId) ?? new Set();
    if (group.has(key(c.itemId))) throw Error('Duplicate selected address');
    group.add(key(c.itemId)); pending.set(c.instanceId, group);
  }
  const segments = [];
  for (const instance of instances) {
    const selectedIds = pending.get(instance.id);
    if (!selectedIds) continue;
    const found = new Set();
    let first;
    for (const id of instance.visibleIds) {
      if (selectedIds.has(key(id))) {
        if (found.has(key(id))) throw Error('Duplicate visible address');
        found.add(key(id)); first ??= id;
      } else if (first !== undefined) {
        segments.push({textInstanceId: instance.id, start: before(first), end: before(id)});
        first = undefined;
      }
    }
    if (first !== undefined) segments.push({textInstanceId: instance.id,
      start: before(first), end: before('end')});
    if (found.size !== selectedIds.size) throw Error('Selected address is not visible');
    pending.delete(instance.id);
  }
  if (pending.size) throw Error('Selected instance is absent');
  return {value: !selected.every(c => c.bold), segments};
}
