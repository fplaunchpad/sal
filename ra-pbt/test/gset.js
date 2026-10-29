/**
 * A grow-only set of strings as an in-process ra-pbt instance.
 *
 * Specification: the state is the sorted array of distinct elements; `add`
 * inserts one. Replicas keep a log of records and deliver each replica's
 * records in counter order (a record arriving early is held as pending). A
 * record carries the dot [replica, counter], so integration uses the
 * default state-vector rule.
 *
 * `droppingGSet` is a deliberately wrong implementation: on integrating a
 * remote record a replica also forgets its own most recent element.
 */

const sortedUnique = (xs) => [...new Set(xs)].sort();

export const gsetSpec = {
  init: () => [],
  apply: (state, op) => (op.kind === 'add' ? sortedUnique([...state, op.value]) : null),
  view: (state) => state,
  serialise: (state) => JSON.stringify(state),
  viewKey: (view) => JSON.stringify(sortedUnique(view)),
  localEdit: (view, request) => sortedUnique([...view, request.value]),
  rc: () => false,
};

function makeAdapter({ dropOwnOnRemote }) {
  const integrate = (rep, record) => {
    const [client, counter] = record.dot;
    rep.sv[client] = counter;
    rep.log.push(record);
    rep.elements.set(client + ':' + counter, record.update.value);
    if (dropOwnOnRemote && client !== rep.id) {
      const own = rep.log.filter((r) => r.dot[0] === rep.id && rep.elements.has(r.dot.join(':')));
      if (own.length) rep.elements.delete(own[own.length - 1].dot.join(':'));
    }
  };
  const drain = (rep) => {
    let progress = true;
    while (progress) {
      progress = false;
      for (const [k, r] of rep.buffer) {
        if ((rep.sv[r.dot[0]] ?? 0) + 1 === r.dot[1]) {
          rep.buffer.delete(k);
          integrate(rep, r);
          progress = true;
        }
      }
    }
  };
  const receive = (rep, record) => {
    const [client, counter] = record.dot;
    if ((rep.sv[client] ?? 0) >= counter) return;
    rep.buffer.set(client + ':' + counter, record);
    drain(rep);
  };
  return {
    createReplica: (id) => ({ id, sv: {}, log: [], elements: new Map(), buffer: new Map() }),
    loadInto(rep, source) {
      for (const r of source.log) receive(rep, r);
    },
    validRequest: (rep, request) => request.kind === 'add' && typeof request.value === 'string' && request.value.length > 0,
    issue(rep, request) {
      if (request.kind !== 'add') throw new RangeError('unknown request ' + request.kind);
      const dot = [rep.id, (rep.sv[rep.id] ?? 0) + 1];
      const record = { replica: rep.id, kind: 'add', request, update: { value: request.value }, dot, specOps: [{ kind: 'add', value: request.value }] };
      integrate(rep, record);
      return record;
    },
    deliver(rep, record) {
      receive(rep, record);
      return { pending: rep.buffer.size > 0, emitted: [] };
    },
    sync(to, from) {
      const records = [...from.log].sort((a, b) => a.dot[0] - b.dot[0] || a.dot[1] - b.dot[1]);
      for (const r of records) receive(to, r);
      return { pending: to.buffer.size > 0, emitted: [] };
    },
    view: (rep) => sortedUnique([...rep.elements.values()]),
    stateVector: (rep) => Object.fromEntries(Object.entries(rep.sv).sort(([a], [b]) => Number(a) - Number(b))),
    hasPending: (rep) => rep.buffer.size > 0,
    inserted: (record) => (record.kind === 'add' ? [[record.dot.join(':'), record.dot.join(':') + '=' + record.update.value]] : []),
    deleted: () => [],
    present: (rep) => [...rep.elements].map(([k, v]) => k + '=' + v),
  };
}

const LETTERS = 'abcdefgh';

/** Requests: add one random letter, or two letters with probability one quarter. */
export function nextRequest(rnd) {
  const value = rnd.next() < 0.25 ? rnd.pick([...LETTERS]) + rnd.pick([...LETTERS]) : rnd.pick([...LETTERS]);
  return { kind: 'add', value };
}

/** A shorter value: the value without its last character. */
export function reduceRequest(request) {
  return request.value.length > 1 ? [{ ...request, value: request.value.slice(0, -1) }] : [];
}

export const gset = { spec: gsetSpec, adapter: makeAdapter({ dropOwnOnRemote: false }), nextRequest, reduceRequest };
export const droppingGSet = { spec: gsetSpec, adapter: makeAdapter({ dropOwnOnRemote: true }), nextRequest, reduceRequest };
