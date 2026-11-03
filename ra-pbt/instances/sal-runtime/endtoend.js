// End-to-end ra-pbt instances for the Sal runtime's OR-set and RGA.
//
// Replicas. Each replica is a `DistributedReplica` (runtime/src/replica.js):
// one content-addressed commit store per replica, so delivery is
// per-replica and one-directional, and merges resolve criss-crosses through
// the runtime's virtual merge base. Identities are minted by the runtime's
// Lamport mint with stride 100 and slot = replica number: the k-th fresh
// identity at a replica whose clock has seen counter c is (c + 1) * 100 + r.
// RGA insertions carry the minted id (`commitGenerated`); OR-set additions
// carry a minted tag (`mintTime`). The mint observes RGA ids on ingest, so RGA
// ids are Lamport timestamps; OR-set tags are unique but not observed.
//
// Transfers.
//   sync(to, from)       one direction of `syncReplicas`: `to` ingests the
//                        delta `from` computes against `to`'s ancestry
//                        (through the binary wire codec), then merges its
//                        head with `from`'s head. Records `from` holds but
//                        cannot yet integrate are handed on to `to` as well.
//   deliver(to, record)  a record carries its commit's ancestry closure: the
//                        delta a replica whose head is exactly that commit
//                        would send to an empty store. Delivery is causal:
//                        the record is held as pending until every authored
//                        commit in that closure other than its own is in
//                        `to`'s store; then the part of the closure `to`
//                        lacks is ingested (merge commits in it are
//                        recomputed, adding no new operation) and `to`
//                        merges its head with the record's commit. The
//                        part shipped is exactly the delta a replica whose
//                        head is that commit computes against `to`'s store:
//                        the wire codec elides the content id of a commit
//                        that is the parent of the next one. This adapter
//                        filters known commits to minimise delivery. The
//                        runtime also deduplicates reconstructed implicit
//                        ids, so overlapping unfiltered deltas are safe
//                        (runtime/test/ingest.test.js). Held records are
//                        retried after every transfer.
// A record is integrated at a replica when its commit is in the ancestry of
// the replica's head; the state vector maps each author to the number of its
// commits in that ancestry.
//
// Opened replicas. The runtime constructs replicas only empty (the root
// commit) and brings them up to date by delta sync; it has no replica built
// from a stored state other than a compaction epoch base, which neither
// datatype here supports. `createReplica(id, { opened: true })` therefore
// throws, the adapter has no `loadInto` (the determinism check is skipped),
// and the instances generate no `open` steps.
//
// Specifications.
//   OR-set: the ordinary set (`setSpec` of orset.js) over elements; spec
//   operations are `{ type: 'add', el, tag }` and `{ type: 'rm', el, tags }`
//   with the runtime's tag and the observed tags, which the set specification
//   ignores. View: the sorted element list.
//   RGA: spec operations are `{ type: 'ins', id, anchorId, el }` and
//   `{ type: 'del', id }` with the runtime's ids. Two list specifications,
//   both deterministic, with views listing `[id, el]` pairs (so no directed
//   search is needed; reports show the element list): `rgaSpec`, the
//   anchor-retaining list, in which an insertion after a deleted anchor is
//   admitted, and `rgaLiveAnchorSpec`, the identified list (`listSpec` of
//   rga.js), in which it is not. `rgaReplicated` uses the first and
//   `rgaLiveAnchorReplicated` the second.
//
// Requests.
//   OR-set: `{ kind: 'add', el }`, `{ kind: 'rm', el }`; `rm` kills the tags
//   the issuer's `observe` reports for `el`.
//   RGA: `{ kind: 'insert', index, el }` places `el` at visible position
//   `index`, anchored at the element displayed at `index - 1` (the root when
//   `index` is 0); `{ kind: 'delete', index }` deletes the element displayed
//   at `index`.

import { DistributedReplica } from '../../../runtime/src/replica.js';
import { encodeWire, decodeWire } from '../../../runtime/src/wire.js';
import { orset as runtimeOrset } from '../../../runtime/src/datatypes/orset.js';
import { rga as runtimeRga } from '../../../runtime/src/datatypes/rga.js';
import { setSpec, orsetInstance, brokenOrsetDatatype } from './orset.js';
import { listSpec, listSpecCommutes } from './rga.js';

export const MINT_STRIDE = 100;

const wire = (commits) => decodeWire(encodeWire({ t: 'delta', c: commits })).c;
const byKey = (a, b) => (a < b ? -1 : a > b ? 1 : 0);

/** Authored commits per author in the ancestry of the store's head. */
function authoredCounts(store) {
  const out = {};
  for (const cid of store.dag.ancestorSet(store.head.id)) {
    const op = store.dag.get(cid).op;
    if (op) out[op.replica] = Math.max(out[op.replica] ?? 0, op.seq + 1);
  }
  return Object.fromEntries(Object.entries(out).sort(([a], [b]) => byKey(a, b)));
}

const inAncestry = (store, gid) => {
  const cid = store.byGid.get(gid);
  return cid !== undefined && store.dag.isAncestor(cid, store.head.id);
};

/**
 * The replicated adapter over a runtime datatype. `ops` supplies the
 * datatype-specific parts:
 *   issue(store, request) -> { gid, specOps }
 *   validRequest(store, request) -> boolean
 *   view(store), inserted(record), deleted(record), present(store)
 */
function replicatedAdapter(datatype, ops) {
  const deliverable = (rep, record) => record.update.commits.every((c) => c.kind !== 'op' || c.gid === record.update.gid || rep.store.byGid.has(c.gid));

  const integrate = (rep, record) => {
    rep.store.ingest(wire(record.update.commits.filter((c) => !rep.store.byGid.has(c.gid))));
    rep.store.mergeWithGid(record.update.gid);
  };

  const drain = (rep) => {
    let progress = true;
    while (progress) {
      progress = false;
      for (const [gid, record] of rep.held) {
        if (inAncestry(rep.store, gid)) {
          rep.held.delete(gid);
          progress = true;
        } else if (deliverable(rep, record)) {
          integrate(rep, record);
          rep.held.delete(gid);
          progress = true;
        }
      }
    }
  };

  const receive = (rep, record) => {
    if (!inAncestry(rep.store, record.update.gid)) rep.held.set(record.update.gid, record);
    drain(rep);
  };

  return {
    createReplica(id, { opened = false } = {}) {
      if (opened) throw new Error('the Sal runtime has no replica constructed from a stored state; replicas start empty and catch up by delta sync');
      if (!(Number.isInteger(id) && id >= 1 && id < MINT_STRIDE)) throw new RangeError(`replica number ${id} outside the mint slots 1..${MINT_STRIDE - 1}`);
      return { id, store: new DistributedReplica(datatype, 'r' + id, { mint: { slot: id, stride: MINT_STRIDE } }), held: new Map() };
    },
    validRequest: (rep, request) => ops.validRequest(rep.store, request),
    issue(rep, request) {
      if (!ops.validRequest(rep.store, request)) throw new RangeError(`request ${JSON.stringify(request)} is invalid at replica ${rep.id}`);
      const { gid, specOps } = ops.issue(rep.store, request);
      const commits = rep.store.delta(new Set());
      return { replica: rep.id, kind: request.kind, request, update: { gid, commits }, specOps };
    },
    deliver(rep, record) {
      receive(rep, record);
      return { pending: rep.held.size > 0, emitted: [] };
    },
    sync(to, from) {
      to.store.ingest(wire(from.store.delta(to.store.ancestryGids())));
      to.store.mergeWithGid(from.store.headGid);
      for (const record of from.held.values()) if (!inAncestry(to.store, record.update.gid)) to.held.set(record.update.gid, record);
      drain(to);
      return { pending: to.held.size > 0, emitted: [] };
    },
    integrated(rep, records) {
      return new Set(records.filter((r) => inAncestry(rep.store, r.update.gid)).map((r) => r.key));
    },
    view: (rep) => ops.view(rep.store),
    stateVector: (rep) => authoredCounts(rep.store),
    hasPending: (rep) => rep.held.size > 0,
    fingerprint: (rep) => datatype.fingerprint(rep.store.head.state),
    snapshot: (rep) => ({ head: rep.store.headGid.slice(0, 12), held: rep.held.size }),
    traceRecord: (record) => ({ gid: record.update.gid.slice(0, 12), specOps: record.specOps }),
    inserted: ops.inserted,
    deleted: ops.deleted,
    present: (rep) => ops.present(rep.store),
  };
}

// ---------------------------------------------------------------- OR-set

const ELEMENTS = ['a', 'b'];

const orsetOps = {
  validRequest: (_store, request) => (request.kind === 'add' || request.kind === 'rm') && typeof request.el === 'string' && request.el.length > 0,
  issue(store, request) {
    if (request.kind === 'add') {
      const tag = store.mintTime();
      const gid = store.commit({ type: 'add', tag, el: request.el });
      return { gid, specOps: [{ type: 'add', el: request.el, tag }] };
    }
    const tags = runtimeOrset.observe(store.head.state, request.el);
    const gid = store.commit({ type: 'rm', tags });
    return { gid, specOps: [{ type: 'rm', el: request.el, tags }] };
  },
  view: (store) => runtimeOrset.read(store.head.state),
  inserted: (record) => record.specOps.filter((o) => o.type === 'add').map((o) => [o.tag, `${o.tag}=${o.el}`]),
  deleted: (record) => record.specOps.filter((o) => o.type === 'rm').flatMap((o) => o.tags),
  present: (store) => [...store.head.state.entries()].map(([tag, el]) => `${tag}=${el}`),
};

/** The ordinary set specification over elements, in ra-pbt form. */
export const orsetSpec = {
  init: () => setSpec.init(),
  apply: (state, op) => setSpec.step(state, op) ?? null,
  view: (state) => setSpec.observe(state),
  serialise: (state) => JSON.stringify(state),
  viewKey: (view) => JSON.stringify([...new Set(view)].sort(byKey)),
  localEdit(view, request) {
    if (request.kind === 'add') return [...new Set([...view, request.el])].sort(byKey);
    return view.filter((x) => x !== request.el);
  },
  rc: (o1, o2) => orsetInstance.rc(o1, o2),
};

/** Add one of a, b (probability 0.55), else remove a present element (0.8) or any. */
export function orsetNextRequest(rnd, view) {
  if (rnd.next() < 0.55) return { kind: 'add', el: rnd.pick(ELEMENTS) };
  const el = view.length && rnd.next() < 0.8 ? rnd.pick(view) : rnd.pick(ELEMENTS);
  return { kind: 'rm', el };
}

/** The same request on element a. */
export function orsetReduceRequest(request) {
  return request.el !== 'a' ? [{ reduction: 'element-a', request: { ...request, el: 'a' }, to: 'a' }] : [];
}

const noOpened = (options) => ({ ...options, openedReplicas: false });

export const orsetReplicated = {
  spec: orsetSpec,
  adapter: replicatedAdapter(runtimeOrset, orsetOps),
  nextRequest: orsetNextRequest,
  reduceRequest: orsetReduceRequest,
  generateOptions: noOpened,
};

/** Negative control: the runtime OR-set with the merge of `brokenOrsetDatatype`
 *  ((A ∩ B) ∪ (A ∖ L), forgetting instances added on the second branch). */
export const brokenOrsetRuntimeDatatype = { ...runtimeOrset, merge3: brokenOrsetDatatype.merge3 };

export const brokenOrsetReplicated = {
  ...orsetReplicated,
  adapter: replicatedAdapter(brokenOrsetRuntimeDatatype, orsetOps),
};

// ---------------------------------------------------------------- RGA

const LETTERS = ['a', 'b', 'c'];

const rgaOps = {
  validRequest(store, request) {
    const n = runtimeRga.readIds(store.head.state).length;
    if (request.kind === 'insert') return Number.isInteger(request.index) && request.index >= 0 && request.index <= n && typeof request.el === 'string';
    if (request.kind === 'delete') return Number.isInteger(request.index) && request.index >= 0 && request.index < n;
    return false;
  },
  issue(store, request) {
    const ids = runtimeRga.readIds(store.head.state);
    if (request.kind === 'insert') {
      const anchorId = request.index === 0 ? null : ids[request.index - 1];
      const { gid, payload } = store.commitGenerated({ type: 'ins', el: request.el, anchorId });
      return { gid, specOps: [{ type: 'ins', id: payload.id, anchorId, el: request.el }] };
    }
    const id = ids[request.index];
    const gid = store.commit({ type: 'del', id });
    return { gid, specOps: [{ type: 'del', id }] };
  },
  view: (store) => runtimeRga.readEntries(store.head.state).map(([id, r]) => [id, r.el]),
  inserted: (record) => record.specOps.filter((o) => o.type === 'ins').map((o) => [o.id, `${o.id}=${o.el}`]),
  deleted: (record) => record.specOps.filter((o) => o.type === 'del').map((o) => o.id),
  present: (store) => runtimeRga.readEntries(store.head.state).map(([id, r]) => `${id}=${r.el}`),
};

const elementsOf = (view) => view.map((e) => (Array.isArray(e) ? e[1] : e));

/** Shared members of the two list specifications: views list `[id, el]`
 *  pairs and are reported as element lists. */
const listViewMembers = {
  viewKey: (view) => JSON.stringify(view),
  normalise: elementsOf,
  localEdit(view, request) {
    const els = elementsOf(view);
    if (request.kind === 'insert') return [...els.slice(0, request.index), request.el, ...els.slice(request.index)];
    return [...els.slice(0, request.index), ...els.slice(request.index + 1)];
  },
};

/**
 * The live-anchor list: `listSpec` of rga.js (live ids B, allocated ids I;
 * an insertion is admitted when its id is fresh and its anchor is the root or
 * live, and is placed immediately after the anchor; a deletion removes its id
 * and is always admitted), with the element of every allocated id.
 * Deterministic.
 */
export const rgaLiveAnchorSpec = {
  ...listViewMembers,
  init: () => ({ ...listSpec.init(), els: {} }),
  apply(state, op) {
    const next = listSpec.step(state, op);
    if (!next) return null;
    return op.type === 'ins' ? { ...next, els: { ...state.els, [op.id]: op.el } } : { ...next, els: state.els };
  },
  view: (state) => state.B.map((id) => [id, state.els[id]]),
  serialise: (state) => JSON.stringify([state.B, [...state.I].sort((x, y) => x - y)]),
  rc: (o1, o2) => !listSpecCommutes(o1, o2),
};

/**
 * The anchor-retaining list: the state is the sequence of every allocated id
 * with its element and a deleted flag. An insertion is admitted when its id
 * is fresh and its anchor is the root or allocated (deleted or not), and is
 * placed immediately after the anchor; a deletion is admitted when its id is
 * allocated and sets the flag. The view lists the `[id, el]` pairs not
 * deleted. Deterministic. It differs from `rgaLiveAnchorSpec` only in
 * admitting an insertion after a deleted anchor.
 */
export const rgaSpec = {
  ...listViewMembers,
  init: () => [],
  apply(state, op) {
    if (op.type === 'ins') {
      const a = op.anchorId ?? null;
      if (!(op.id > 0) || state.some((e) => e[0] === op.id)) return null;
      const i = a === null ? 0 : state.findIndex((e) => e[0] === a) + 1;
      if (a !== null && i === 0) return null;
      return [...state.slice(0, i), [op.id, op.el, false], ...state.slice(i)];
    }
    if (op.type === 'del') {
      const i = state.findIndex((e) => e[0] === op.id);
      if (i < 0) return null;
      return state[i][2] ? state : [...state.slice(0, i), [op.id, state[i][1], true], ...state.slice(i + 1)];
    }
    return null;
  },
  view: (state) => state.filter((e) => !e[2]).map(([id, el]) => [id, el]),
  serialise: (state) => JSON.stringify(state),
  rc(o1, o2) {
    const anc = (o) => o.anchorId ?? null;
    if (o1.type === 'ins' && o2.type === 'ins') return anc(o1) === anc(o2) || anc(o1) === o2.id || anc(o2) === o1.id;
    if (o1.type === 'del' && o2.type === 'del') return false;
    const [i, d] = o1.type === 'ins' ? [o1, o2] : [o2, o1];
    return d.id === i.id;
  },
};

/** Insert one of a, b, c at a random position (probability 0.65 or on an empty list), else delete. */
export function rgaNextRequest(rnd, view) {
  if (view.length === 0 || rnd.next() < 0.65) return { kind: 'insert', index: rnd.int(0, view.length), el: rnd.pick(LETTERS) };
  return { kind: 'delete', index: rnd.int(0, view.length - 1) };
}

/** Position 0, then element a. */
export function rgaReduceRequest(request) {
  const out = [];
  if (request.index > 0) out.push({ reduction: 'index-0', request: { ...request, index: 0 }, to: 0 });
  if (request.kind === 'insert' && request.el !== 'a') out.push({ reduction: 'element-a', request: { ...request, el: 'a' }, to: 'a' });
  return out;
}

export const rgaReplicated = {
  spec: rgaSpec,
  adapter: replicatedAdapter(runtimeRga, rgaOps),
  nextRequest: rgaNextRequest,
  reduceRequest: rgaReduceRequest,
  generateOptions: noOpened,
};

/** The same replicas checked against the live-anchor list. */
export const rgaLiveAnchorReplicated = { ...rgaReplicated, spec: rgaLiveAnchorSpec };
