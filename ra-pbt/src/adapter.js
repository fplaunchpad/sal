/**
 * Implementation adapters.
 *
 * An adapter connects the implementation under test to the schedule
 * executor. Replicas are numbered 1..n; the replica objects are the
 * adapter's own and are only passed back to it.
 *
 * Required members:
 *
 *   createReplica(id, { opened = false })
 *       A fresh replica. With `opened`, the replica will receive an existing
 *       state through `loadInto` before any other use, as a client opening a
 *       stored document does.
 *   issue(replica, request) -> record
 *       Issues a request locally. The record is
 *         { replica, kind, request, update, deps?, specOps: [op] }
 *       where `update` is an opaque serialisable payload that `deliver` can
 *       apply elsewhere, and `specOps` are the specification operations the
 *       request denotes, including the identities the implementation
 *       assigned. Throws a RangeError for a request the implementation
 *       rejects.
 *   deliver(replica, record) -> { pending, emitted: [record] }
 *       Applies one record received from another replica. `pending` reports
 *       whether the replica holds received state it cannot yet integrate;
 *       `emitted` lists records the replica issued on its own while
 *       integrating (cleanup records), which must be propagated like any
 *       other record. A cleanup record has `kind: 'cleanup'` and no specOps.
 *   sync(to, from) -> { pending?, emitted: [record] }
 *       Brings `to` up to date with everything `from` holds.
 *   view(replica)
 *       The replica's observable value in the specification's view format,
 *       with identities when the specification or its classifier needs them;
 *       views are compared by the specification's key.
 *   stateVector(replica)
 *       A JSON-serialisable summary of what the replica holds; replicas with
 *       equal state vectors, equal integrated records and nothing pending
 *       must display the same value.
 *   hasPending(replica)
 *       Whether the replica holds received state it has not integrated.
 *   validRequest(replica, request)
 *       False (or a thrown RangeError) when the request is out of range for
 *       the replica's current state.
 *
 * Optional members:
 *
 *   loadInto(replica, source)           gives an opened replica `source`'s whole state
 *   integrated(replica, records)        which received records are fully
 *       integrated: a Set of record keys, or { integrated: Set, partial: [key] }
 *       when the adapter can tell records whose effect is partly present. The
 *       default treats a record carrying `dot: [origin, counter]` (counters
 *       from 1) as integrated when the replica's state vector maps `origin`
 *       to at least `counter`.
 *   displayed(replica)                  the value as displayed, compared by the
 *       convergence, localMeaning and determinism checks; defaults to view
 *   fingerprint(replica)                a string compared alongside the
 *       displayed value by the convergence check
 *   requestOf(step)                     the request of an edit step; defaults
 *       to the step without `type` and `replica`
 *   snapshot(replica)                   extra fields recorded in each snapshot
 *   traceRecord(record)                 extra fields of a record in a trace
 *   crossCheck(record, records)         notes on inconsistencies between a new
 *       record's dependencies and the implementation's own account of them;
 *       each becomes an execution anomaly
 *   inserted(record) -> [[key, label]], deleted(record) -> [key],
 *   present(replica) -> [label]         element accounting for the
 *       conservation check: after the final sync every replica presents
 *       exactly the inserted labels whose keys were never deleted
 */

const REQUIRED = ['createReplica', 'issue', 'deliver', 'sync', 'view', 'stateVector', 'hasPending', 'validRequest'];
const NORMALISED = Symbol('ra-pbt.adapter');

/** Integration by state vector and record dots. */
export function integratedByDots(adapter, replica, records) {
  const sv = adapter.stateVector(replica);
  const out = new Set();
  for (const r of records) {
    if (!Array.isArray(r.dot)) throw new TypeError(`record ${r.key} carries no dot; the adapter must provide integrated()`);
    if ((sv[String(r.dot[0])] ?? 0) >= r.dot[1]) out.add(r.key);
  }
  return out;
}

/** The request of an edit step: the step without `type` and `replica`, keys in order. */
export function stepRequest(step) {
  const { type: _t, replica: _r, final: _f, ...request } = step;
  return request;
}

/**
 * Validates an adapter and returns it with every optional member filled in.
 * Throws a TypeError naming the missing required members. Idempotent.
 */
export function checkAdapter(adapter) {
  if (adapter && adapter[NORMALISED]) return adapter;
  const missing = REQUIRED.filter((k) => typeof adapter?.[k] !== 'function');
  if (missing.length) throw new TypeError('adapter lacks ' + missing.join(', '));
  const a = {
    displayed: (rep) => adapter.view(rep),
    fingerprint: null,
    requestOf: stepRequest,
    snapshot: () => ({}),
    traceRecord: () => ({}),
    crossCheck: () => [],
    loadInto: null,
    inserted: null,
    deleted: null,
    present: null,
    ...adapter,
    [NORMALISED]: true,
  };
  if (typeof adapter.integrated !== 'function') a.integrated = (rep, records) => integratedByDots(a, rep, records);
  a.supportsOpen = typeof a.loadInto === 'function';
  a.supportsConservation = typeof a.inserted === 'function' && typeof a.deleted === 'function' && typeof a.present === 'function';
  return a;
}
