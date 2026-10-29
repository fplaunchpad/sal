/**
 * Replayable schedules over numbered replicas, and their execution.
 *
 * An instance is { spec, adapter, ...hooks } (see spec.js, adapter.js and
 * generate.js). A schedule is { replicas: n, steps: [step] } over replicas
 * 1..n. Steps:
 *
 *   { type: 'edit', replica, ...request }  issue the request at `replica`
 *   { type: 'deliver', from, to }          sync `to` with everything `from` holds
 *   { type: 'send', from, to, op }         deliver `from`'s record number `op`
 *                                          (position in from's own record list,
 *                                          cleanup records included) to `to`
 *   { type: 'open', replica, from }        construct `replica` as an opened
 *                                          replica holding `from`'s whole state;
 *                                          must be the first step mentioning
 *                                          `replica`, after `from` was used
 *
 * Replicas not opened are created fresh.
 *
 * Executing a schedule yields a trace: every record in issue order with a key
 * 'r<replica>#<n>' and its causal past (`deps`: the records integrated at the
 * issuing replica when it was issued), a snapshot after every step, and the
 * results of the checks in checks.js.
 *
 * Integration. A record is received at a replica when the replica issued it,
 * was sent it, or synced with a replica that had received it. Which received
 * records are integrated (their whole effect present) and which are partly
 * integrated is the adapter's judgement (`adapter.integrated`). The
 * specification has no event for a partly integrated record, so versions
 * holding one are not checked for RA-linearizability.
 *
 * Cleanup records. Records an implementation emits on its own while
 * integrating a remote record are registered as records of the receiver:
 * their past is everything integrated at the receiver, they carry no
 * specification operations, and they occupy positions in the receiver's
 * record list, so `send` can forward them like any other record.
 */
import { normaliseSpec } from './spec.js';
import { checkAdapter } from './adapter.js';
import { CHECKS, runStepChecks, runPreEditChecks, runFinalChecks, newCheckState } from './checks.js';

const PREPARED = new WeakMap();

/** The instance with its specification and adapter normalised. */
export function prepareInstance(instance) {
  if (PREPARED.has(instance)) return PREPARED.get(instance);
  if (!instance || !instance.spec || !instance.adapter) throw new TypeError('an instance needs a spec and an adapter');
  const out = { ...instance, spec: normaliseSpec(instance.spec), adapter: checkAdapter(instance.adapter) };
  PREPARED.set(instance, out);
  PREPARED.set(out, out);
  return out;
}

/** The final-sync round: every ordered pair once. */
export function finalSyncSteps(n) {
  const out = [];
  for (let a = 1; a <= n; a++) for (let b = 1; b <= n; b++) if (a !== b) out.push({ type: 'deliver', from: a, to: b, final: true });
  return out;
}

/** The replica a step acts on: the issuer of an edit, the opened replica, or the receiver of a transfer. */
export function actorOf(step) {
  return step.type === 'edit' || step.type === 'open' ? step.replica : step.to;
}

/**
 * An incremental execution of a schedule. `checks` lists check names from
 * checks.js (empty for a bare run).
 */
export class Execution {
  constructor(instance, n, { checks = CHECKS, witnessBound = 12, witnessStateLimit } = {}) {
    const inst = prepareInstance(instance);
    this.instance = inst;
    this.spec = inst.spec;
    this.adapter = inst.adapter;
    this.n = n;
    this.replicas = {};
    this.ownOps = {};
    this.received = {};
    this.integrated = {};
    this.partial = {};
    this.opened = new Set();
    for (let r = 1; r <= n; r++) {
      this.replicas[r] = this.adapter.createReplica(r, { opened: false });
      this.ownOps[r] = [];
      this.received[r] = new Set();
      this.integrated[r] = new Set();
      this.partial[r] = [];
    }
    this.mentioned = new Set();
    this.ops = [];
    this.byKey = new Map();
    this.steps = [];
    this.produced = [];
    this.snapshots = [];
    this.anomalies = [];
    this.stats = { edits: 0, deliveries: 0, sends: 0, pendingSends: 0, cleanups: 0, opens: 0 };
    this.checkNames = checks;
    this.checkState = newCheckState(checks, { witnessBound, witnessStateLimit });
  }

  replica(r) {
    const x = this.replicas[r];
    if (!x) throw new RangeError('no replica ' + r);
    return x;
  }

  /** Recomputes the integrated and partly integrated records at replica r. */
  refresh(r) {
    const records = [...this.received[r]].map((k) => this.byKey.get(k));
    const res = this.adapter.integrated(this.replicas[r], records);
    if (res instanceof Set) {
      this.integrated[r] = res;
      this.partial[r] = [];
    } else {
      this.integrated[r] = res.integrated;
      this.partial[r] = res.partial ?? [];
    }
  }

  /** Applies one step; throws on an invalid step. Returns the record of an edit. */
  apply(step) {
    const index = this.steps.length;
    if (step.type === 'open') return this._open(step, index);
    let result;
    if (step.type === 'edit') result = this._edit(step, index);
    else if (step.type === 'deliver' || step.type === 'send') result = this._transfer(step, index);
    else throw new Error('unknown step type ' + step.type);
    for (const r of [step.replica, step.from, step.to]) if (r !== undefined) this.mentioned.add(r);
    return result;
  }

  _snapshot(index, r, extra) {
    const rep = this.replicas[r];
    return { step: index, replica: r, ...extra, visible: this.adapter.displayed(rep), ...this.adapter.snapshot(rep) };
  }

  _open(step, index) {
    const r = step.replica;
    this.replica(r);
    this.replica(step.from);
    if (!this.adapter.supportsOpen) throw new Error('the adapter does not support opened replicas');
    if (r === step.from) throw new RangeError('open from self');
    if (this.mentioned.has(r)) throw new RangeError(`open of replica ${r} after it was used`);
    if (!this.mentioned.has(step.from)) throw new RangeError(`open from replica ${step.from} before it was used`);
    this.mentioned.add(r);
    const rep = this.adapter.createReplica(r, { opened: true });
    this.adapter.loadInto(rep, this.replicas[step.from]);
    this.replicas[r] = rep;
    this.opened.add(r);
    for (const k of this.received[step.from]) this.received[r].add(k);
    this.refresh(r);
    this.stats.opens++;
    this.produced.push([]);
    this.steps.push(step);
    this.snapshots.push(this._snapshot(index, r, { opened: true }));
    runStepChecks(this, { index, step, actor: r });
  }

  _edit(step, index) {
    const r = step.replica;
    const rep = this.replica(r);
    const request = this.adapter.requestOf(step);
    const before = this.adapter.displayed(rep);
    if (this.adapter.validRequest(rep, request) === false) throw new RangeError(`request ${JSON.stringify(request)} is invalid at replica ${r}`);
    runPreEditChecks(this, { index, step, request, actor: r, before });
    const record = this.adapter.issue(rep, request);
    this._register(r, record, index);
    for (const note of this.adapter.crossCheck(record, this.ops)) this.anomalies.push({ step: record.step, replica: record.replica, note });
    this.produced.push([record.key]);
    this.stats.edits++;
    this.steps.push(step);
    this.snapshots.push(this._snapshot(index, r, { op: record.key }));
    runStepChecks(this, { index, step, request, actor: r, before, record });
    return record;
  }

  /** Records a locally issued record of replica r (an edit or a cleanup) and refreshes r. */
  _register(r, record, index) {
    record.key = `r${r}#${this.ownOps[r].length}`;
    record.seq = this.ops.length;
    record.step = index;
    record.deps = [...this.integrated[r]].sort();
    if (!Array.isArray(record.specOps)) record.specOps = [];
    this.ops.push(record);
    this.byKey.set(record.key, record);
    this.ownOps[r].push(record);
    this.received[r].add(record.key);
    this.refresh(r);
    if (!this.integrated[r].has(record.key)) this.anomalies.push({ step: index, replica: r, note: `own op ${record.key} not integrated` });
  }

  _transfer(step, index) {
    const from = this.replica(step.from);
    const to = this.replica(step.to);
    if (step.from === step.to) throw new RangeError('transfer to self');
    let result;
    if (step.type === 'deliver') {
      result = this.adapter.sync(to, from);
      for (const k of this.received[step.from]) this.received[step.to].add(k);
      this.stats.deliveries++;
    } else {
      const record = this.ownOps[step.from][step.op];
      if (!record) throw new RangeError(`replica ${step.from} has no op ${step.op}`);
      result = this.adapter.deliver(to, record);
      this.received[step.to].add(record.key);
      this.stats.sends++;
      if (result.pending) this.stats.pendingSends++;
    }
    this.refresh(step.to);
    const cleanups = (result.emitted ?? []).map((rec) => {
      this._register(step.to, rec, index);
      this.stats.cleanups++;
      return rec.key;
    });
    this.produced.push(cleanups);
    this.steps.push(step);
    const snap = this._snapshot(index, step.to, {});
    if (step.type === 'send') snap.pending = result.pending;
    if (cleanups.length) snap.cleanups = cleanups;
    this.snapshots.push(snap);
    runStepChecks(this, { index, step, actor: step.to });
    return result;
  }

  /**
   * The final sync: rounds over every ordered pair, repeated until a round
   * emits no cleanup record (a cleanup emitted late in a round is carried
   * only by the next one), at most eight rounds. Then the end-of-schedule
   * checks.
   */
  finish() {
    for (let round = 0; round < 8; round++) {
      const before = this.stats.cleanups;
      for (const s of finalSyncSteps(this.n)) this.apply(s);
      if (this.stats.cleanups === before) break;
    }
    runFinalChecks(this);
  }

  /** The serialisable trace. */
  trace(schedule) {
    return {
      schedule,
      ops: this.ops.map((o) => ({ key: o.key, replica: o.replica, kind: o.kind, request: o.request, deps: o.deps, ...this.adapter.traceRecord(o), step: o.step })),
      snapshots: this.snapshots,
      anomalies: this.anomalies,
      stats: { ...this.stats, ...this.checkState.stats },
      checks: this.checkState.results(),
    };
  }
}

/**
 * Executes a schedule on fresh replicas, followed by the final sync. Throws
 * when a step is invalid (an out-of-range request, an unknown record, a
 * request the implementation rejects).
 */
export function execute(instance, schedule, { checks = CHECKS, witnessBound = 12, witnessStateLimit, finalSync = true } = {}) {
  const ex = new Execution(instance, schedule.replicas, { checks, witnessBound, witnessStateLimit });
  for (const s of schedule.steps) ex.apply(s);
  if (finalSync) ex.finish();
  return ex.trace(schedule);
}
