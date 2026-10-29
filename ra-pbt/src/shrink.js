/**
 * Greedy shrinking of a failing schedule.
 *
 * `fails(schedule)` re-executes from scratch and reports whether the failure
 * of interest is still present; a schedule that cannot be executed (an
 * out-of-range request, a send of a missing record, a rejected request) or
 * whose predicate throws counts as not failing.
 *
 * A `send` names a record by its position in the sender's record list, and
 * that list also holds cleanup records produced by transfers, so positions
 * shift when steps are removed. During shrinking each send instead refers to
 * the step that produced its record and to the record's rank among that
 * step's products; every candidate is re-executed to recompute positions, and
 * a send whose producing step is gone is dropped with it.
 *
 * Reductions, each kept only when the failure persists:
 *   remove-step      drop one step (and the sends of the records it produced);
 *   reduce-request   replace an edit's request by one of the instance's
 *                    `reduceRequest(request)` candidates, tried in order; the
 *                    first that keeps the failure is taken.
 * `reduceRequest` returns smaller requests, each either a request or
 * { request, reduction, to } naming the reduction for the report. Removal is
 * repeated to a fixpoint before the request reductions, and the whole cycle
 * repeats until nothing changes. The result is minimal under these
 * reductions, not a globally shortest failing schedule.
 */
import { Execution, prepareInstance } from './schedule.js';
import { stepRequest } from './adapter.js';

/** Annotated steps: { step, ref? } where ref = { producer, rank } names the step that produced a send's record. */
function annotate(inst, schedule) {
  const ex = new Execution(inst, schedule.replicas, { checks: [] });
  const items = schedule.steps.map((step) => ({ step }));
  const producerOf = new Map();
  items.forEach((it, i) => {
    if (it.step.type === 'send') {
      const rec = ex.ownOps[it.step.from][it.step.op];
      if (rec) it.ref = producerOf.get(rec.key);
    }
    ex.apply(it.step);
    ex.produced[i].forEach((key, rank) => producerOf.set(key, { producer: it, rank }));
  });
  return items;
}

/** Concrete schedule from annotated steps, or null when it cannot be executed. */
function materialise(inst, base, items) {
  const ex = new Execution(inst, base.replicas, { checks: [] });
  const keyOf = new Map();
  const steps = [];
  try {
    for (const it of items) {
      let step = it.step;
      if (step.type === 'send' && it.ref) {
        const key = keyOf.get(it.ref.producer)?.[it.ref.rank];
        if (key === undefined) continue;
        const op = ex.ownOps[step.from].findIndex((o) => o.key === key);
        if (op < 0) return null;
        step = { ...step, op };
      }
      ex.apply(step);
      keyOf.set(it, ex.produced[ex.produced.length - 1]);
      steps.push(step);
    }
  } catch {
    return null;
  }
  return { ...base, steps };
}

function safeFails(fails, schedule) {
  if (schedule === null) return false;
  try {
    return fails(schedule);
  } catch {
    return false;
  }
}

/** Candidate edit steps from the instance's request reducer. */
function reducedSteps(inst, step) {
  if (step.type !== 'edit' || typeof inst.reduceRequest !== 'function') return [];
  return inst.reduceRequest(stepRequest(step)).map((c) => {
    const labelled = c && typeof c === 'object' && 'request' in c && typeof c.request === 'object';
    const request = labelled ? c.request : c;
    const next = { type: step.type, replica: step.replica, ...request };
    return { step: next, note: labelled ? { reduction: c.reduction ?? 'reduce-request', step, to: c.to ?? next } : { reduction: 'reduce-request', step, to: next } };
  });
}

/** shrink(instance, schedule, fails) returns { schedule, reductions, executions }. */
export function shrink(instance, schedule, fails) {
  const inst = prepareInstance(instance);
  let items = annotate(inst, schedule);
  let cur = schedule;
  const reductions = [];
  let executions = 0;
  const attempt = (candItems, note) => {
    executions++;
    const cand = materialise(inst, schedule, candItems);
    if (safeFails(fails, cand)) {
      items = candItems.filter((it) => it.step.type !== 'send' || !it.ref || candItems.includes(it.ref.producer));
      cur = cand;
      reductions.push(note);
      return true;
    }
    return false;
  };
  const replace = (i, step) => {
    const old = items[i];
    const fresh = { step };
    return items.map((it, j) => (j === i ? fresh : it.ref?.producer === old ? { ...it, ref: { ...it.ref, producer: fresh } } : it));
  };
  let changed = true;
  while (changed) {
    changed = false;
    let removed = true;
    while (removed) {
      removed = false;
      for (let i = items.length - 1; i >= 0; i--) {
        if (i >= items.length) continue;
        const s = items[i].step;
        if (attempt(items.filter((_, j) => j !== i), { reduction: 'remove-step', step: s })) {
          removed = true;
          changed = true;
        }
      }
    }
    for (let i = 0; i < items.length; i++) {
      for (const c of reducedSteps(inst, items[i].step)) {
        if (attempt(replace(i, c.step), c.note)) {
          changed = true;
          break;
        }
      }
    }
  }
  return { schedule: cur, reductions, executions };
}
