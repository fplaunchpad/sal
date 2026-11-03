/**
 * Regressions: minimal schedules with hand-derived expected outcomes.
 *
 * A regression is either a procedure
 *
 *   { name, schedule?, run(results) }
 *       `run` throws (for instance through node:assert) when the regression
 *       does not hold, and may record `results.observed` and
 *       `results.admitted` for the report;
 *
 * or a declaration
 *
 *   { name, schedule, replicas?: [r], observed, notObserved?: [view],
 *     admitted: [view], witness: boolean, finalSync?: false,
 *     controls?: [regression] }
 *
 * checked as follows: the schedule is executed without checks (and with the
 * final sync when `finalSync`); at each listed replica (default: all) the
 * displayed value equals `observed` and none of `notObserved`; the views the
 * specification admits for the replica's integrated records are exactly
 * `admitted` (as a set, under `viewKey`); a witness for the replica's view
 * exists exactly when `witness` is true, and `witness` agrees with whether
 * `observed` is admitted. Every control is a regression of its own that must
 * hold; a failing regression is meant to carry a control that changes one
 * ingredient and passes.
 */
import { Execution, prepareInstance } from './schedule.js';
import { eventsAt } from './checks.js';
import { findWitness, allFinalViews } from './witness.js';

function fail(message) {
  throw new Error(message);
}

/** Whether two lists of views are equal as sets under the specification's `viewKey`. */
export function sameViewSet(spec, a, b) {
  const ka = new Set(a.map((x) => spec.viewKey(x)));
  const kb = new Set(b.map((x) => spec.viewKey(x)));
  return ka.size === kb.size && [...ka].every((k) => kb.has(k));
}

/** Checks one declared regression; throws with a message naming the first violated expectation. */
export function checkDeclared(instance, c, results = {}) {
  const inst = prepareInstance(instance);
  const { spec, adapter } = inst;
  const ex = new Execution(inst, c.schedule.replicas, { checks: [] });
  for (const s of c.schedule.steps) ex.apply(s);
  if (c.finalSync) ex.finish();
  const replicas = c.replicas ?? Array.from({ length: c.schedule.replicas }, (_, i) => i + 1);
  const observedKey = spec.viewKey(c.observed);
  const admittedKeys = new Set(c.admitted.map((x) => spec.viewKey(x)));
  if (admittedKeys.has(observedKey) !== c.witness)
    fail(`declaration inconsistent: observed is ${c.witness ? 'not ' : ''}among the admitted views but witness is ${c.witness}`);
  for (const r of replicas) {
    const rep = ex.replica(r);
    const shown = spec.normalise(adapter.displayed(rep));
    if (spec.viewKey(shown) !== observedKey) fail(`replica ${r}: observed ${JSON.stringify(shown)}, expected ${JSON.stringify(spec.normalise(c.observed))}`);
    for (const w of c.notObserved ?? []) if (spec.viewKey(shown) === spec.viewKey(w)) fail(`replica ${r}: shows the excluded view ${JSON.stringify(spec.normalise(w))}`);
    const { events } = eventsAt(ex, r);
    const admitted = allFinalViews(spec, events);
    if (admitted.truncated) fail(`replica ${r}: the admitted views were truncated`);
    if (!sameViewSet(spec, admitted, c.admitted)) fail(`replica ${r}: admitted ${JSON.stringify(admitted.map(spec.normalise))}, expected ${JSON.stringify(c.admitted.map(spec.normalise))}`);
    const w = findWitness(spec, events, adapter.view(rep));
    if (w.found !== c.witness) fail(`replica ${r}: witness ${w.found ? 'found' : 'not found'}`);
    if (results.observed === undefined) results.observed = shown;
  }
  results.admitted = c.admitted;
  for (const control of c.controls ?? []) {
    const r = runRegression(instance, control);
    if (!r.pass) fail(`control "${control.name}": ${r.error}`);
  }
  return results;
}

/** Runs one regression; returns { name, pass, error?, results }. */
export function runRegression(instance, c) {
  const results = {};
  try {
    if (typeof c.run === 'function') c.run(results);
    else checkDeclared(instance, c, results);
    return { name: c.name, pass: true, results };
  } catch (e) {
    return { name: c.name, pass: false, error: e.message, results };
  }
}

/** Runs every regression; returns [{ name, pass, error?, results }]. `instance` is needed only by declarations. */
export function runRegressions(cases, instance = null) {
  return cases.map((c) => runRegression(instance, c));
}
