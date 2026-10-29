/**
 * Checks run during the execution of a schedule (see schedule.js).
 *
 *   convergence        replicas that have integrated the same records (equal
 *                      state vectors, equal integrated record sets, nothing
 *                      pending) display the same value; after the final sync
 *                      all replicas display the same value.
 *   raLinearizability  after every step at replica R, R's view is the view of
 *                      the specification's fold over some linear extension of
 *                      the causal order on the records R has integrated.
 *   localMeaning       after every edit at R, R's displayed value is the
 *                      specification's `localEdit` of R's displayed value
 *                      before it. Needs `localEdit` on the specification or
 *                      the adapter; skipped (and counted) otherwise.
 *   determinism        before every edit at R, R is forked twice under one
 *                      fresh replica id (1000 + R): one fork created fresh and
 *                      synced, one opened by loading R's state. Both issue the
 *                      request; their displayed values afterwards must agree.
 *                      Needs `adapter.loadInto`; skipped (and counted)
 *                      otherwise.
 *   conservation       after the final sync, every replica presents exactly
 *                      the inserted elements minus the deleted ones, nothing
 *                      is pending, and every record is integrated. Needs the
 *                      adapter's element accounting; skipped (and counted)
 *                      otherwise.
 *
 * Every failure records the replica, step index, expected and actual values,
 * the integrated record keys, and a signature (check name and the kinds of
 * the records involved, cleanup records excluded) used to group failures.
 */
import { findWitness, allFinalViews, MAX_EVENTS } from './witness.js';

export const CHECKS = ['convergence', 'raLinearizability', 'localMeaning', 'determinism', 'conservation'];

const MAX_FAILURES_KEPT = 25;
export const FORK_ID_BASE = 1000;

/** Distinct kinds of the records with specification operations among the keys, sorted and joined. */
export function kindsOf(ex, keys) {
  const kinds = [...keys].map((k) => ex.byKey.get(k)).filter((o) => o.specOps.length > 0).map((o) => o.kind);
  return [...new Set(kinds)].sort().join('+') || 'none';
}

function skip(cs, name) {
  cs.stats.skipped ??= {};
  cs.stats.skipped[name] = (cs.stats.skipped[name] ?? 0) + 1;
}

/** Per-execution check bookkeeping. */
export function newCheckState(names, { witnessBound }) {
  const enabled = new Set(names);
  const per = {};
  for (const n of CHECKS) per[n] = { runs: 0, failures: [], failureCount: 0 };
  return {
    enabled,
    witnessBound,
    per,
    memo: new Map(),
    stats: { versionsChecked: 0, witnessSkips: 0, witnessSkipsPartial: 0, causalGaps: 0, localMeaningByKind: {}, localMeaningFailuresByKind: {} },
    fail(name, f) {
      per[name].failureCount++;
      if (per[name].failures.length < MAX_FAILURES_KEPT) per[name].failures.push({ check: name, ...f });
    },
    results() {
      return Object.fromEntries(
        CHECKS.filter((n) => enabled.has(n)).map((n) => [
          n,
          { name: n, pass: per[n].failureCount === 0, details: { runs: per[n].runs, failureCount: per[n].failureCount, failures: per[n].failures } },
        ]),
      );
    },
  };
}

/**
 * Witness-search events from the records integrated at replica r. A
 * dependency on a record not integrated there is dropped and counted as a
 * causal gap.
 */
export function eventsAt(ex, r) {
  const keys = ex.integrated[r];
  let gaps = 0;
  const events = ex.ops
    .filter((o) => keys.has(o.key))
    .map((o) => {
      const deps = o.deps.filter((d) => keys.has(d));
      gaps += o.deps.length - deps.length;
      return { key: o.key, deps, specOps: o.specOps };
    });
  return { events, gaps };
}

const sameJson = (a, b) => JSON.stringify(a) === JSON.stringify(b);

/** Convergence after a step: every pair with identical integrated state displays identically. */
export function convergenceStep(ex, index) {
  const { spec, adapter } = ex;
  const cs = ex.checkState;
  const rs = Object.keys(ex.replicas).map(Number);
  for (let i = 0; i < rs.length; i++)
    for (let j = i + 1; j < rs.length; j++) {
      const a = rs[i];
      const b = rs[j];
      const A = ex.replicas[a];
      const B = ex.replicas[b];
      if (adapter.hasPending(A) || adapter.hasPending(B)) continue;
      if (!sameJson(adapter.stateVector(A), adapter.stateVector(B))) continue;
      const ia = [...ex.integrated[a]].sort().join(',');
      if (ia !== [...ex.integrated[b]].sort().join(',')) continue;
      cs.per.convergence.runs++;
      const va = adapter.displayed(A);
      const vb = adapter.displayed(B);
      if (spec.viewKey(va) !== spec.viewKey(vb) || (adapter.fingerprint && adapter.fingerprint(A) !== adapter.fingerprint(B)))
        cs.fail('convergence', {
          replica: [a, b],
          step: index,
          expected: spec.normalise(va),
          actual: spec.normalise(vb),
          opKeys: [...ex.integrated[a]].sort(),
          signature: 'convergence:' + kindsOf(ex, ex.integrated[a]),
        });
    }
}

/** RA-linearizability at replica r after a step. */
export function raLinearizabilityStep(ex, r, index) {
  const cs = ex.checkState;
  const keys = ex.integrated[r];
  if (ex.partial[r].length) {
    cs.stats.witnessSkipsPartial++;
    return;
  }
  const edits = [...keys].filter((k) => ex.byKey.get(k).specOps.length > 0).length;
  if (edits > cs.witnessBound || keys.size > MAX_EVENTS) {
    cs.stats.witnessSkips++;
    return;
  }
  const target = ex.adapter.view(ex.replicas[r]);
  const opKeys = [...keys].sort();
  const memoKey = opKeys.join(',') + '|' + JSON.stringify(target);
  cs.per.raLinearizability.runs++;
  cs.stats.versionsChecked++;
  let res = cs.memo.get(memoKey);
  const { events, gaps } = eventsAt(ex, r);
  cs.stats.causalGaps += gaps;
  if (!res) {
    res = findWitness(ex.spec, events, target);
    cs.memo.set(memoKey, res);
  }
  if (!res.found)
    cs.fail('raLinearizability', {
      replica: r,
      step: index,
      expected: { admittedViews: allFinalViews(ex.spec, events, { target }) },
      actual: target,
      opKeys,
      causalGaps: gaps,
      signature: 'raLinearizability:' + kindsOf(ex, keys),
    });
}

/** The local-edit function of an execution, or null. */
const localEditOf = (ex) => ex.spec.localEdit ?? ex.adapter.localEdit ?? null;

/** Local meaning at the acting replica after an edit. */
export function localMeaningStep(ex, ctx) {
  const cs = ex.checkState;
  const localEdit = localEditOf(ex);
  if (!localEdit) return skip(cs, 'localMeaning');
  const { spec } = ex;
  const r = ctx.actor;
  const kind = ctx.request.kind;
  cs.per.localMeaning.runs++;
  cs.stats.localMeaningByKind[kind] = (cs.stats.localMeaningByKind[kind] ?? 0) + 1;
  const expected = spec.normalise(localEdit(spec.normalise(ctx.before), ctx.request));
  const actual = spec.normalise(ex.adapter.displayed(ex.replicas[r]));
  if (spec.viewKey(expected) !== spec.viewKey(actual)) {
    cs.stats.localMeaningFailuresByKind[kind] = (cs.stats.localMeaningFailuresByKind[kind] ?? 0) + 1;
    cs.fail('localMeaning', {
      replica: r,
      step: ctx.index,
      request: ctx.request,
      before: spec.normalise(ctx.before),
      expected,
      actual,
      opKeys: [...ex.integrated[r]].sort(),
      signature: `localMeaning:${kind}:` + kindsOf(ex, ex.integrated[r]),
    });
  }
}

/** Issues a request on a fork; returns its displayed value or the error message. */
function issueOnFork(ex, rep, request) {
  try {
    ex.adapter.issue(rep, request);
    return { visible: ex.spec.normalise(ex.adapter.displayed(rep)) };
  } catch (e) {
    return { error: e.message };
  }
}

/** Fork outcomes of an edit about to be issued at the acting replica. */
function determinismForks(ex, ctx) {
  const { adapter } = ex;
  const src = ex.replicas[ctx.actor];
  const id = FORK_ID_BASE + ctx.actor;
  const created = adapter.createReplica(id, { opened: false });
  adapter.sync(created, src);
  const opened = adapter.createReplica(id, { opened: true });
  adapter.loadInto(opened, src);
  return { created: issueOnFork(ex, created, ctx.request), opened: issueOnFork(ex, opened, ctx.request), actorOpened: ex.opened.has(ctx.actor) };
}

const outcomeKey = (spec, o) => (o.error !== undefined ? 'error:' + o.error : spec.viewKey(o.visible));

/** Checks run before an edit is issued. */
export function runPreEditChecks(ex, ctx) {
  const cs = ex.checkState;
  if (!cs.enabled.has('determinism')) return;
  if (!ex.adapter.supportsOpen) return skip(cs, 'determinism');
  cs.forks = determinismForks(ex, ctx);
}

function determinismStep(ex, ctx) {
  const cs = ex.checkState;
  const f = cs.forks;
  cs.forks = null;
  if (!f) return;
  cs.per.determinism.runs++;
  if (outcomeKey(ex.spec, f.created) !== outcomeKey(ex.spec, f.opened))
    cs.fail('determinism', {
      replica: ctx.actor,
      step: ctx.index,
      request: ctx.request,
      before: ex.spec.normalise(ctx.before),
      expected: f.created,
      actual: f.opened,
      actorOpened: f.actorOpened,
      actorOutcome: ex.spec.normalise(ex.adapter.displayed(ex.replicas[ctx.actor])),
      opKeys: [...ex.integrated[ctx.actor]].sort(),
      signature: `determinism:${ctx.request.kind}:` + kindsOf(ex, ex.integrated[ctx.actor]),
    });
}

/** Checks run after every step. */
export function runStepChecks(ex, ctx) {
  const on = ex.checkState.enabled;
  if (on.has('determinism') && ctx.step.type === 'edit') determinismStep(ex, ctx);
  if (on.has('localMeaning') && ctx.step.type === 'edit') localMeaningStep(ex, ctx);
  if (on.has('raLinearizability')) raLinearizabilityStep(ex, ctx.actor, ctx.index);
  if (on.has('convergence')) convergenceStep(ex, ctx.index);
}

/** Expected labels after the final sync: inserted elements whose keys were never deleted, sorted. */
export function expectedElements(ex) {
  const inserted = new Map();
  const deleted = new Set();
  for (const o of ex.ops) {
    for (const [k, label] of ex.adapter.inserted(o)) inserted.set(k, label);
    for (const k of ex.adapter.deleted(o)) deleted.add(k);
  }
  return [...inserted.entries()].filter(([k]) => !deleted.has(k)).map(([, label]) => label).sort();
}

/** Checks run once after the final sync. */
export function runFinalChecks(ex) {
  const { spec, adapter } = ex;
  const cs = ex.checkState;
  const on = cs.enabled;
  const rs = Object.keys(ex.replicas).map(Number);
  const index = ex.steps.length - 1;
  const all = ex.ops.map((o) => o.key).sort();
  if (on.has('convergence')) {
    cs.per.convergence.runs++;
    const R0 = ex.replicas[rs[0]];
    const v0 = adapter.displayed(R0);
    const f0 = adapter.fingerprint ? adapter.fingerprint(R0) : null;
    for (const r of rs.slice(1)) {
      const v = adapter.displayed(ex.replicas[r]);
      if (spec.viewKey(v0) !== spec.viewKey(v) || (adapter.fingerprint && adapter.fingerprint(ex.replicas[r]) !== f0))
        cs.fail('convergence', {
          replica: [rs[0], r],
          step: index,
          final: true,
          expected: spec.normalise(v0),
          actual: spec.normalise(v),
          opKeys: all,
          signature: 'convergence:final:' + kindsOf(ex, all),
        });
    }
  }
  if (on.has('conservation')) {
    if (!adapter.supportsConservation) return skip(cs, 'conservation');
    const expected = expectedElements(ex);
    for (const r of rs) {
      cs.per.conservation.runs++;
      const rep = ex.replicas[r];
      const actual = [...adapter.present(rep)].sort();
      const pending = adapter.hasPending(rep);
      const notIntegrated = all.filter((k) => !ex.integrated[r].has(k));
      if (pending || !sameJson(actual, expected) || notIntegrated.length)
        cs.fail('conservation', {
          replica: r,
          step: index,
          expected,
          actual,
          pending,
          notIntegrated,
          opKeys: [...ex.integrated[r]].sort(),
          signature: 'conservation:' + kindsOf(ex, all),
        });
    }
  }
}
