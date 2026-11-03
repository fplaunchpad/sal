/**
 * Shared parts of the production block-layer runs: schedule notation,
 * execution with classification, class-preserving shrinking, and compact
 * renderings.
 */
import { execute, generate, shrink, failuresOf, trialSeed, CHECKS, Execution, eventsAt, allFinalViews, findWitness } from '../../ra-pbt/src/index.js';
import { productionBlocksInstance, renderBlocks, renderStep, textsOf, blocksOf, adapterStats } from '../../ra-pbt/instances/notion-production-blocks/index.js';
import { classifyFailure, observeSchedule } from '../../ra-pbt/instances/notion-production-blocks/classify.js';

export { renderBlocks, renderStep, textsOf, blocksOf, adapterStats, CHECKS };

// ------------------------------------------------------------ notation
const e = (replica, kind, x) => ({ type: 'edit', replica, kind, ...x });
export const split = (r, block, index) => e(r, 'split', { block, index });
export const merge = (r, block) => e(r, 'merge', { block });
export const insert = (r, block, index, text) => e(r, 'insert', { block, index, text });
export const bold = (r, block, start, end) => e(r, 'bold', { block, start, end });
export const create = (r, after) => e(r, 'create', { after });
export const send = (from, to, op) => ({ type: 'send', from, to, op });
export const deliver = (from, to) => ({ type: 'deliver', from, to });

/** A view literal from block strings; `[c]` marks a bold character. */
export const V = (...blocks) =>
  blocks.map((s) => {
    const out = [];
    for (let i = 0; i < s.length; i++) {
      if (s[i] === '[') {
        out.push({ text: s[i + 1], bold: true });
        i += 2;
      } else out.push({ text: s[i], bold: false });
    }
    return out;
  });

/** Executes with every check and classifies every failure; returns { trace, failing, classes, observed }. */
export function runClassified(lib, options, schedule, { finalSync = true, witnessBound = 12 } = {}) {
  const inst = productionBlocksInstance(lib, options);
  const trace = execute(inst, schedule, { finalSync, witnessBound });
  const failing = CHECKS.filter((c) => !trace.checks[c].pass);
  let observed = null;
  const classes = {};
  for (const f of failuresOf(trace)) {
    observed ??= observeSchedule(lib, options, schedule, { finalSync });
    const c = classifyFailure(lib, options, schedule, f, observed).class;
    (classes[f.check] ??= new Set()).add(c);
  }
  for (const k of Object.keys(classes)) classes[k] = [...classes[k]].sort();
  return { trace, failing, classes, observed };
}

/** The displayed blocks at replica r after the first `steps` steps (no final sync). */
export function shownAfter(lib, options, schedule, steps, r) {
  const inst = productionBlocksInstance(lib, options);
  const ex = new Execution(inst, schedule.replicas, { checks: [] });
  for (const s of schedule.steps.slice(0, steps)) ex.apply(s);
  return blocksOf(ex.adapter.displayed(ex.replica(r)));
}

/** Admitted views and witness at replica r after the whole schedule (no final sync). */
export function admittedAt(lib, options, schedule, r) {
  const inst = productionBlocksInstance(lib, options);
  const ex = new Execution(inst, schedule.replicas, { checks: [] });
  for (const s of schedule.steps) ex.apply(s);
  const { events } = eventsAt(ex, r);
  return { admitted: allFinalViews(inst.spec, events), witness: findWitness(inst.spec, events, ex.adapter.view(ex.replica(r))).found, shown: blocksOf(ex.adapter.displayed(ex.replica(r))) };
}

/** Shrinks `schedule` under "some failure of `check` still has class `cls`". */
export function shrinkClass(lib, options, schedule, check, cls, { witnessBound = 12 } = {}) {
  const inst = productionBlocksInstance(lib, options);
  const fails = (s) => {
    const trace = execute(inst, s, { witnessBound });
    const fs = failuresOf(trace).filter((f) => f.check === check);
    if (!fs.length) return false;
    const obs = observeSchedule(lib, options, s);
    return fs.some((f) => classifyFailure(lib, options, s, f, obs).class === cls);
  };
  return shrink(inst, schedule, fails);
}

/** A compact rendering of a failure. */
export function renderFailure(f) {
  const out = { check: f.check, replica: f.replica, step: f.step };
  if (f.request) out.request = renderStep({ type: 'edit', replica: f.replica, ...f.request });
  if (f.before) out.before = renderBlocks(f.before);
  if (f.check === 'raLinearizability') {
    out.actual = renderBlocks(f.actual);
    out.admitted = f.expected.admittedViews.map(renderBlocks);
  } else if (f.check === 'conservation') {
    out.expected = f.expected.length;
    out.actual = f.actual.length;
    out.pending = f.pending;
    out.notIntegrated = f.notIntegrated;
  } else {
    out.expected = Array.isArray(f.expected) ? renderBlocks(f.expected) : f.expected;
    out.actual = Array.isArray(f.actual) ? renderBlocks(f.actual) : f.actual;
  }
  return out;
}

/** Generates and executes trials of one configuration; returns per-check and per-class counts and first schedules per class. */
export function searchConfiguration(lib, cfg, seeds) {
  const options = { texts: cfg.texts, profile: cfg.profile, ...(cfg.reading ?? {}) };
  const inst = productionBlocksInstance(lib, options);
  const gen = { steps: cfg.steps, partialDelivery: !!cfg.partial, openedReplicas: !!cfg.opened, ...(cfg.replicas ? { replicas: cfg.replicas } : {}) };
  const totals = { trials: 0, edits: 0, deliveries: 0, sends: 0, opens: 0, versionsChecked: 0, witnessSkips: 0, witnessSkipsPartial: 0, failingTrials: 0, rejectedApplies: 0, trialsWithRejection: 0 };
  const failuresByCheck = Object.fromEntries(CHECKS.map((c) => [c, 0]));
  const trialsByCheck = Object.fromEntries(CHECKS.map((c) => [c, 0]));
  const trialsByClass = {};
  const runsByCheck = Object.fromEntries(CHECKS.map((c) => [c, 0]));
  const first = {};
  const rejectedBefore = adapterStats.rejected;
  for (const seed of seeds)
    for (let t = 0; t < cfg.trials; t++) {
      const ts = trialSeed(seed, t);
      const schedule = generate(inst, ts, gen);
      const trace = execute(inst, schedule, { witnessBound: cfg.bound ?? 12 });
      totals.trials++;
      for (const k of ['edits', 'deliveries', 'sends', 'opens', 'versionsChecked', 'witnessSkips', 'witnessSkipsPartial']) totals[k] += trace.stats[k] ?? 0;
      for (const c of CHECKS) {
        runsByCheck[c] += trace.checks[c].details.runs;
        failuresByCheck[c] += trace.checks[c].details.failureCount;
        if (!trace.checks[c].pass) trialsByCheck[c]++;
      }
      const fs = failuresOf(trace);
      const obs = observeSchedule(lib, options, schedule);
      const rejected = obs.events.filter((x) => x.phase === 'apply' && !x.ok).length;
      totals.rejectedApplies += rejected;
      if (rejected) totals.trialsWithRejection++;
      if (!fs.length) continue;
      totals.failingTrials++;
      const seen = new Set();
      for (const f of fs) {
        const cls = classifyFailure(lib, options, schedule, f, obs).class;
        const key = `${f.check}:${cls}`;
        if (seen.has(key)) continue;
        seen.add(key);
        trialsByClass[key] = (trialsByClass[key] ?? 0) + 1;
        first[key] ??= { campaignSeed: seed, trial: t, seed: ts, schedule };
      }
    }
  return { config: cfg, options, generation: gen, totals, runsByCheck, failuresByCheck, trialsByCheck, trialsByClass, first, rejectedRequests: adapterStats.rejected - rejectedBefore };
}
