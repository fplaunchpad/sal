/**
 * Seeded search over generated schedules: the campaign of
 * ra-pbt/src/campaign.js (same trial seeds, statistics, failure records and
 * shrinking per failure signature), with one difference required by the
 * library: control returns to the event loop after every trial. The shipped
 * code arms short timers (cache expiry in its grapheme segmentation) that
 * keep each client's module context alive until they fire, so a campaign
 * that never yields holds every client it ever created.
 */
import { generate, execute, shrink, failuresOf, trialSeed, CHECKS, prepareInstance } from '../../ra-pbt/src/index.js';

const STAT_KEYS = ['edits', 'deliveries', 'sends', 'pendingSends', 'opens', 'cleanups', 'versionsChecked', 'witnessSkips', 'witnessSkipsPartial', 'causalGaps'];
export const yieldToTimers = () => new Promise((resolve) => setTimeout(resolve, 2));

const add = (into, from) => {
  for (const [k, v] of Object.entries(from ?? {})) into[k] = (into[k] ?? 0) + v;
};

/**
 * runSearch(instance, { seed, trials, bound, options, shrink, keepFailing, classify, checks, renderStep, renderFailure })
 * returns { summary, failing, shrunk }. `keepFailing` bounds the number of
 * failing trials stored in full (all are counted). `classify(schedule,
 * trace)`, when given, returns [{ class }] for the failures of a trace;
 * the summary then counts failure records and trials per class, and the
 * class of each trial's earliest failure (its onset). `checks` names the
 * checks run (default all).
 */
export async function runSearch(instance, { seed = 1, trials = 20, bound = 12, options = {}, shrink: doShrink = true, keepFailing = 40, classify, checks = CHECKS, renderStep, renderFailure } = {}) {
  const inst = prepareInstance(instance);
  const summary = { seed, trials, options, witnessBound: bound, ...Object.fromEntries(STAT_KEYS.map((k) => [k, 0])), anomalies: 0, failingTrials: 0 };
  summary.failuresByCheck = Object.fromEntries(CHECKS.map((c) => [c, 0]));
  summary.trialsFailingByCheck = Object.fromEntries(CHECKS.map((c) => [c, 0]));
  summary.localMeaningByKind = {};
  summary.localMeaningFailuresByKind = {};
  const failing = [];
  const first = new Map();
  for (let t = 0; t < trials; t++) {
    const ts = trialSeed(seed, t);
    const schedule = generate(inst, ts, options);
    const trace = execute(inst, schedule, { witnessBound: bound, checks });
    for (const k of STAT_KEYS) summary[k] += trace.stats[k];
    summary.anomalies += trace.anomalies.length;
    add(summary.localMeaningByKind, trace.stats.localMeaningByKind);
    add(summary.localMeaningFailuresByKind, trace.stats.localMeaningFailuresByKind);
    if (trace.stats.skipped) add((summary.skipped ??= {}), trace.stats.skipped);
    for (const c of CHECKS) {
      if (!trace.checks[c]) continue;
      summary.failuresByCheck[c] += trace.checks[c].details.failureCount;
      if (!trace.checks[c].pass) summary.trialsFailingByCheck[c]++;
    }
    const fs = failuresOf(trace);
    if (classify && fs.length) {
      const classes = classify(schedule, trace);
      const c = (summary.classes ??= { records: {}, trials: {}, onset: {} });
      for (const x of classes) c.records[x.class] = (c.records[x.class] ?? 0) + 1;
      for (const k of new Set(classes.map((x) => x.class))) c.trials[k] = (c.trials[k] ?? 0) + 1;
      const earliest = classes.reduce((m, x) => (m === null || x.step < m.step ? x : m), null);
      c.onset[earliest.class] = (c.onset[earliest.class] ?? 0) + 1;
    }
    if (fs.length) {
      summary.failingTrials++;
      if (failing.length < keepFailing) failing.push({ trial: t, seed: ts, schedule, checks: trace.checks, anomalies: trace.anomalies, ops: trace.ops });
      for (const f of fs) if (!first.has(f.signature)) first.set(f.signature, { trial: t, seed: ts, schedule });
    }
    if (trace.anomalies.length && failing.at(-1)?.trial !== t && failing.length < keepFailing) failing.push({ trial: t, seed: ts, schedule, checks: trace.checks, anomalies: trace.anomalies, ops: trace.ops });
    await yieldToTimers();
  }
  const shrunk = [];
  if (doShrink)
    for (const [signature, f] of first) {
      const fails = (s) => failuresOf(execute(inst, s, { witnessBound: bound, checks })).some((x) => x.signature === signature);
      const res = shrink(inst, f.schedule, fails);
      const trace = execute(inst, res.schedule, { witnessBound: bound, checks });
      const failure = failuresOf(trace).find((x) => x.signature === signature);
      const entry = { signature, trial: f.trial, seed: f.seed, originalSteps: f.schedule.steps.length, schedule: res.schedule };
      if (renderStep) entry.rendered = res.schedule.steps.map(renderStep);
      Object.assign(entry, { reductions: res.reductions, shrinkExecutions: res.executions, failure });
      if (renderFailure) entry.renderedFailure = failure && renderFailure(failure);
      shrunk.push(entry);
      await yieldToTimers();
    }
  return { summary, failing, shrunk };
}
