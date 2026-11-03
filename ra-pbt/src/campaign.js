/**
 * Search campaigns: generated schedules executed under every check.
 *
 * For each seed and trial t the schedule is generated from the trial seed
 * (seed * 1000003 + t) mod 2^32 and executed with the final sync. The
 * summary totals the execution statistics and the failures per check; every
 * failing trial is kept with its schedule, check results, anomalies and
 * records; and for each failure signature the first trial showing it is
 * shrunk under the predicate "the schedule still fails with this signature".
 */
import { mkdirSync, writeFileSync } from 'node:fs';
import { dirname } from 'node:path';
import { execute, prepareInstance } from './schedule.js';
import { CHECKS } from './checks.js';
import { generate } from './generate.js';
import { shrink } from './shrink.js';

/** Every failure record of a trace, in check order. */
export function failuresOf(trace) {
  return CHECKS.flatMap((c) => trace.checks[c]?.details.failures ?? []);
}

/** The seed of trial t under a campaign seed. */
export const trialSeed = (seed, t) => (seed * 1000003 + t) >>> 0;

const STAT_KEYS = ['edits', 'deliveries', 'sends', 'pendingSends', 'opens', 'cleanups', 'versionsChecked', 'witnessSkips', 'witnessSkipsPartial', 'causalGaps'];

function addCounts(into, from) {
  for (const [k, v] of Object.entries(from ?? {})) into[k] = (into[k] ?? 0) + v;
}

/**
 * runCampaign(instance, { seed = 1 | seeds: [seed], trials = 20, bound = 12,
 *             options = {}, shrink = true, renderStep?, renderFailure? })
 * returns { summary, failing, shrunk }. With several seeds every failing
 * trial and shrunk representative also records its campaign seed.
 */
export function runCampaign(instance, { seed = 1, seeds, trials = 20, bound = 12, options = {}, shrink: doShrink = true, renderStep, renderFailure } = {}) {
  const inst = prepareInstance(instance);
  const seedList = seeds ?? [seed];
  const summary = {
    ...(seeds ? { seeds } : { seed }),
    trials,
    options,
    witnessBound: bound,
    ...Object.fromEntries(STAT_KEYS.map((k) => [k, 0])),
    anomalies: 0,
    failingTrials: 0,
  };
  summary.failuresByCheck = Object.fromEntries(CHECKS.map((c) => [c, 0]));
  summary.trialsFailingByCheck = Object.fromEntries(CHECKS.map((c) => [c, 0]));
  summary.localMeaningByKind = {};
  summary.localMeaningFailuresByKind = {};
  const failing = [];
  const firstBySignature = new Map();
  for (const s of seedList)
    for (let t = 0; t < trials; t++) {
      const ts = trialSeed(s, t);
      const schedule = generate(inst, ts, options);
      const trace = execute(inst, schedule, { witnessBound: bound });
      const st = trace.stats;
      for (const k of STAT_KEYS) summary[k] += st[k];
      summary.anomalies += trace.anomalies.length;
      addCounts(summary.localMeaningByKind, st.localMeaningByKind);
      addCounts(summary.localMeaningFailuresByKind, st.localMeaningFailuresByKind);
      if (st.skipped) addCounts((summary.skipped ??= {}), st.skipped);
      const fs = failuresOf(trace);
      for (const c of CHECKS) {
        if (!trace.checks[c]) continue;
        summary.failuresByCheck[c] += trace.checks[c].details.failureCount;
        if (!trace.checks[c].pass) summary.trialsFailingByCheck[c]++;
      }
      if (fs.length) {
        summary.failingTrials++;
        const where = seeds ? { campaignSeed: s } : {};
        failing.push({ ...where, trial: t, seed: ts, schedule, checks: trace.checks, anomalies: trace.anomalies, ops: trace.ops });
        for (const f of fs) if (!firstBySignature.has(f.signature)) firstBySignature.set(f.signature, { ...where, trial: t, seed: ts, schedule, failure: f });
      }
    }
  const shrunk = [];
  if (doShrink)
    for (const [signature, first] of firstBySignature) {
      const fails = (s) => failuresOf(execute(inst, s, { witnessBound: bound })).some((f) => f.signature === signature);
      const res = shrink(inst, first.schedule, fails);
      const trace = execute(inst, res.schedule, { witnessBound: bound });
      const f = failuresOf(trace).find((x) => x.signature === signature);
      const entry = {
        signature,
        ...(seeds ? { campaignSeed: first.campaignSeed } : {}),
        trial: first.trial,
        seed: first.seed,
        originalSteps: first.schedule.steps.length,
        schedule: res.schedule,
      };
      if (renderStep) entry.rendered = res.schedule.steps.map(renderStep);
      Object.assign(entry, { reductions: res.reductions, shrinkExecutions: res.executions, failure: f });
      if (renderFailure) entry.renderedFailure = f && renderFailure(f);
      shrunk.push(entry);
    }
  return { summary, failing, shrunk };
}

/** Writes JSON with one-space indentation, creating the directory. */
export function writeJson(path, data) {
  mkdirSync(dirname(path), { recursive: true });
  writeFileSync(path, JSON.stringify(data, null, 1) + '\n');
}
