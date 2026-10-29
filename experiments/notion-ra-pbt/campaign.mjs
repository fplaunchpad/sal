/**
 * The campaign: end-to-end searches and law-layer runs over both models,
 * written to results/.
 *
 *   node campaign.mjs [--quick]
 *
 * End to end. For every configuration (model, seed document, request
 * profile, delivery) trials are generated and executed under every check
 * with the final sync. A configuration with `probe` also checks, at the end
 * of every generated schedule (before the final sync), every valid request
 * of its profile at every replica: the probe is the schedule extended by
 * that one edit, executed under the local-meaning and RA-linearizability
 * checks. Every failing check of a trial is classified
 * (classify.js) and the first trial of each (check, class) group is shrunk
 * with ra-pbt's shrinker under the predicate "some failure of this check
 * still has this class". ra-pbt's own campaign keys representatives by
 * check and record kinds, which merges different mechanisms.
 *
 * Systematic. For a seed document and a block of it, every pair of split
 * positions (i at replica 1, j at replica 2), replica 1 receiving replica
 * 2's split, then either nothing or each valid merge at replica 1, and
 * finally every valid request of the profile at replica 1 as a probe: the
 * directed suite of experiments/notion-correctness, as ra-pbt schedules.
 *
 * Laws. Every property on the transaction-archive datatype, with the
 * display observation and with the visible-character bag observation, over
 * several seeds; the first failure of a property is shrunk by the law layer.
 *
 * Writes results/endtoend-<model>.json, results/laws-<model>.json and
 * results/summary.json (per catalogue class: the detecting properties and
 * the smallest shrunk counterexample).
 */
import { execute, generate, shrink, failuresOf, trialSeed, writeJson, CHECKS, Execution } from '../../ra-pbt/src/index.js';
import { loadModel, notionInstance, classifyFailure, renderStep, adapterStats, allRequests } from '../../ra-pbt/instances/notion/index.js';
import { runLaws } from './lib.mjs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const here = dirname(fileURLToPath(import.meta.url));
const quick = process.argv.includes('--quick');
const T = (n) => (quick ? Math.max(4, Math.round(n / 10)) : n);

const E2E = [
  { texts: ['x'], profile: 'structure', partial: true, replicas: 2, steps: 12, trials: 300 },
  { texts: ['a', 'b', 'c'], profile: 'structure', partial: true, replicas: 2, steps: 14, trials: 300 },
  { texts: ['a', 'b', 'c'], profile: 'structure', partial: true, replicas: 3, steps: 16, trials: 200 },
  { texts: ['ab', 'cd'], profile: 'structure', partial: true, steps: 14, trials: 200 },
  { texts: ['a'], profile: 'text', partial: false, steps: 14, trials: 200 },
  { texts: ['abc'], profile: 'text', partial: true, steps: 14, trials: 200 },
  { texts: ['ab'], profile: 'format', partial: false, steps: 10, trials: 200 },
  { texts: ['abc'], profile: 'format', partial: true, steps: 12, trials: 200 },
  { texts: ['ab', 'cd'], profile: 'format', partial: false, steps: 12, trials: 200 },
  { texts: ['ab'], profile: 'format', partial: true, replicas: 2, steps: 6, trials: 150, probe: true },
  { texts: ['abc'], profile: 'format', partial: true, replicas: 2, steps: 6, trials: 150, probe: true },
  { texts: ['a', 'b', 'c'], profile: 'structure', partial: true, replicas: 2, steps: 10, trials: 150, probe: true },
  { texts: ['a', 'b', 'c'], profile: 'structure', partial: true, replicas: 2, steps: 40, trials: 300 },
  { texts: ['a', 'b', 'c'], profile: 'structure', partial: true, replicas: 3, steps: 40, trials: 300 },
];
const SYSTEMATIC = [
  { texts: ['ab'], profile: 'format' },
  { texts: ['abc'], profile: 'format' },
  { texts: ['abcd'], profile: 'format' },
  { texts: ['ab', 'cd'], profile: 'format' },
  { texts: ['abc'], profile: 'text' },
  { texts: ['ab', 'cd'], profile: 'text' },
];
const LAWS = [
  { texts: ['x'], profile: 'structure', observation: 'bag', replicas: 3, syncProbability: 0.4, size: 8, trials: 2000, seeds: [1, 2, 3] },
  { texts: ['a', 'b', 'c'], profile: 'structure', observation: 'bag', replicas: 3, syncProbability: 0.4, size: 10, trials: 2000, seeds: [1, 2, 3] },
  { texts: ['a', 'b', 'c'], profile: 'structure', observation: 'view', replicas: 3, syncProbability: 0.3, size: 12, trials: 300, seeds: [1, 2] },
  { texts: ['ab', 'cd'], profile: 'structure', observation: 'view', replicas: 3, syncProbability: 0.3, size: 12, trials: 300, seeds: [1, 2] },
  { texts: ['a'], profile: 'text', observation: 'view', replicas: 3, syncProbability: 0.3, size: 12, trials: 300, seeds: [1, 2] },
  { texts: ['ab'], profile: 'format', observation: 'view', replicas: 2, syncProbability: 0.3, size: 8, trials: 300, seeds: [1, 2] },
  { texts: ['abc'], profile: 'format', observation: 'view', replicas: 2, syncProbability: 0.3, size: 8, trials: 300, seeds: [1, 2] },
];

const classKey = (c) => c.catalogue.join('+');

function e2eConfig(model, cfg, seed = 1) {
  const inst = notionInstance(model, { texts: cfg.texts, profile: cfg.profile, format: cfg.profile === 'format' });
  const options = { steps: cfg.steps, partialDelivery: cfg.partial, ...(cfg.replicas ? { replicas: cfg.replicas } : {}) };
  const trials = T(cfg.trials);
  const totals = { trials, edits: 0, versionsChecked: 0, witnessSkips: 0, failingTrials: 0, skipped: {} };
  const runs = Object.fromEntries(CHECKS.map((c) => [c, 0]));
  const groups = new Map();
  const rejected0 = adapterStats.rejected;
  for (let t = 0; t < trials; t++) {
    const schedule = generate(inst, trialSeed(seed, t), options);
    const trace = execute(inst, schedule);
    totals.edits += trace.stats.edits;
    totals.versionsChecked += trace.stats.versionsChecked;
    totals.witnessSkips += trace.stats.witnessSkips;
    for (const [k, v] of Object.entries(trace.stats.skipped ?? {})) totals.skipped[k] = (totals.skipped[k] ?? 0) + v;
    for (const c of CHECKS) runs[c] += trace.checks[c].details.runs;
    const fs = CHECKS.filter((c) => !trace.checks[c].pass).map((c) => trace.checks[c].details.failures[0]);
    if (fs.length) totals.failingTrials++;
    for (const f of fs) {
      const cls = classKey(classifyFailure(inst, schedule, f));
      const k = `${f.check}:${cls}`;
      const g = groups.get(k) ?? { check: f.check, class: cls, trials: 0, first: { trial: t, schedule } };
      g.trials++;
      groups.set(k, g);
    }
  }
  if (cfg.probe) {
    totals.probes = 0;
    totals.failingProbes = 0;
    for (let t = 0; t < trials; t++) {
      const schedule = generate(inst, trialSeed(seed, t), options);
      const ex = new Execution(inst, schedule.replicas, { checks: [] });
      for (const s of schedule.steps) ex.apply(s);
      for (let r = 1; r <= schedule.replicas; r++)
        for (const q of allRequests(ex.adapter.displayed(ex.replica(r)), cfg.profile)) {
          const probe = { ...schedule, steps: [...schedule.steps, { type: 'edit', replica: r, ...q }] };
          let trace;
          try {
            trace = execute(inst, probe, { checks: ['localMeaning', 'raLinearizability'], finalSync: false });
          } catch (err) {
            if (err instanceof RangeError) continue;
            throw err;
          }
          totals.probes++;
          const last = probe.steps.length - 1;
          const fs = ['localMeaning', 'raLinearizability'].map((c) => trace.checks[c].details.failures.find((f) => f.step === last)).filter(Boolean);
          if (fs.length) totals.failingProbes++;
          for (const f of fs) {
            const cls = classKey(classifyFailure(inst, probe, f));
            const k = `probe:${f.check}:${cls}`;
            const g = groups.get(k) ?? { check: f.check, class: cls, probe: true, trials: 0, first: { trial: t, schedule: probe } };
            g.trials++;
            groups.set(k, g);
          }
        }
    }
  }
  const representatives = shrinkGroups(inst, groups);
  return { ...cfg, trials, seed, totals: { ...totals, rejectedRequests: adapterStats.rejected - rejected0 }, checkRuns: runs, representatives };
}

/** Representatives of failure groups, shrunk under the class-preserving predicate. */
function shrinkGroups(inst, groups) {
  const representatives = [];
  for (const g of groups.values()) {
    const run = (s) => execute(inst, s, g.probe ? { finalSync: false } : {});
    const fails = (s) => failuresOf(run(s)).some((f) => f.check === g.check && classKey(classifyFailure(inst, s, f)) === g.class);
    const res = shrink(inst, g.first.schedule, fails);
    const f = failuresOf(run(res.schedule)).find((x) => x.check === g.check && classKey(classifyFailure(inst, res.schedule, x)) === g.class);
    representatives.push({
      probe: !!g.probe,
      check: g.check,
      class: g.class,
      trials: g.trials,
      originalSteps: g.first.schedule.steps.length,
      steps: res.schedule.steps.length,
      edits: res.schedule.steps.filter((x) => x.type === 'edit').length,
      rendered: res.schedule.steps.map(renderStep),
      schedule: res.schedule,
      failure: f && { check: f.check, replica: f.replica, step: f.step, final: !!f.final, signature: f.signature, request: f.request, expected: f.expected, actual: f.actual },
    });
  }
  return representatives.sort((a, b) => (a.check + a.class < b.check + b.class ? -1 : 1));
}

function systematic(model, cfg) {
  const inst = notionInstance(model, { texts: cfg.texts, profile: cfg.profile, format: cfg.profile === 'format' });
  const groups = new Map();
  const totals = { prefixes: 0, probes: 0, failingProbes: 0, failingPrefixes: 0 };
  const split = (r, block, index) => ({ type: 'edit', replica: r, kind: 'split', block, index });
  const prefixes = [];
  cfg.texts.forEach((t, block) => {
    for (let i = 0; i <= t.length; i++)
      for (let j = 0; j <= t.length; j++) {
        const base = [split(1, block, i), split(2, block, j), { type: 'send', from: 2, to: 1, op: 0 }];
        const ex = new Execution(inst, 2, { checks: [] });
        for (const s of base) ex.apply(s);
        const blocks = ex.adapter.displayed(ex.replica(1)).length;
        prefixes.push(base);
        for (let m = 1; m < blocks; m++) prefixes.push([...base, { type: 'edit', replica: 1, kind: 'merge', block: m }]);
      }
  });
  for (const steps of prefixes) {
    const schedule = { replicas: 2, steps };
    totals.prefixes++;
    const whole = execute(inst, schedule);
    if (failuresOf(whole).length) totals.failingPrefixes++;
    for (const f of CHECKS.filter((c) => !whole.checks[c].pass).map((c) => whole.checks[c].details.failures[0])) {
      const cls = classKey(classifyFailure(inst, schedule, f));
      const k = `${f.check}:${cls}`;
      const g = groups.get(k) ?? { check: f.check, class: cls, trials: 0, first: { schedule } };
      g.trials++;
      groups.set(k, g);
    }
    const ex = new Execution(inst, 2, { checks: [] });
    for (const s of steps) ex.apply(s);
    for (const q of allRequests(ex.adapter.displayed(ex.replica(1)), cfg.profile)) {
      const probe = { replicas: 2, steps: [...steps, { type: 'edit', replica: 1, ...q }] };
      const trace = execute(inst, probe, { checks: ['localMeaning', 'raLinearizability'], finalSync: false });
      totals.probes++;
      const last = probe.steps.length - 1;
      const fs = ['localMeaning', 'raLinearizability'].map((c) => trace.checks[c].details.failures.find((f) => f.step === last)).filter(Boolean);
      if (fs.length) totals.failingProbes++;
      for (const f of fs) {
        const cls = classKey(classifyFailure(inst, probe, f));
        const k = `probe:${f.check}:${cls}`;
        const g = groups.get(k) ?? { check: f.check, class: cls, probe: true, trials: 0, first: { schedule: probe } };
        g.trials++;
        groups.set(k, g);
      }
    }
  }
  return { ...cfg, systematic: true, totals, representatives: shrinkGroups(inst, groups) };
}

const summary = { quick, models: {}, classes: {} };
for (const variant of ['demo', 'anchor-absorb']) {
  const model = await loadModel(variant);
  const e2e = [];
  for (const cfg of E2E) {
    const r = e2eConfig(model, cfg);
    e2e.push(r);
    console.log(variant, JSON.stringify(cfg.texts), cfg.profile, cfg.partial ? 'partial' : 'whole', cfg.probe ? `probes ${r.totals.failingProbes}/${r.totals.probes}` : '', `failing ${r.totals.failingTrials}/${r.trials}`, r.representatives.map((x) => `${x.probe ? 'probe:' : ''}${x.check}:${x.class}(${x.edits})`).join(' '));
  }
  for (const cfg of quick ? SYSTEMATIC.slice(0, 2) : SYSTEMATIC) {
    const r = systematic(model, cfg);
    e2e.push(r);
    console.log(variant, 'systematic', JSON.stringify(cfg.texts), cfg.profile, `prefixes ${r.totals.failingPrefixes}/${r.totals.prefixes}`, `probes ${r.totals.failingProbes}/${r.totals.probes}`, r.representatives.map((x) => `${x.probe ? 'probe:' : ''}${x.check}:${x.class}(${x.edits})`).join(' '));
  }
  writeJson(join(here, 'results', `endtoend-${variant}.json`), { model: variant, hashes: model.hashes, configurations: e2e });
  const laws = [];
  for (const cfg of LAWS)
    for (const seed of cfg.seeds) {
      const r = await runLaws({ model: variant, ...cfg, seed, trials: T(cfg.trials) });
      laws.push(r);
      const fails = r.properties.filter((p) => p.verdict === 'fail');
      console.log(variant, 'laws', JSON.stringify(cfg.texts), cfg.profile, cfg.observation, 'seed', seed, fails.length ? fails.map((p) => `${p.name}:${p.classification.catalogue.join('+')}(${p.counterexample.size})`).join(' ') : 'all pass');
    }
  writeJson(join(here, 'results', `laws-${variant}.json`), { model: variant, hashes: model.hashes, runs: laws });
  const m = (summary.models[variant] = {
    endToEndFailingTrials: e2e.reduce((a, r) => a + (r.totals.failingTrials ?? 0), 0),
    endToEndTrials: e2e.reduce((a, r) => a + (r.trials ?? 0), 0),
    probes: e2e.reduce((a, r) => a + (r.totals.probes ?? 0), 0),
    failingProbes: e2e.reduce((a, r) => a + (r.totals.failingProbes ?? 0), 0),
    systematicPrefixes: e2e.reduce((a, r) => a + (r.totals.prefixes ?? 0), 0),
    failingSystematicPrefixes: e2e.reduce((a, r) => a + (r.totals.failingPrefixes ?? 0), 0),
    lawFailures: [],
  });
  for (const r of e2e)
    for (const x of r.representatives)
      for (const cls of x.class.split('+')) {
        const c = (summary.classes[cls] ??= {});
        const d = (c[variant] ??= { endToEnd: {}, laws: {} });
        const key = (x.probe ? 'probe:' : '') + x.check;
        const prev = d.endToEnd[key];
        if (!prev || x.edits < prev.edits) d.endToEnd[key] = { edits: x.edits, steps: x.steps, texts: r.texts, profile: r.profile, systematic: !!r.systematic, rendered: x.rendered, failure: x.failure };
      }
  for (const r of laws)
    for (const p of r.properties)
      if (p.verdict === 'fail') {
        m.lawFailures.push({ property: p.name, texts: r.texts, profile: r.profile, observation: r.observation, seed: r.seed, class: p.classification.catalogue.join('+'), size: p.counterexample.size });
        for (const cls of p.classification.catalogue) {
          const d = ((summary.classes[cls] ??= {})[variant] ??= { endToEnd: {}, laws: {} });
          const key = `${p.name}/${r.observation}`;
          const prev = d.laws[key];
          if (!prev || p.counterexample.size < prev.size) d.laws[key] = { size: p.counterexample.size, texts: r.texts, events: p.counterexample.events };
        }
      }
}
writeJson(join(here, 'results', 'summary.json'), summary);
console.log(JSON.stringify(Object.fromEntries(Object.entries(summary.classes).map(([k, v]) => [k, Object.fromEntries(Object.entries(v).map(([m, d]) => [m, { e2e: Object.fromEntries(Object.entries(d.endToEnd).map(([c, x]) => [c, x.edits])), laws: Object.fromEntries(Object.entries(d.laws).map(([c, x]) => [c, x.size])) }]))]))));
