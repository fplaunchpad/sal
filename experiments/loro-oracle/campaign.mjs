/**
 * The Loro campaign: seeded searches over several feature mixes, each
 * failing trial classified by the instance's classifier, and for every run
 * and class the first trial showing it shrunk under the predicate "the trial
 * still shows this class".
 *
 *   node campaign.mjs [--trials N] [--only name1,name2] [--shrink false]
 *
 * Writes results/campaign/<run>.json (the search output) and .log (its
 * summary) for every run, and results/campaign.json (summaries, class
 * histograms, representatives). Source verification runs before and after.
 * Runs whose seed matches another run's (`sameSchedulesAs`) execute the same
 * schedules under another attribute reading, since generation does not
 * depend on the specification.
 */
import { mkdirSync, writeFileSync } from 'node:fs';
import { failuresOf, writeJson } from '../../ra-pbt/src/index.js';
import { verifySources, runCampaign, execute, shrink, renderStep, CHECKS } from '../../ra-pbt/instances/loro/index.js';
import { classifyTrial, CLASSES } from '../../ra-pbt/instances/loro/classify.js';
import { renderFailure, renderView } from './render.mjs';

const RUNS = [
  { name: 'plain-gap-21', seed: 21, rule: 'gap', options: {} },
  { name: 'plain-gap-22', seed: 22, rule: 'gap', options: { replicas: 3 } },
  { name: 'plain-left-23', seed: 23, rule: 'left', options: {} },
  { name: 'plain-left-long-24', seed: 24, rule: 'left', bound: 14, options: { steps: 20, replicas: 3 } },
  { name: 'plain-both-25', seed: 25, rule: 'both', options: {} },
  { name: 'plain-gap-long-26', seed: 26, rule: 'gap', options: { steps: 16, replicas: 4 } },
  { name: 'partial-plain-27', seed: 27, rule: 'gap', options: { partialDelivery: true } },
  { name: 'styles-created-31', seed: 31, rule: 'gap', options: { withStyles: true, openedReplicas: false } },
  { name: 'styles-created-32', seed: 32, rule: 'gap', options: { withStyles: true, openedReplicas: false } },
  { name: 'styles-opened-33', seed: 33, rule: 'gap', options: { withStyles: true, openedReplicas: true } },
  { name: 'styles-opened-34', seed: 34, rule: 'gap', options: { withStyles: true, openedReplicas: true } },
  { name: 'partial-styles-35', seed: 35, rule: 'gap', options: { withStyles: true, partialDelivery: true } },
  { name: 'partial-styles-36', seed: 36, rule: 'gap', options: { withStyles: true, partialDelivery: true, openedReplicas: false } },
  { name: 'styles-created-31-inherit', seed: 31, rule: 'gap', attrs: 'inherit', sameSchedulesAs: 'styles-created-31', options: { withStyles: true, openedReplicas: false } },
  { name: 'styles-opened-33-inherit', seed: 33, rule: 'gap', attrs: 'inherit', sameSchedulesAs: 'styles-opened-33', options: { withStyles: true, openedReplicas: true } },
  { name: 'partial-styles-35-inherit', seed: 35, rule: 'gap', attrs: 'inherit', sameSchedulesAs: 'partial-styles-35', options: { withStyles: true, partialDelivery: true } },
  { name: 'styles-created-31-expand', seed: 31, rule: 'gap', attrs: 'expand', sameSchedulesAs: 'styles-created-31', options: { withStyles: true, openedReplicas: false } },
  { name: 'styles-created-32-expand', seed: 32, rule: 'gap', attrs: 'expand', sameSchedulesAs: 'styles-created-32', options: { withStyles: true, openedReplicas: false } },
  { name: 'styles-opened-33-expand', seed: 33, rule: 'gap', attrs: 'expand', sameSchedulesAs: 'styles-opened-33', options: { withStyles: true, openedReplicas: true } },
  { name: 'styles-opened-34-expand', seed: 34, rule: 'gap', attrs: 'expand', sameSchedulesAs: 'styles-opened-34', options: { withStyles: true, openedReplicas: true } },
  { name: 'partial-styles-35-expand', seed: 35, rule: 'gap', attrs: 'expand', sameSchedulesAs: 'partial-styles-35', options: { withStyles: true, partialDelivery: true } },
  { name: 'partial-styles-36-expand', seed: 36, rule: 'gap', attrs: 'expand', sameSchedulesAs: 'partial-styles-36', options: { withStyles: true, partialDelivery: true, openedReplicas: false } },
  { name: 'styles-created-31-anchors', seed: 31, rule: 'gap', attrs: 'anchors', bound: 10, sameSchedulesAs: 'styles-created-31', options: { withStyles: true, openedReplicas: false } },
  { name: 'styles-created-32-anchors', seed: 32, rule: 'gap', attrs: 'anchors', bound: 10, sameSchedulesAs: 'styles-created-32', options: { withStyles: true, openedReplicas: false } },
  { name: 'styles-opened-33-anchors', seed: 33, rule: 'gap', attrs: 'anchors', bound: 10, sameSchedulesAs: 'styles-opened-33', options: { withStyles: true, openedReplicas: true } },
  { name: 'styles-opened-34-anchors', seed: 34, rule: 'gap', attrs: 'anchors', bound: 10, sameSchedulesAs: 'styles-opened-34', options: { withStyles: true, openedReplicas: true } },
  { name: 'partial-styles-35-anchors', seed: 35, rule: 'gap', attrs: 'anchors', bound: 10, sameSchedulesAs: 'partial-styles-35', options: { withStyles: true, partialDelivery: true } },
  { name: 'partial-styles-36-anchors', seed: 36, rule: 'gap', attrs: 'anchors', bound: 10, sameSchedulesAs: 'partial-styles-36', options: { withStyles: true, partialDelivery: true, openedReplicas: false } },
  { name: 'styles-created-31-short-carry', seed: 31, rule: 'gap', attrs: 'carry', bound: 8, options: { steps: 8, withStyles: true, openedReplicas: false } },
  { name: 'styles-created-31-short-anchors', seed: 31, rule: 'gap', attrs: 'anchors', bound: 8, sameSchedulesAs: 'styles-created-31-short-carry', options: { steps: 8, withStyles: true, openedReplicas: false } },
  { name: 'styles-created-31-short-persistent', seed: 31, rule: 'gap', attrs: 'persistent', bound: 8, sameSchedulesAs: 'styles-created-31-short-carry', options: { steps: 8, withStyles: true, openedReplicas: false } },
  { name: 'styles-created-32-short-carry', seed: 32, rule: 'gap', attrs: 'carry', bound: 8, options: { steps: 8, withStyles: true, openedReplicas: false } },
  { name: 'styles-created-32-short-anchors', seed: 32, rule: 'gap', attrs: 'anchors', bound: 8, sameSchedulesAs: 'styles-created-32-short-carry', options: { steps: 8, withStyles: true, openedReplicas: false } },
  { name: 'styles-created-32-short-persistent', seed: 32, rule: 'gap', attrs: 'persistent', bound: 8, sameSchedulesAs: 'styles-created-32-short-carry', options: { steps: 8, withStyles: true, openedReplicas: false } },
  { name: 'styles-opened-33-short-carry', seed: 33, rule: 'gap', attrs: 'carry', bound: 8, options: { steps: 8, withStyles: true, openedReplicas: true } },
  { name: 'styles-opened-33-short-anchors', seed: 33, rule: 'gap', attrs: 'anchors', bound: 8, sameSchedulesAs: 'styles-opened-33-short-carry', options: { steps: 8, withStyles: true, openedReplicas: true } },
  { name: 'styles-opened-33-short-persistent', seed: 33, rule: 'gap', attrs: 'persistent', bound: 8, sameSchedulesAs: 'styles-opened-33-short-carry', options: { steps: 8, withStyles: true, openedReplicas: true } },
  { name: 'styles-opened-34-short-carry', seed: 34, rule: 'gap', attrs: 'carry', bound: 8, options: { steps: 8, withStyles: true, openedReplicas: true } },
  { name: 'styles-opened-34-short-anchors', seed: 34, rule: 'gap', attrs: 'anchors', bound: 8, sameSchedulesAs: 'styles-opened-34-short-carry', options: { steps: 8, withStyles: true, openedReplicas: true } },
  { name: 'styles-opened-34-short-persistent', seed: 34, rule: 'gap', attrs: 'persistent', bound: 8, sameSchedulesAs: 'styles-opened-34-short-carry', options: { steps: 8, withStyles: true, openedReplicas: true } },
  { name: 'partial-styles-35-short-carry', seed: 35, rule: 'gap', attrs: 'carry', bound: 8, options: { steps: 8, withStyles: true, partialDelivery: true } },
  { name: 'partial-styles-35-short-anchors', seed: 35, rule: 'gap', attrs: 'anchors', bound: 8, sameSchedulesAs: 'partial-styles-35-short-carry', options: { steps: 8, withStyles: true, partialDelivery: true } },
  { name: 'partial-styles-35-short-persistent', seed: 35, rule: 'gap', attrs: 'persistent', bound: 8, sameSchedulesAs: 'partial-styles-35-short-carry', options: { steps: 8, withStyles: true, partialDelivery: true } },
  { name: 'partial-styles-36-short-carry', seed: 36, rule: 'gap', attrs: 'carry', bound: 8, options: { steps: 8, withStyles: true, partialDelivery: true, openedReplicas: false } },
  { name: 'partial-styles-36-short-anchors', seed: 36, rule: 'gap', attrs: 'anchors', bound: 8, sameSchedulesAs: 'partial-styles-36-short-carry', options: { steps: 8, withStyles: true, partialDelivery: true, openedReplicas: false } },
  { name: 'partial-styles-36-short-persistent', seed: 36, rule: 'gap', attrs: 'persistent', bound: 8, sameSchedulesAs: 'partial-styles-36-short-carry', options: { steps: 8, withStyles: true, partialDelivery: true, openedReplicas: false } },
];

function parseArgs(argv) {
  const out = {};
  for (let i = 0; i < argv.length; i += 2) out[argv[i].replace(/^--/, '')] = argv[i + 1];
  return out;
}

const showsClass = (cls, run, bound) => (schedule) => {
  const trace = execute(schedule, { rule: run.rule, attrs: run.attrs ?? 'carry', witnessBound: bound });
  return classifyTrial(trace.checks, trace.ops).classes.includes(cls);
};

/** Compact evidence of a classified record. */
function compact(rec) {
  const out = { ...rec };
  if (out.reference) out.reference = renderView(out.reference);
  return out;
}

function summaryLines(s) {
  const rows = [
    ['rule / attrs', `${s.rule} / ${s.attrs}`],
    ['seed', s.seed],
    ['trials', s.trials],
    ['options', JSON.stringify(s.options)],
    ['edits', s.edits],
    ['deliveries', s.deliveries],
    ['sends (pending after)', `${s.sends} (${s.pendingSends})`],
    ['opens', s.opens],
    ['versions checked', s.versionsChecked],
    ['witness skips (bound / partial)', `${s.witnessSkips} / ${s.witnessSkipsPartial}`],
    ['causal gaps', s.causalGaps],
    ['execution anomalies', s.anomalies],
    ['failing trials', s.failingTrials],
    ...CHECKS.map((c) => [`  ${c} (failures / trials)`, `${s.failuresByCheck[c]} / ${s.trialsFailingByCheck[c]}`]),
    ...['insert', 'delete', 'mark', 'unmark'].filter((k) => s.localMeaningByKind?.[k]).map((k) => [`  localMeaning on ${k} (failures / requests)`, `${s.localMeaningFailuresByKind?.[k] ?? 0} / ${s.localMeaningByKind[k]}`]),
  ];
  const w = Math.max(...rows.map((r) => r[0].length));
  return rows.map(([k, v]) => k.padEnd(w) + '  ' + v);
}

function main() {
  const args = parseArgs(process.argv.slice(2));
  const trials = Number(args.trials ?? 200);
  const only = args.only ? new Set(args.only.split(',')) : null;
  const doShrink = args.shrink !== 'false';
  const m = verifySources();
  console.log(`sources verified: ${m.package}@${m.version}`);
  mkdirSync('results/campaign', { recursive: true });
  const out = { package: `${m.package}@${m.version}`, node: process.version, classes: CLASSES, trials, runs: [] };
  for (const run of RUNS) {
    if (only && !only.has(run.name)) continue;
    const bound = run.bound ?? 12;
    const attrs = run.attrs ?? 'carry';
    const t0 = Date.now();
    const { summary, failing, shrunk } = runCampaign({ rule: run.rule, attrs, seed: run.seed, trials, bound, options: { steps: 12, ...run.options }, renderFailure, shrink: false });
    summary.rule = run.rule;
    summary.attrs = attrs;
    summary.seconds = (Date.now() - t0) / 1000;
    writeJson(`results/campaign/${run.name}.json`, { summary, failing, shrunk });
    writeFileSync(`results/campaign/${run.name}.log`, summaryLines(summary).join('\n') + '\n');
    const byTrial = {};
    const byOnset = {};
    const byRecord = {};
    const expandSplit = { consistent: 0, inconsistent: 0 };
    const classified = failing.map((t) => ({ t, c: classifyTrial(t.checks, t.ops) }));
    for (const { c } of classified) {
      if (c.onset) byOnset[c.onset] = (byOnset[c.onset] ?? 0) + 1;
      for (const k of c.classes) byTrial[k] = (byTrial[k] ?? 0) + 1;
      for (const r of c.records) {
        byRecord[r.class] = (byRecord[r.class] ?? 0) + 1;
        if (r.class === 'L-001') expandSplit[r.expandConsistent ? 'consistent' : 'inconsistent']++;
      }
    }
    const representatives = [];
    const seen = new Set();
    for (const { t, c } of classified)
      for (const cls of c.classes) {
        if (seen.has(cls)) continue;
        seen.add(cls);
        const rep = { class: cls, trial: t.trial, seed: t.seed, originalSteps: t.schedule.steps.length };
        if (doShrink) {
          const res = shrink(t.schedule, showsClass(cls, run, bound), { rule: run.rule, attrs });
          const trace = execute(res.schedule, { rule: run.rule, attrs, witnessBound: bound });
          const recs = classifyTrial(trace.checks, trace.ops).records.filter((r) => r.class === cls);
          const f = failuresOf(trace).find((x) => x.step === recs[0]?.step && x.check === recs[0]?.check);
          Object.assign(rep, { schedule: res.schedule, rendered: res.schedule.steps.map(renderStep), evidence: recs.slice(0, 2).map(compact), failure: f && renderFailure(f) });
        } else rep.evidence = c.records.filter((r) => r.class === cls).slice(0, 1).map(compact);
        representatives.push(rep);
      }
    const entry = { name: run.name, source: `results/campaign/${run.name}.json`, sameSchedulesAs: run.sameSchedulesAs, summary, failureRecordsByClass: byRecord, trialsByClass: byTrial, trialsByOnset: byOnset, boundaryRecordsByExpand: expandSplit, representatives };
    out.runs.push(entry);
    console.log(`${run.name} (${summary.seconds}s): failing ${summary.failingTrials}/${trials} by check ${JSON.stringify(summary.trialsFailingByCheck)} trials by class ${JSON.stringify(byTrial)} onset ${JSON.stringify(byOnset)}`);
  }
  writeJson(only ? `results/campaign-${[...only].join('+')}.json` : 'results/campaign.json', out);
  verifySources();
  console.log('sources verified after run');
}

main();
