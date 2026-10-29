/**
 * Classification of a set of search outputs.
 *
 *   node campaign.mjs [--shrink false] <name>=<search-output.json> ...
 *
 * For every run: the search summary, every failure record classified by
 * the instance's mechanism classifier, a histogram of classes over failure
 * records and over trials (a trial counts once per class it shows), and, per
 * class, the first trial
 * showing it shrunk under the predicate "the trial still shows this class".
 * The opened-document family (Y-006) is counted but not shrunk. Writes
 * results/campaign.json.
 */
import { readFileSync, writeFileSync } from 'node:fs';
import { verifySources, execute, shrink, renderStep } from '../../ra-pbt/instances/yjs/index.js';
import { classifySearch, classifyTrace, renderView, CLASSES } from '../../ra-pbt/instances/yjs/classify.js';

const showsClass = (cls, bound) => (schedule) => {
  const trace = execute(schedule, { witnessBound: bound });
  return classifyTrace(schedule, trace.checks).some((r) => r.class === cls);
};

/** Compact evidence of one classified record. */
function compact(rec) {
  const out = { check: rec.check, replica: rec.replica, step: rec.step, class: rec.class };
  if (rec.reference) out.reference = renderView(rec.reference);
  if (rec.differences) out.differences = rec.differences;
  if (rec.pattern) out.pattern = rec.pattern;
  if (rec.markerAnchoredInserts) out.markerAnchoredInserts = rec.markerAnchoredInserts;
  if (rec.items) out.items = rec.items;
  if (rec.notIntegrated) Object.assign(out, { charactersConserved: rec.charactersConserved, pending: rec.pending, notIntegrated: rec.notIntegrated });
  return out;
}

function main() {
  const args = process.argv.slice(2);
  let doShrink = true;
  const runs = [];
  for (let i = 0; i < args.length; i++) {
    if (args[i] === '--shrink') doShrink = args[++i] !== 'false';
    else {
      const [name, path] = args[i].split('=');
      runs.push({ name, path });
    }
  }
  const m = verifySources();
  console.log(`sources verified: ${m.package}@${m.version}`);
  const out = { classes: CLASSES, runs: [] };
  for (const run of runs) {
    const data = JSON.parse(readFileSync(run.path, 'utf8'));
    const classified = classifySearch(data);
    const byFailure = {};
    const byTrial = {};
    const byOnset = {};
    for (const t of classified) {
      if (t.onset) byOnset[t.onset] = (byOnset[t.onset] ?? 0) + 1;
      for (const c of t.classes) byTrial[c] = (byTrial[c] ?? 0) + 1;
      for (const r of t.records) byFailure[r.class] = (byFailure[r.class] ?? 0) + 1;
    }
    const representatives = [];
    const seen = new Set();
    for (const t of classified)
      for (const cls of t.classes) {
        if (seen.has(cls)) continue;
        seen.add(cls);
        const trial = data.failing.find((x) => x.trial === t.trial);
        const rep = { class: cls, trial: t.trial, seed: t.seed, originalSteps: trial.schedule.steps.length };
        if (doShrink && cls !== 'Y-006') {
          const res = shrink(trial.schedule, showsClass(cls, data.summary.witnessBound));
          const trace = execute(res.schedule, { witnessBound: data.summary.witnessBound });
          const recs = classifyTrace(res.schedule, trace.checks).filter((r) => r.class === cls);
          Object.assign(rep, { schedule: res.schedule, rendered: res.schedule.steps.map(renderStep), evidence: recs.slice(0, 2).map(compact) });
        } else {
          rep.evidence = t.records.filter((r) => r.class === cls).slice(0, 1).map(compact);
        }
        representatives.push(rep);
      }
    out.runs.push({
      name: run.name,
      source: run.path,
      summary: data.summary,
      failureRecordsByClass: byFailure,
      trialsByClass: byTrial,
      trialsByOnset: byOnset,
      representatives,
      trials: classified.map((t) => ({ trial: t.trial, seed: t.seed, onset: t.onset, classes: t.classes, records: t.records.map(compact) })),
    });
    console.log(`${run.name}: trials ${JSON.stringify(byTrial)} onset ${JSON.stringify(byOnset)}`);
  }
  writeFileSync('results/campaign.json', JSON.stringify(out, null, 1) + '\n');
  verifySources();
  console.log('sources verified after run');
}

main();
