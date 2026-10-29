/**
 * The search campaign: every feature mix under both mark semantics and
 * several seeds, each run classified by mechanism.
 *
 *   node campaign.mjs [--trials N] [--seeds 31,32] [--mixes plain,marks,...] [--semantics anchor,marker]
 *
 * Mixes: plain (insert and delete), partial-plain (single-change sends with
 * changes held back), marks (bold, italic and link marks, bold inserts),
 * marks-opened (marks, replicas joining by loading a saved document),
 * partial-marks (marks with single-change sends). For every run the search
 * output goes to results/campaign/<mix>-<semantics>-<seed>.json; the summary,
 * the failing trials not explained by an artefact class alone (confirmed),
 * the failure records and trials per class (with the onset class of every
 * failing trial) and, per class, the first trial showing it shrunk under the
 * predicate "the schedule still shows this class" go to results/campaign.json.
 * Exits 0.
 */
import { writeJson } from '../../ra-pbt/src/index.js';
import { verifySources, execute, shrink, runCampaign, renderStep } from '../../ra-pbt/instances/automerge/index.js';
import { classifySearch, classifyTrace, CLASSES } from '../../ra-pbt/instances/automerge/classify.js';

export const MIXES = {
  plain: { withFormat: false },
  'partial-plain': { withFormat: false, partialDelivery: true },
  marks: { withFormat: true, openedReplicas: false },
  'marks-opened': { withFormat: true, openedReplicas: true },
  'partial-marks': { withFormat: true, partialDelivery: true, openedReplicas: false },
};

function parseArgs(argv) {
  const out = {};
  for (let i = 0; i < argv.length; i += 2) out[argv[i].replace(/^--/, '')] = argv[i + 1];
  return out;
}

const showsClass = (cls, semantics, bound) => (schedule) => {
  const trace = execute(schedule, { semantics, witnessBound: bound });
  return classifyTrace(schedule, trace.checks, semantics).some((r) => r.class === cls);
};

function main() {
  const args = parseArgs(process.argv.slice(2));
  const trials = Number(args.trials ?? 200);
  const seeds = (args.seeds ?? '31,32').split(',').map(Number);
  const mixes = (args.mixes ?? Object.keys(MIXES).join(',')).split(',');
  const semanticsList = (args.semantics ?? 'anchor,marker').split(',');
  const m = verifySources();
  console.log(`sources verified: ${m.package}@${m.version}`);
  const out = { version: m.version, classes: CLASSES, trials, runs: [] };
  for (const mix of mixes)
    for (const semantics of semanticsList)
      for (const seed of seeds) {
        const name = `${mix}-${semantics}-${seed}`;
        const t0 = Date.now();
        const data = runCampaign({ seed, trials, options: MIXES[mix], semantics, shrink: false });
        data.summary.semantics = semantics;
        data.summary.mix = mix;
        writeJson(`results/campaign/${name}.json`, data);
        const classified = classifySearch(data, semantics);
        const byFailure = {};
        const byTrial = {};
        const byOnset = {};
        for (const t of classified) {
          if (t.onset) byOnset[t.onset] = (byOnset[t.onset] ?? 0) + 1;
          for (const c of t.classes) byTrial[c] = (byTrial[c] ?? 0) + 1;
          for (const r of t.records) byFailure[r.class] = (byFailure[r.class] ?? 0) + 1;
        }
        const ARTEFACTS = ['layout-artefact', 'view-artefact'];
        const confirmed = classified.filter((t) => t.classes.some((c) => !ARTEFACTS.includes(c))).length;
        const undecided = classified.flatMap((t) => t.records).filter((x) => x.witnessCharsOnly === 'undecided').length;
        const representatives = [];
        const seen = new Set();
        for (const t of classified)
          for (const cls of t.classes) {
            if (seen.has(cls) || cls === 'layout-artefact') continue;
            seen.add(cls);
            const trial = data.failing.find((x) => x.trial === t.trial);
            const res = shrink(trial.schedule, showsClass(cls, semantics, data.summary.witnessBound), { semantics });
            const trace = execute(res.schedule, { semantics });
            const recs = classifyTrace(res.schedule, trace.checks, semantics).filter((r) => r.class === cls);
            representatives.push({ class: cls, trial: t.trial, seed: t.seed, originalSteps: trial.schedule.steps.length, schedule: res.schedule, rendered: res.schedule.steps.map(renderStep), evidence: recs.slice(0, 1) });
          }
        out.runs.push({
          name,
          mix,
          semantics,
          seed,
          source: `results/campaign/${name}.json`,
          summary: data.summary,
          confirmedFailingTrials: confirmed,
          undecidedConfirmations: undecided,
          failureRecordsByClass: byFailure,
          trialsByClass: byTrial,
          trialsByOnset: byOnset,
          representatives,
          trials: classified.map((t) => ({ trial: t.trial, seed: t.seed, onset: t.onset, classes: t.classes })),
        });
        const s = data.summary;
        console.log(`${name}: edits ${s.edits}, versions ${s.versionsChecked}, failing ${s.failingTrials} (confirmed ${confirmed}, undecided ${undecided}), trials by class ${JSON.stringify(byTrial)}, ${Date.now() - t0} ms`);
      }
  writeJson('results/campaign.json', out);
  verifySources();
  console.log('sources verified after run');
}

main();
