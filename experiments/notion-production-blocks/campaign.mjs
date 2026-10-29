/**
 * The search campaign over the production block layer, written to results/.
 *
 *   NOTION_PRODUCTION_LIBRARY=<export> node campaign.mjs [--quick]
 *
 * For every configuration (seed document, request profile, delivery,
 * replicas, opened replicas, specification reading) and every campaign
 * seed, trials are generated and executed under every ra-pbt check with the
 * final sync. Every failure is classified (classify.js) and every trial is
 * re-executed with the observer to count rejected record applications.
 * For each (check, class) the first trial showing it, over the
 * configurations in order, is shrunk with ra-pbt's shrinker under "some
 * failure of this check still has this class".
 *
 * The library is verified before and after the run (verify-sources.js).
 * Writes results/campaign.json (per configuration) and
 * results/summary.json (per class: configurations, trial counts, the
 * shrunk representative).
 */
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { writeJson } from '../../ra-pbt/src/index.js';
import { withVerifiedLibrary } from '../../ra-pbt/instances/notion-production-blocks/index.js';
import { searchConfiguration, shrinkClass, runClassified, renderStep, renderFailure } from './lib.mjs';
import { failuresOf, execute } from '../../ra-pbt/src/index.js';
import { productionBlocksInstance } from '../../ra-pbt/instances/notion-production-blocks/index.js';

const here = dirname(fileURLToPath(import.meta.url));
const quick = process.argv.includes('--quick');
const T = (n) => (quick ? Math.max(5, Math.round(n / 10)) : n);
const SEEDS = quick ? [1] : [1, 2, 3];

export const CONFIGS = [
  { name: 'abc-blocks3-structure', texts: ['a', 'b', 'c'], profile: 'structure', partial: true, replicas: 2, steps: 10, trials: 100 },
  { name: 'abc-blocks3-structure-r3', texts: ['a', 'b', 'c'], profile: 'structure', partial: true, replicas: 3, steps: 12, trials: 100 },
  { name: 'abc-structure', texts: ['abc'], profile: 'structure', partial: true, steps: 10, trials: 100 },
  { name: 'x-structure', texts: ['x'], profile: 'structure', partial: true, replicas: 2, steps: 10, trials: 100 },
  { name: 'ab-cd-blocks', texts: ['ab', 'cd'], profile: 'blocks', partial: true, steps: 10, trials: 100 },
  { name: 'ab-cd-blocks-exchange', texts: ['ab', 'cd'], profile: 'blocks', partial: false, steps: 12, trials: 100 },
  { name: 'a-blocks-exchange', texts: ['a'], profile: 'blocks', partial: false, steps: 12, trials: 100 },
  { name: 'ab-format', texts: ['ab'], profile: 'format', partial: true, replicas: 2, steps: 8, trials: 100 },
  { name: 'abc-format', texts: ['abc'], profile: 'format', partial: true, replicas: 2, steps: 8, trials: 100 },
  { name: 'ab-c-mixed', texts: ['ab', 'c'], profile: 'mixed', partial: true, steps: 10, trials: 100 },
  { name: 'ab-c-mixed-opened', texts: ['ab', 'c'], profile: 'mixed', partial: true, opened: true, steps: 10, trials: 100 },
  { name: 'abc-blocks-opened-exchange', texts: ['abc'], profile: 'blocks', partial: false, opened: true, steps: 10, trials: 100 },
  { name: 'abc-blocks3-structure-source-reading', texts: ['a', 'b', 'c'], profile: 'structure', partial: true, replicas: 2, steps: 10, trials: 100, reading: { splitPlacement: 'source' } },
  { name: 'ab-c-mixed-issue-reading', texts: ['ab', 'c'], profile: 'mixed', partial: true, steps: 10, trials: 100, reading: { inherit: 'issue' } },
  { name: 'abc-structure-record-model-clocks', texts: ['abc'], profile: 'structure', partial: true, replicas: 1, steps: 8, trials: 100, reading: { liveClock: false } },
];

export async function campaign() {
  return withVerifiedLibrary(async (lib) => {
    const t0 = Date.now();
    const configs = [];
    const firstByClass = new Map();
    for (const cfg of CONFIGS) {
      const t = Date.now();
      const r = searchConfiguration(lib, { ...cfg, trials: T(cfg.trials) }, SEEDS);
      r.ms = Date.now() - t;
      for (const [k, v] of Object.entries(r.first)) if (!firstByClass.has(k)) firstByClass.set(k, { config: cfg.name, options: r.options, ...v });
      delete r.first;
      configs.push(r);
      console.log(`${cfg.name}: ${r.totals.trials} trials, ${r.totals.failingTrials} failing, ${r.totals.trialsWithRejection} with a rejected record, ${JSON.stringify(r.trialsByClass)} (${r.ms} ms)`);
    }
    const classes = {};
    for (const [key, first] of firstByClass) {
      const [check, cls] = key.split(':');
      const res = shrinkClass(lib, first.options, first.schedule, check, cls);
      const { trace, failing, classes: got } = runClassified(lib, first.options, res.schedule);
      const f = failuresOf(trace).find((x) => x.check === check);
      classes[key] = {
        check,
        class: cls,
        configurations: configs.filter((c) => c.trialsByClass[key]).map((c) => ({ name: c.config.name, trials: c.trialsByClass[key], of: c.totals.trials })),
        firstFound: { config: first.config, campaignSeed: first.campaignSeed, trial: first.trial, seed: first.seed, steps: first.schedule.steps.length },
        shrunk: {
          options: first.options,
          schedule: res.schedule,
          rendered: res.schedule.steps.map(renderStep),
          edits: res.schedule.steps.filter((s) => s.type === 'edit').length,
          reductions: res.reductions.length,
          failingChecks: failing,
          classes: got,
          failure: f && renderFailure(f),
        },
      };
      console.log(`shrunk ${key}: ${res.schedule.steps.length} steps (${classes[key].shrunk.edits} edits)`);
    }
    const sum = (k) => configs.reduce((a, c) => a + c.totals[k], 0);
    const summary = {
      scope: 'Production Notion block-layer editing code (exported library, verified digests), shared record handlers, harness block creation and removal, causal peer-to-peer delivery; not live production',
      seeds: SEEDS,
      quick,
      trials: sum('trials'),
      edits: sum('edits'),
      versionsChecked: sum('versionsChecked'),
      witnessSkips: sum('witnessSkips'),
      failingTrials: sum('failingTrials'),
      trialsWithRejection: sum('trialsWithRejection'),
      rejectedApplies: sum('rejectedApplies'),
      determinismRuns: configs.reduce((a, c) => a + c.runsByCheck.determinism, 0),
      determinismFailures: configs.reduce((a, c) => a + c.failuresByCheck.determinism, 0),
      ms: Date.now() - t0,
      classes,
    };
    writeJson(join(here, 'results', quick ? 'campaign-quick.json' : 'campaign.json'), { configs });
    writeJson(join(here, 'results', quick ? 'summary-quick.json' : 'summary.json'), summary);
    return summary;
  });
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  const s = await campaign();
  console.log(`${s.trials} trials, ${s.failingTrials} failing, ${Object.keys(s.classes).length} (check, class) groups, ${s.ms} ms`);
}
