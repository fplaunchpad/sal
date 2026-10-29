/**
 * The campaign: named searches over seeds, mixes and specification
 * configurations, each written to results/campaign/<name>.json, and their
 * summary table, results/campaign.json.
 *
 *   node campaign.mjs run <name> [<name> ...]
 *   node campaign.mjs summarise
 *   node campaign.mjs list
 *
 * Runs sharing a seed and options execute the same schedules, so their
 * verdicts differ only by the specification configuration.
 */
import { readFileSync, existsSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { writeJson, CHECKS } from '../../ra-pbt/src/index.js';
import { instanceFor, renderStep, verifySources, describeVerification } from '../../ra-pbt/instances/notion-production-text/index.js';
import { classifyTrace } from '../../ra-pbt/instances/notion-production-text/classify.js';
import { runSearch } from './search.mjs';
import { renderFailure } from './render.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const PLAIN = { withBold: false };
const BOLD = { withBold: true };
const INHERIT = { local: 'inherit' };

export const RUNS = {
  'plain-created-21': { seed: 21, options: PLAIN, config: {} },
  'plain-left-21': { seed: 21, options: PLAIN, config: { rule: 'left' } },
  'plain-both-21': { seed: 21, options: PLAIN, config: { rule: 'both' } },
  'plain-opened-22': { seed: 22, options: { ...PLAIN, openedReplicas: true }, config: {} },
  'plain-partial-23': { seed: 23, options: { ...PLAIN, partialDelivery: true }, config: {} },
  'plain-partial-left-23': { seed: 23, options: { ...PLAIN, partialDelivery: true }, config: { rule: 'left' } },
  'plain-four-24': { seed: 24, options: { ...PLAIN, replicas: 4, steps: 14 }, config: { rule: 'left' }, bound: 14 },
  'bold-created-31': { seed: 31, options: BOLD, config: {} },
  'bold-inherit-31': { seed: 31, options: BOLD, config: INHERIT },
  'bold-left-31': { seed: 31, options: BOLD, config: { ...INHERIT, rule: 'left' } },
  'bold-both-31': { seed: 31, options: BOLD, config: { ...INHERIT, rule: 'both' } },
  'bold-interval-31': { seed: 31, options: BOLD, config: { ...INHERIT, reading: 'interval' } },
  'bold-opened-32': { seed: 32, options: { ...BOLD, openedReplicas: true }, config: INHERIT },
  'bold-opened-left-32': { seed: 32, options: { ...BOLD, openedReplicas: true }, config: { ...INHERIT, rule: 'left' } },
  'bold-partial-33': { seed: 33, options: { ...BOLD, partialDelivery: true }, config: INHERIT },
  'bold-partial-left-33': { seed: 33, options: { ...BOLD, partialDelivery: true }, config: { ...INHERIT, rule: 'left' } },
  'bold-long-34': { seed: 34, options: { ...BOLD, steps: 16, replicas: 3 }, config: INHERIT, bound: 16 },
  'bold-long-left-34': { seed: 34, options: { ...BOLD, steps: 16, replicas: 3 }, config: { ...INHERIT, rule: 'left' }, bound: 16 },
  'bold-opened-35': { seed: 35, options: { ...BOLD, openedReplicas: true }, config: INHERIT },
};

const fileOf = (name) => join(here, 'results', 'campaign', `${name}.json`);

async function run(name) {
  const r = RUNS[name];
  if (!r) throw new Error('unknown run ' + name);
  const inst = instanceFor(r.config);
  const res = await runSearch(inst, {
    seed: r.seed,
    trials: r.trials ?? 200,
    bound: r.bound ?? 12,
    options: r.options,
    classify: (schedule, trace) => classifyTrace(inst, schedule, trace.checks),
    renderStep,
    renderFailure,
  });
  res.summary.config = inst.spec && { rule: inst.spec.rule, reading: inst.spec.reading, local: inst.spec.local };
  writeJson(fileOf(name), res);
  const s = res.summary;
  console.log(`${name}: failing ${s.failingTrials}/${s.trials}, versions ${s.versionsChecked}, ` + CHECKS.map((c) => `${c} ${s.failuresByCheck[c]}`).join(', ') + (s.classes ? ' classes ' + JSON.stringify(s.classes.trials) : ''));
}

function summarise() {
  const rows = [];
  for (const name of Object.keys(RUNS)) {
    if (!existsSync(fileOf(name))) continue;
    const { summary: s, shrunk } = JSON.parse(readFileSync(fileOf(name), 'utf8'));
    rows.push({
      name,
      config: s.config,
      options: s.options,
      trials: s.trials,
      edits: s.edits,
      deliveries: s.deliveries,
      sends: s.sends,
      opens: s.opens,
      versionsChecked: s.versionsChecked,
      witnessSkips: s.witnessSkips,
      witnessSkipsTruncated: s.witnessSkipsTruncated ?? 0,
      anomalies: s.anomalies,
      failingTrials: s.failingTrials,
      failuresByCheck: s.failuresByCheck,
      trialsFailingByCheck: s.trialsFailingByCheck,
      localMeaningByKind: s.localMeaningByKind,
      localMeaningFailuresByKind: s.localMeaningFailuresByKind,
      skipped: s.skipped,
      classes: s.classes ?? null,
      shrunk: shrunk.map((x) => ({ signature: x.signature, trial: x.trial, steps: `${x.originalSteps} -> ${x.schedule.steps.length}`, rendered: x.rendered, failure: x.renderedFailure })),
    });
  }
  writeJson(join(here, 'results', 'campaign.json'), { runs: rows });
  const total = (k) => rows.reduce((a, r) => a + r[k], 0);
  console.log(`${rows.length} runs, ${total('trials')} trials, ${total('edits')} edits, ${total('versionsChecked')} versions checked, ${total('anomalies')} anomalies`);
  for (const r of rows) console.log(`${r.name.padEnd(22)} ${JSON.stringify(r.config).padEnd(58)} failing ${String(r.failingTrials).padStart(3)}  ${CHECKS.map((c) => `${c}=${r.failuresByCheck[c]}`).join(' ')}  ${r.classes ? JSON.stringify(r.classes.trials) : ''}`);
}

async function main() {
  const [mode, ...names] = process.argv.slice(2);
  console.log(describeVerification(verifySources()));
  if (mode === 'run') for (const n of names) await run(n);
  else if (mode === 'summarise') summarise();
  else if (mode === 'list') console.log(Object.keys(RUNS).join('\n'));
  else throw new Error('usage: node campaign.mjs run <name>... | summarise | list');
  verifySources();
  console.log('export verified after run');
}

if (process.argv[1] && fileURLToPath(import.meta.url) === resolve(process.argv[1])) await main();
