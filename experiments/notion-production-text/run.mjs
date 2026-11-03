/**
 * Command-line driver.
 *
 *   node run.mjs --mode search --seed S --trials N [--steps K] [--bold] [--partial]
 *                [--opened true|false] [--replicas R] [--bound B]
 *                [--rule gap|left|both] [--reading anchored|interval]
 *                [--local positional|inherit] [--no-shrink] [--output <file>.json]
 *   node run.mjs --mode replay --input <file.json> [--rule ..] [--reading ..] [--local ..] [--output <file.json>]
 *   node run.mjs --mode regressions
 *
 * NOTION_PRODUCTION_LIBRARY must name the exported library (outside the
 * repository); with NOTION_PRODUCTION_CACHE set, the source check also ties
 * every module body to the downloaded public assets. The check runs before
 * and after every mode. Exit status: 0 when no check failed (search,
 * replay) or every regression held; 1 otherwise.
 */
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { failuresOf, writeJson } from '../../ra-pbt/src/index.js';
import { verifySources, describeVerification, execute, instanceFor, renderStep, CHECKS } from '../../ra-pbt/instances/notion-production-text/index.js';
import { runSearch, yieldToTimers } from './search.mjs';
import { renderFailure } from './render.mjs';

function parseArgs(argv) {
  const flags = new Set(['bold', 'partial', 'no-shrink']);
  const out = {};
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (!a.startsWith('--')) throw new Error('unexpected argument ' + a);
    const k = a.slice(2);
    out[k] = flags.has(k) ? true : argv[++i];
  }
  return out;
}

export const configOf = (args) => ({ rule: args.rule ?? 'gap', reading: args.reading ?? 'anchored', local: args.local ?? 'positional' });

function printSummary(s, shrunk) {
  const rows = [
    ['seed', s.seed],
    ['trials', s.trials],
    ['options', JSON.stringify(s.options)],
    ['edits', s.edits],
    ['deliveries / sends', `${s.deliveries} / ${s.sends}`],
    ['opens', s.opens],
    ['versions checked', s.versionsChecked],
    ['witness skips (bound / partial)', `${s.witnessSkips} / ${s.witnessSkipsPartial}`],
    ['causal gaps', s.causalGaps],
    ['execution anomalies', s.anomalies],
    ['failing trials', s.failingTrials],
    ...CHECKS.map((c) => [`  ${c} (failures / trials)`, `${s.failuresByCheck[c]} / ${s.trialsFailingByCheck[c]}`]),
    ...['insert', 'delete', 'bold'].filter((k) => s.localMeaningByKind?.[k]).map((k) => [`  localMeaning on ${k} (failures / requests)`, `${s.localMeaningFailuresByKind?.[k] ?? 0} / ${s.localMeaningByKind[k]}`]),
  ];
  const w = Math.max(...rows.map((r) => r[0].length));
  for (const [k, v] of rows) console.log(k.padEnd(w) + '  ' + v);
  for (const x of shrunk) {
    console.log(`\n${x.signature}  (trial ${x.trial}, ${x.originalSteps} -> ${x.schedule.steps.length} steps)`);
    for (const line of x.rendered) console.log('  ' + line);
    if (x.renderedFailure) console.log('  failure: ' + JSON.stringify(x.renderedFailure));
  }
}

async function search(args) {
  const config = configOf(args);
  const options = { steps: Number(args.steps ?? 12), withBold: !!args.bold, partialDelivery: !!args.partial };
  if (args.replicas) options.replicas = Number(args.replicas);
  if (args.opened !== undefined) options.openedReplicas = args.opened === 'true';
  const res = await runSearch(instanceFor(config), {
    seed: Number(args.seed ?? 1),
    trials: Number(args.trials ?? 20),
    bound: Number(args.bound ?? 12),
    options,
    shrink: !args['no-shrink'],
    renderStep,
    renderFailure,
  });
  res.summary.config = config;
  printSummary(res.summary, res.shrunk);
  if (args.output) writeJson(args.output, res);
  return res.summary.failingTrials > 0 || res.summary.anomalies > 0 ? 1 : 0;
}

async function replay(args) {
  const data = JSON.parse(readFileSync(args.input, 'utf8'));
  const schedules = data.steps ? [data] : data.schedule ? [data.schedule] : [...(data.shrunk ?? []).map((x) => x.schedule), ...(data.failing ?? []).map((x) => x.schedule)];
  const config = { ...(data.summary?.config ?? {}), ...Object.fromEntries(Object.entries(configOf(args)).filter(([k]) => args[k] !== undefined)) };
  let anyFail = false;
  const out = [];
  for (const s of schedules) {
    const trace = execute(s, {}, config);
    const fs = failuresOf(trace);
    anyFail ||= fs.length > 0;
    console.log(`${fs.length ? 'FAIL' : 'ok  '} ${s.steps.length} steps: ${CHECKS.map((c) => `${c}=${trace.checks[c].pass ? 'pass' : 'fail'}`).join(' ')}`);
    for (const f of fs.slice(0, 3)) console.log(`     ${f.signature} replica ${f.replica} step ${f.step}`);
    out.push(trace);
    await yieldToTimers();
  }
  if (args.output) writeJson(args.output, out);
  return anyFail ? 1 : 0;
}

async function regressions() {
  const { runAll } = await import('./regressions.mjs');
  const out = await runAll();
  for (const r of out) {
    console.log(`${r.pass ? 'ok  ' : 'FAIL'} ${r.name}${r.pass ? '' : ': ' + r.error}`);
    if (r.results.observed) console.log(`     observed: ${r.results.observed}`);
    if (r.results.admitted) console.log(`     admitted: ${r.results.admitted.join(' | ')}`);
  }
  console.log(`${out.filter((r) => r.pass).length} of ${out.length} regressions hold`);
  return out.every((r) => r.pass) ? 0 : 1;
}

async function main() {
  const args = parseArgs(process.argv.slice(2));
  console.log(describeVerification(verifySources()));
  let code;
  if (args.mode === 'search') code = await search(args);
  else if (args.mode === 'replay') code = await replay(args);
  else if (args.mode === 'regressions') code = await regressions();
  else throw new Error('--mode must be search, replay or regressions');
  verifySources();
  console.log('export verified after run');
  process.exitCode = code;
}

if (process.argv[1] && fileURLToPath(import.meta.url) === resolve(process.argv[1])) await main();
