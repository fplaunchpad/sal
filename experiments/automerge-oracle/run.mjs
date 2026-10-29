/**
 * Command-line driver for the schedule search over Automerge text.
 *
 *   node run.mjs --mode search --seed S --trials N [--steps K] [--format] [--partial]
 *                [--replicas R] [--bound B] [--opened true|false]
 *                [--semantics anchor|marker] --output results/<file>.json
 *   node run.mjs --mode replay --input <file.json> [--semantics anchor|marker] [--output <file.json>]
 *   node run.mjs --mode regressions
 *
 * Source verification runs before and after every mode. Exit status: 0 when
 * no check failed (search, replay) or every regression held; 1 otherwise.
 */
import { readFileSync } from 'node:fs';
import { failuresOf, writeJson } from '../../ra-pbt/src/index.js';
import { verifySources, execute, runCampaign, renderStep, CHECKS } from '../../ra-pbt/instances/automerge/index.js';
import { renderView } from '../../ra-pbt/instances/automerge/classify.js';
import { runRegressions } from './regressions.mjs';

function parseArgs(argv) {
  const out = {};
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (!a.startsWith('--')) throw new Error('unexpected argument ' + a);
    const k = a.slice(2);
    if (k === 'format' || k === 'partial') out[k] = true;
    else out[k] = argv[++i];
  }
  return out;
}

const isView = (x) => Array.isArray(x) && x.every((e) => e && typeof e === 'object' && 'ch' in e);

/** Views inside a failure value rendered compactly; other values unchanged. */
function renderValue(x) {
  if (isView(x)) return renderView(x);
  if (x && typeof x === 'object' && !Array.isArray(x))
    return Object.fromEntries(Object.entries(x).map(([k, v]) => [k, Array.isArray(v) && v.every(isView) ? v.map(renderView) : renderValue(v)]));
  return x;
}

/** Compact rendering of a check failure. */
export function renderFailure(f) {
  const out = {};
  for (const k of ['replica', 'step', 'request', 'before', 'expected', 'actual', 'opKeys']) if (f[k] !== undefined) out[k] = renderValue(f[k]);
  return out;
}

/** Generation options from command-line arguments. */
export function optionsOf(args) {
  const options = { steps: Number(args.steps ?? 12), withFormat: !!args.format, partialDelivery: !!args.partial };
  if (args.replicas) options.replicas = Number(args.replicas);
  if (args.opened !== undefined) options.openedReplicas = args.opened === 'true';
  return options;
}

function search(args) {
  const semantics = args.semantics ?? 'anchor';
  const { summary, failing, shrunk } = runCampaign({
    seed: Number(args.seed ?? 1),
    trials: Number(args.trials ?? 20),
    bound: Number(args.bound ?? 12),
    options: optionsOf(args),
    semantics,
    renderFailure,
  });
  summary.semantics = semantics;
  printSummary(summary, shrunk);
  if (args.output) writeJson(args.output, { summary, failing, shrunk });
  return summary.failingTrials > 0 ? 1 : 0;
}

export function printSummary(s, shrunk = []) {
  const rows = [
    ['semantics', s.semantics],
    ['seed', s.seed ?? JSON.stringify(s.seeds)],
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
  ];
  const w = Math.max(...rows.map((r) => r[0].length));
  for (const [k, v] of rows) console.log(k.padEnd(w) + '  ' + v);
  for (const x of shrunk) {
    console.log(`\n${x.signature}  (trial ${x.trial}, ${x.originalSteps} -> ${x.schedule.steps.length} steps)`);
    for (const line of x.rendered) console.log('  ' + line);
    if (x.renderedFailure) console.log('  failure: ' + JSON.stringify(x.renderedFailure));
  }
}

function replay(args) {
  const semantics = args.semantics ?? 'anchor';
  const data = JSON.parse(readFileSync(args.input, 'utf8'));
  const schedules = data.steps ? [data] : data.schedule ? [data.schedule] : [...(data.shrunk ?? []).map((x) => x.schedule), ...(data.failing ?? []).map((x) => x.schedule)];
  let anyFail = false;
  const out = [];
  for (const s of schedules) {
    const trace = execute(s, { semantics });
    const fs = failuresOf(trace);
    anyFail ||= fs.length > 0;
    console.log(`${fs.length ? 'FAIL' : 'ok  '} ${s.steps.length} steps: ${CHECKS.map((c) => `${c}=${trace.checks[c].pass ? 'pass' : 'fail'}`).join(' ')}`);
    for (const f of fs.slice(0, 3)) console.log(`     ${f.signature} replica ${f.replica} step ${f.step}`);
    out.push(trace);
  }
  if (args.output) writeJson(args.output, out);
  return anyFail ? 1 : 0;
}

function regressions() {
  const out = runRegressions();
  for (const r of out) {
    console.log(`${r.pass ? 'ok  ' : 'FAIL'} ${r.name}${r.pass ? '' : ': ' + r.error}`);
    if (r.results.observed) console.log(`     observed: ${renderView(r.results.observed)}`);
    if (r.results.admitted) console.log(`     admitted (anchor): ${r.results.admitted.map(renderView).join(' | ')}`);
  }
  return out.every((r) => r.pass) ? 0 : 1;
}

function main() {
  const args = parseArgs(process.argv.slice(2));
  const m = verifySources();
  console.log(`sources verified: ${m.package}@${m.version}`);
  let code;
  if (args.mode === 'search') code = search(args);
  else if (args.mode === 'replay') code = replay(args);
  else if (args.mode === 'regressions') code = regressions();
  else throw new Error('--mode must be search, replay or regressions');
  verifySources();
  console.log('sources verified after run');
  process.exitCode = code;
}

if (process.argv[1] && process.argv[1].endsWith('run.mjs')) main();
