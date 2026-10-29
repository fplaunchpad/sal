/**
 * Command-line driver for the schedule search over Loro text.
 *
 *   node run.mjs --mode search --seed S --trials N [--rule gap|left|both] [--attrs carry|inherit] [--steps K]
 *                [--styles] [--keys k1,k2] [--partial] [--replicas R] [--bound B]
 *                [--opened true|false] [--shrink false] --output results/<file>.json
 *   node run.mjs --mode replay --input <file.json> [--rule R] [--attrs A] [--output <file.json>]
 *   node run.mjs --mode regressions
 *
 * Source verification runs before and after every mode. Exit status: 0 when
 * no check failed (search, replay) or every regression held; 1 otherwise.
 */
import { readFileSync } from 'node:fs';
import { failuresOf, writeJson } from '../../ra-pbt/src/index.js';
import { verifySources, execute, runCampaign, renderStep, CHECKS } from '../../ra-pbt/instances/loro/index.js';
import { runRegressions } from './regressions.mjs';
import { renderView, renderFailure } from './render.mjs';

function parseArgs(argv) {
  const out = {};
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (!a.startsWith('--')) throw new Error('unexpected argument ' + a);
    const k = a.slice(2);
    if (k === 'styles' || k === 'partial') out[k] = true;
    else out[k] = argv[++i];
  }
  return out;
}


function search(args) {
  const seed = Number(args.seed ?? 1);
  const trials = Number(args.trials ?? 20);
  const bound = Number(args.bound ?? 12);
  const rule = args.rule ?? 'gap';
  const options = { steps: Number(args.steps ?? 12), withStyles: !!args.styles, partialDelivery: !!args.partial };
  if (args.keys) options.styleKeys = args.keys.split(',');
  if (args.replicas) options.replicas = Number(args.replicas);
  if (args.opened !== undefined) options.openedReplicas = args.opened === 'true';
  const attrs = args.attrs ?? 'carry';
  const { summary, failing, shrunk } = runCampaign({ rule, attrs, seed, trials, bound, options, renderFailure, shrink: args.shrink !== 'false' });
  summary.rule = rule;
  summary.attrs = attrs;
  printSummary(summary, shrunk);
  if (args.output) writeJson(args.output, { summary, failing, shrunk });
  return summary.failingTrials > 0 ? 1 : 0;
}

function printSummary(s, shrunk) {
  const rows = [
    ['seed', s.seed],
    ['rule / attrs', `${s.rule} / ${s.attrs}`],
    ['trials', s.trials],
    ['options', JSON.stringify(s.options)],
    ['edits', s.edits],
    ['deliveries', s.deliveries],
    ['sends (pending after)', `${s.sends} (${s.pendingSends})`],
    ['opens', s.opens],
    ['versions checked', s.versionsChecked],
    ['witness skips (bound / partial / truncated)', `${s.witnessSkips} / ${s.witnessSkipsPartial} / ${s.witnessSkipsTruncated ?? 0}`],
    ['causal gaps', s.causalGaps],
    ['execution anomalies', s.anomalies],
    ['failing trials', s.failingTrials],
    ...CHECKS.map((c) => [`  ${c} (failures / trials)`, `${s.failuresByCheck[c]} / ${s.trialsFailingByCheck[c]}`]),
    ...['insert', 'delete', 'mark', 'unmark'].filter((k) => s.localMeaningByKind?.[k]).map((k) => [`  localMeaning on ${k} (failures / requests)`, `${s.localMeaningFailuresByKind?.[k] ?? 0} / ${s.localMeaningByKind[k]}`]),
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
  const data = JSON.parse(readFileSync(args.input, 'utf8'));
  const schedules = data.steps ? [data] : data.schedule ? [data.schedule] : [...(data.shrunk ?? []).map((x) => x.schedule), ...(data.failing ?? []).map((x) => x.schedule)];
  let anyFail = false;
  const out = [];
  for (const s of schedules) {
    const trace = execute(s, { rule: args.rule ?? data.summary?.rule ?? 'gap', attrs: args.attrs ?? data.summary?.attrs ?? 'carry' });
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
  console.log(`${out.filter((r) => r.pass).length}/${out.length} regressions hold`);
  for (const r of out) {
    console.log(`${r.pass ? 'ok  ' : 'FAIL'} ${r.name}${r.pass ? '' : ': ' + r.error}`);
    if (r.results.observed) console.log(`     observed: ${renderView(r.results.observed)}`);
    if (r.results.admitted) console.log(`     admitted: ${r.results.admitted.map(renderView).join(' | ')}`);
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

main();
