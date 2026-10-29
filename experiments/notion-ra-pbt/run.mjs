/**
 * Command-line driver.
 *
 *   node run.mjs --mode laws --model demo|anchor-absorb [--texts '["x"]']
 *                [--profile structure|text|format] [--observation view|bag]
 *                [--replicas R] [--sync P] [--seed S] [--trials N] [--size K]
 *                [--output results/<file>.json]
 *   node run.mjs --mode endtoend --model demo|anchor-absorb [--texts ...] [--profile ...]
 *                [--seed S] [--trials N] [--steps K] [--replicas R] [--partial]
 *                [--bound B] [--output results/<file>.json]
 *   node run.mjs --mode regressions
 *
 * The models are loaded from $NOTION_RA_PBT_SOURCES (prepared by
 * ra-pbt/instances/notion/prepare.js). Exit status: 0 when no property
 * failed (laws, endtoend) or every regression held; 1 otherwise.
 */
import { writeJson } from '../../ra-pbt/src/index.js';
import { parseArgs, runLaws, runEndToEnd } from './lib.mjs';

const args = parseArgs(process.argv.slice(2));
const num = (k, d) => (args[k] === undefined ? d : Number(args[k]));
const common = {
  model: args.model ?? 'demo',
  texts: args.texts ? JSON.parse(args.texts) : ['x'],
  profile: args.profile ?? 'structure',
  seed: num('seed', 1),
};
let out;
let failed;
if (args.mode === 'laws') {
  out = await runLaws({ ...common, observation: args.observation ?? 'view', replicas: num('replicas', 3), syncProbability: num('sync', 0.3), trials: num('trials', 150), size: num('size', 12) });
  failed = out.properties.some((p) => p.verdict === 'fail');
  for (const p of out.properties) console.log(`${p.name.padEnd(24)} ${p.verdict.padEnd(15)} ${p.runs}${p.classification ? '  ' + p.classification.catalogue.join(',') + ' (' + p.counterexample.size + ' events)' : ''}`);
} else if (args.mode === 'endtoend') {
  out = await runEndToEnd({ ...common, trials: num('trials', 50), steps: num('steps', 12), replicas: args.replicas && Number(args.replicas), partial: !!args.partial, bound: num('bound', 12) });
  failed = out.summary.failingTrials > 0;
  console.log(JSON.stringify({ failingTrials: out.summary.failingTrials, trialsFailingByCheck: out.summary.trialsFailingByCheck, classes: out.failingTrialsByCheckAndClass }));
  for (const s of out.shrunk) console.log(`${s.signature}: ${s.edits} edits / ${s.steps} steps -> ${s.classification.catalogue.join(',')}`);
} else if (args.mode === 'regressions') {
  const { main } = await import('./regressions.mjs');
  process.exit(await main());
} else throw new Error('--mode laws|endtoend|regressions');
if (args.output) writeJson(args.output, out);
process.exit(failed ? 1 : 0);
