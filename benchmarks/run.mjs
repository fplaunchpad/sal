// Task #98 orchestrator: reproduces every number in README.md / results/.
//
//   node run.mjs             full matrix (approx 25-35 min, dominated by
//                            our as-shipped O(live-set) apply on the two
//                            big traces + the python projection)
//   node run.mjs --quick     small trace + freq preset + churn only
//   node run.mjs --only seq:sal   (substring filter on job ids)
//   node run.mjs --skip-projection
//
// Each job runs in a FRESH child process under --expose-gc (heap isolation;
// one system's wasm/GC noise cannot leak into another's numbers). Jobs run
// sequentially, never in parallel.

import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const HERE = dirname(fileURLToPath(import.meta.url));
const args = process.argv.slice(2);
const quick = args.includes('--quick');
const skipProjection = args.includes('--skip-projection');
const onlyIdx = args.indexOf('--only');
const only = onlyIdx >= 0 ? args[onlyIdx + 1] : null;

const SYSTEMS = ['sal', 'yjs', 'automerge', 'loro', 'listpositions'];
const SEQ_TRACES = quick
  ? ['friendsforever_flat']
  : ['friendsforever_flat', 'clownschool_flat', 'seph-blog1', 'automerge-paper'];
const PRESETS = quick ? ['freq'] : ['freq', 'bulk'];

const jobs = [];
for (const t of SEQ_TRACES) {
  for (const s of SYSTEMS) {
    jobs.push({ id: `seq:${s}:${t}`, cmd: 'node', argv: ['--expose-gc', join(HERE, 'workloads', 'seq.mjs'), s, t] });
  }
}
for (const p of PRESETS) {
  for (const s of SYSTEMS) {
    jobs.push({ id: `concurrent:${s}:${p}`, cmd: 'node', argv: ['--expose-gc', join(HERE, 'workloads', 'concurrent.mjs'), s, p] });
  }
}
for (const s of SYSTEMS) {
  jobs.push({ id: `churn:${s}`, cmd: 'node', argv: ['--expose-gc', join(HERE, 'workloads', 'churn.mjs'), s] });
}
if (!skipProjection) {
  jobs.push({ id: 'projection', cmd: 'python3',
    argv: [join(HERE, 'tools', 'run_table_projection.py'), ...SEQ_TRACES] });
}
jobs.push({ id: 'summarize', cmd: 'node', argv: [join(HERE, 'tools', 'summarize.mjs')] });

const failures = [];
for (const job of jobs) {
  if (only && job.id !== 'summarize' && !job.id.includes(only)) continue;
  console.log(`\n=== ${job.id}`);
  const t0 = Date.now();
  const r = spawnSync(job.cmd, job.argv, { stdio: 'inherit', cwd: HERE });
  console.log(`=== ${job.id} done in ${((Date.now() - t0) / 1000).toFixed(1)} s (exit ${r.status})`);
  if (r.status !== 0) failures.push(job.id);
}

if (failures.length > 0) {
  console.error(`\nFAILED jobs: ${failures.join(', ')}`);
  process.exit(1);
}
console.log('\nAll jobs passed. Matrix: results/summary.md');
