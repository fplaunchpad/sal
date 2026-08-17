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

const SYSTEMS = ['rga', 'embed-rga', 'sided-embed-rga', 'sal', 'sal-shared', 'sal-sided', 'sal-sided-shared', 'sal-sided-unified', 'yjs', 'automerge', 'loro', 'listpositions'];
const SEQ_TRACES = quick
  ? ['friendsforever_flat']
  : ['friendsforever_flat', 'clownschool_flat', 'seph-blog1', 'automerge-paper'];
const PRESETS = quick ? ['freq'] : ['freq', 'bulk'];
const SAL_GC_MODES = ['none', 'history', 'state', 'both', 'both-delayed'];
const PERITEXT_GC_MODES = ['none', 'history', 'text-state', 'full-state', 'both', 'both-delayed'];
const PERITEXT_SCENARIOS = ['concurrent-rich', 'format-trace', 'mark-churn',
  'marked-delete-churn', 'offline-rich', 'empty-rich', 'multi-epoch-rich'];
const SAL_REPRESENTATIONS = ['absolute', 'shared'];
const PERITEXT_KERNELS = ['rga', 'embed-rga'];
const PERITEXT_KERNEL_GC_MODES = ['none', 'history', 'state', 'both'];

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
for (const p of PRESETS) {
  for (const representation of SAL_REPRESENTATIONS) for (const mode of SAL_GC_MODES) {
    jobs.push({ id: `plain-gc:${representation}:${mode}:${p}`, cmd: 'node',
      argv: ['--expose-gc', join(HERE, 'workloads', 'plain-gc.mjs'), mode, p, representation] });
  }
}
jobs.push({ id: 'peritext:semantic-spots', cmd: 'node',
  argv: [join(HERE, 'tools', 'check-peritext-semantics.mjs')] });
for (const p of PRESETS) {
  for (const scenario of PERITEXT_SCENARIOS) {
    for (const representation of SAL_REPRESENTATIONS) for (const mode of PERITEXT_GC_MODES) {
      jobs.push({ id: `peritext:${representation}:${scenario}:${mode}:${p}`, cmd: 'node',
        argv: ['--expose-gc', join(HERE, 'workloads', 'peritext-gc.mjs'), mode, p, scenario, representation] });
    }
  }
}
jobs.push({ id: 'peritext:ablation-gate', cmd: 'node',
  argv: [join(HERE, 'tools', 'check-peritext-ablation.mjs')] });
for (const kernel of PERITEXT_KERNELS) for (const mode of PERITEXT_KERNEL_GC_MODES) for (const topology of ['spine', 'leaves']) {
  jobs.push({ id: `peritext-kernel:${kernel}:${mode}:${quick ? 'quick' : 'full'}:${topology}`, cmd: 'node',
    argv: ['--expose-gc', join(HERE, 'workloads', 'peritext-kernel-gc.mjs'), kernel, mode, quick ? 'quick' : 'full', topology] });
}
for (const s of SYSTEMS) {
  jobs.push({ id: `churn:${s}`, cmd: 'node', argv: ['--expose-gc', join(HERE, 'workloads', 'churn.mjs'), s] });
}
if (!skipProjection) {
  jobs.push({ id: 'projection', cmd: 'python3',
    argv: [join(HERE, 'tools', 'run_table_projection.py'), ...SEQ_TRACES] });
}
// SHIPPED run-table serializer (task #104): fast final-state serialization +
// round-trip gates + projection cross-check. Runs after projection.
jobs.push({ id: 'run-table-shipped', cmd: 'node',
  argv: [join(HERE, 'tools', 'run_table_shipped.mjs'), ...SEQ_TRACES] });
jobs.push({ id: 'normalize', cmd: 'node', argv: [join(HERE, 'tools', 'normalize.mjs')] });
jobs.push({ id: 'summarize', cmd: 'node', argv: [join(HERE, 'tools', 'summarize.mjs')] });

const failures = [];
for (const job of jobs) {
  if (only && !['normalize', 'summarize'].includes(job.id) && !job.id.includes(only)) continue;
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
