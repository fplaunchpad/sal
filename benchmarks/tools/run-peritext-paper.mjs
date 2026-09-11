// Repeated, paper-facing Peritext evaluation. The design deliberately avoids
// the full Cartesian product: each retained cell answers a stated GC claim.

import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const HERE = dirname(fileURLToPath(import.meta.url));
const ROOT = join(HERE, '..'), RAW = join(ROOT, 'results', 'raw');
const repetitions = Number(process.argv[2] ?? 3);
const smoke = process.argv.includes('--smoke');
// The old RGA state hook performs current-read-only dead-leaf pruning and is
// retained as a negative control. It is not continuation-safe, so paper-facing
// combined-GC measurements include only the two continuation-safe collectors.
const kernels = ['embed-rga', 'sided-embed-rga'];
const design = smoke ? { 'empty-rich': ['none', 'both'] } : {
  // Separates history GC, per-state GC, and their composition.
  'concurrent-rich': ['none', 'history', 'full-state', 'both'],
  'format-trace': ['none', 'history', 'full-state', 'both'],
  'mark-churn': ['none', 'full-state', 'both'],
  'empty-rich': ['none', 'full-state', 'both'],
  // Exercises evidence refusal and repeated collection without redundant modes.
  'offline-rich': ['none', 'both-delayed'],
  'multi-epoch-rich': ['none', 'both'],
};
if (!Number.isInteger(repetitions) || repetitions < 1)
  throw new Error('repetitions must be a positive integer');

const rows = [];
for (let repetition = 1; repetition <= repetitions; repetition++) {
  for (const [scenario, modes] of Object.entries(design)) {
    for (const kernel of kernels) for (const mode of modes) {
      const args = ['--expose-gc', join(ROOT, 'workloads', 'peritext-gc.mjs'),
        mode, smoke ? 'freq' : 'bulk', scenario, kernel];
      const run = spawnSync(process.execPath, args, { cwd: ROOT, encoding: 'utf8' });
      if (run.status !== 0) throw new Error(`${kernel}/${scenario}/${mode} failed:\n${run.stdout}\n${run.stderr}`);
      const file = join(RAW, `peritext-${scenario}-${mode}-${smoke ? 'freq' : 'bulk'}-${kernel}.json`);
      const result = JSON.parse(readFileSync(file, 'utf8'));
      rows.push({ repetition, kernel, scenario, mode, ...result.metrics, gates: result.gates });
      console.log(`[${repetition}/${repetitions}] ${kernel} ${scenario} ${mode}: ${result.metrics.elapsedMs.toFixed(1)} ms`);
    }
  }
}

const numeric = ['elapsedMs', 'syncMs', 'syncBytes', 'historyGcMs', 'stateGcMs',
  'durableStateBytes', 'commitsBeforeFinalGc', 'commitsAfter', 'identityRecords',
  'deletedIds', 'markRecords', 'coordinateSymbols'];
const groups = new Map();
for (const row of rows) {
  const key = `${row.kernel}|${row.scenario}|${row.mode}`;
  if (!groups.has(key)) groups.set(key, []);
  groups.get(key).push(row);
}
const median = (xs) => [...xs].sort((a, b) => a - b)[Math.floor(xs.length / 2)];
const summary = [...groups.entries()].map(([key, xs]) => {
  const [kernel, scenario, mode] = key.split('|');
  const out = { kernel, scenario, mode, repetitions: xs.length };
  for (const field of numeric) {
    const values = xs.map((x) => x[field]).filter(Number.isFinite);
    if (values.length) out[field] = { median: median(values), min: Math.min(...values), max: Math.max(...values) };
  }
  return out;
});
const artifact = { schemaVersion: 1, generatedAt: new Date().toISOString(),
  preset: smoke ? 'freq' : 'bulk', repetitions, design, rows, summary };
const output = join(ROOT, 'results', `peritext-paper-repeated${smoke ? '-smoke' : ''}.json`);
mkdirSync(dirname(output), { recursive: true });
writeFileSync(output, JSON.stringify(artifact, null, 2) + '\n');
console.log(`wrote ${output}`);
