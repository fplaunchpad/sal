// Repeated paper-facing comparison of the three proved sequence kernels plus
// the focused Peritext RGA/EmbedRGA GC question.

import { spawnSync } from 'node:child_process';
import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const HERE = dirname(fileURLToPath(import.meta.url)), ROOT = join(HERE, '..');
const RESULTS = join(ROOT, 'results'), reps = Number(process.argv[2] ?? 3);
const systems = ['rga', 'embed-rga', 'sided-embed-rga'];
const traces = ['friendsforever_flat', 'clownschool_flat', 'seph-blog1', 'automerge-paper'];
const rows = [];
const run = (args) => {
  const r = spawnSync(process.execPath, ['--expose-gc', ...args], { cwd: ROOT, encoding: 'utf8' });
  if (r.status !== 0) throw new Error(`${args.join(' ')} failed:\n${r.stdout}\n${r.stderr}`);
};

for (let rep = 1; rep <= reps; rep++) {
  for (const system of systems) for (const trace of traces) {
    run([join(ROOT, 'workloads', 'seq.mjs'), system, trace]);
    const x = JSON.parse(readFileSync(join(RESULTS, `seq-${system}-${trace}.json`)));
    rows.push({ rep, suite: 'sequence', system, workload: trace,
      applyMs: x.apply.totalMs, medianUs: x.apply.medianUs, p95Us: x.apply.p95Us,
      saveBytes: x.saves[0].bytes, loadMs: x.loads[0]?.medianMs ?? null, textOk: x.gates.textOk });
  }
  for (const system of systems) for (const preset of ['freq', 'bulk']) {
    run([join(ROOT, 'workloads', 'concurrent.mjs'), system, preset]);
    const x = JSON.parse(readFileSync(join(RESULTS, `concurrent-${system}-${preset}.json`)));
    rows.push({ rep, suite: 'concurrent', system, workload: preset,
      syncMedianUs: x.sync.medianUs, syncP95Us: x.sync.p95Us,
      saveBytes: x.saves[0].bytes, converged: x.gates.converged });
  }
  for (const kernel of ['rga', 'embed-rga', 'sided-embed-rga']) for (const mode of ['none', 'both']) {
    run([join(ROOT, 'workloads', 'peritext-kernel-gc.mjs'), kernel, mode, 'full', 'spine']);
    const x = JSON.parse(readFileSync(join(RESULTS, 'raw',
      `peritext-kernel-${kernel}-${mode}-full-spine.json`)));
    rows.push({ rep, suite: 'peritext-kernel', system: kernel, workload: `spine-${mode}`,
      ...x.metrics, gates: x.gates });
  }
  console.log(`kernel comparison repetition ${rep}/${reps} passed`);
}

const values = (xs, key) => xs.map((x) => x[key]).filter(Number.isFinite).sort((a, b) => a - b);
const median = (xs) => xs.length ? xs[Math.floor(xs.length / 2)] : null;
const groups = new Map();
for (const row of rows) {
  const key = `${row.suite}|${row.system}|${row.workload}`;
  if (!groups.has(key)) groups.set(key, []); groups.get(key).push(row);
}
const summary = [...groups.entries()].map(([key, xs]) => {
  const [suite, system, workload] = key.split('|'), out = { suite, system, workload, repetitions: xs.length };
  for (const field of ['applyMs', 'medianUs', 'p95Us', 'saveBytes', 'loadMs',
    'syncMedianUs', 'syncP95Us', 'durableStateBytes', 'stateGcMs', 'historyGcMs',
    'shadowRecords', 'identityRecords', 'deletedIds', 'commits']) {
    const vs = values(xs, field); if (vs.length) out[field] = { median: median(vs), min: vs[0], max: vs.at(-1) };
  }
  return out;
});
const artifact = { generatedAt: new Date().toISOString(), repetitions: reps, rows, summary };
writeFileSync(join(RESULTS, 'kernel-comparison-repeated.json'), JSON.stringify(artifact, null, 2) + '\n');
console.log(`wrote ${join(RESULTS, 'kernel-comparison-repeated.json')}`);
