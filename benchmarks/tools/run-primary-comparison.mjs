// Repeated paper-facing comparison against production sequence libraries.
// Runs each cell in a fresh process and publishes both raw observations and a
// compact Markdown table. Overall workload time is primary; Sal's nested
// adapter timings are diagnostics only.

import { spawnSync } from 'node:child_process';
import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const HERE = dirname(fileURLToPath(import.meta.url)), ROOT = join(HERE, '..');
const RESULTS = join(ROOT, 'results'), reps = Number(process.argv[2] ?? 3);
const systems = ['rga', 'embed-rga', 'sided-embed-rga', 'yjs', 'automerge', 'loro', 'listpositions'];
const traces = ['friendsforever_flat', 'clownschool_flat', 'seph-blog1', 'automerge-paper'];
const presets = ['freq', 'bulk'];
if (!Number.isInteger(reps) || reps < 1) throw new Error('repetitions must be a positive integer');

const run = (args) => {
  const r = spawnSync(process.execPath, ['--expose-gc', ...args], { cwd: ROOT, encoding: 'utf8' });
  if (r.status !== 0) throw new Error(`${args.join(' ')} failed:\n${r.stdout}\n${r.stderr}`);
};
const rows = [];
let environment = null;
for (let repetition = 1; repetition <= reps; repetition++) {
  for (const trace of traces) for (const system of systems) {
    run([join(ROOT, 'workloads', 'seq.mjs'), system, trace]);
    const x = JSON.parse(readFileSync(join(RESULTS, `seq-${system}-${trace}.json`)));
    environment ??= x.env;
    rows.push({ repetition, suite: 'sequence', system, workload: trace,
      operations: x.ops.total, finalChars: x.finalChars, applyMs: x.apply.totalMs,
      medianUs: x.apply.medianUs, p95Us: x.apply.p95Us,
      saveBytes: x.saves[0]?.bytes ?? null, loadMs: x.loads[0]?.medianMs ?? null,
      positionIndexMs: x.adapterCost?.indexTotalMs ?? null,
      datatypeApplyMs: x.adapterCost?.datatypeTotalMs ?? null,
      gates: x.gates });
  }
  for (const preset of presets) for (const system of systems) {
    run([join(ROOT, 'workloads', 'concurrent.mjs'), system, preset]);
    const x = JSON.parse(readFileSync(join(RESULTS, `concurrent-${system}-${preset}.json`)));
    rows.push({ repetition, suite: 'concurrent', system, workload: preset,
      operations: x.localOps.count, finalChars: x.finalChars,
      syncMedianUs: x.sync.medianUs, syncP95Us: x.sync.p95Us,
      syncTotalMs: x.sync.totalMs, localOpMeanUs: x.localOps.meanUs,
      payloadBytes: x.syncPayloadBytes?.total ?? null, saveBytes: x.saves[0]?.bytes ?? null,
      positionIndexMs: x.adapterCost?.indexTotalMs ?? null,
      positionIndexRebuildMs: x.adapterCost?.rebuildTotalMs ?? null,
      datatypeApplyMs: x.adapterCost?.datatypeTotalMs ?? null,
      gates: x.gates });
  }
  console.log(`primary comparison repetition ${repetition}/${reps} passed`);
}

const numeric = ['operations', 'finalChars', 'applyMs', 'medianUs', 'p95Us',
  'saveBytes', 'loadMs', 'syncMedianUs', 'syncP95Us', 'syncTotalMs',
  'localOpMeanUs', 'payloadBytes', 'positionIndexMs', 'positionIndexRebuildMs',
  'datatypeApplyMs'];
const groups = new Map();
for (const row of rows) {
  const key = `${row.suite}|${row.system}|${row.workload}`;
  if (!groups.has(key)) groups.set(key, []);
  groups.get(key).push(row);
}
const median = (xs) => [...xs].sort((a, b) => a - b)[Math.floor(xs.length / 2)];
const summary = [...groups.entries()].map(([key, xs]) => {
  const [suite, system, workload] = key.split('|');
  const out = { suite, system, workload, repetitions: xs.length };
  for (const field of numeric) {
    const vs = xs.map((x) => x[field]).filter(Number.isFinite);
    if (vs.length) out[field] = { median: median(vs), min: Math.min(...vs), max: Math.max(...vs) };
  }
  return out;
});
const artifact = { schemaVersion: 1, generatedAt: new Date().toISOString(), environment,
  repetitions: reps, systems, traces, presets, rows, summary };
writeFileSync(join(RESULTS, 'primary-comparison-repeated.json'), JSON.stringify(artifact, null, 2) + '\n');

const label = new Map([['rga', 'Sal RGA'], ['embed-rga', 'Sal EmbedRGA'],
  ['sided-embed-rga', 'Sal SidedEmbedRGA'], ['listpositions', 'list-positions']]);
const fmt = (x, unit) => x ? `${x.median.toFixed(2)} ${unit} [${x.min.toFixed(2)}, ${x.max.toFixed(2)}]` : 'n/a';
const md = ['# Repeated primary comparison', '',
  `Generated ${artifact.generatedAt}; ${reps} fresh-process repetitions per cell. Values are median [min, max].`, '',
  'Overall workload timings include adapter work. Sal index/datatype nested timers are diagnostics and add timer overhead.', ''];
for (const trace of traces) {
  md.push(`## Sequential: ${trace}`, '', '| system | total | apply median | p95 | save | recovery |',
    '| --- | ---: | ---: | ---: | ---: | ---: |');
  for (const system of systems) {
    const x = summary.find((r) => r.suite === 'sequence' && r.system === system && r.workload === trace);
    md.push(`| ${label.get(system) ?? system} | ${fmt(x.applyMs, 'ms')} | ${fmt(x.medianUs, 'us')} | ${fmt(x.p95Us, 'us')} | ${fmt(x.saveBytes, 'B')} | ${fmt(x.loadMs, 'ms')} |`);
  }
  md.push('');
}
for (const preset of presets) {
  md.push(`## Concurrent: ${preset}`, '', '| system | sync median | sync p95 | sync total | local op mean | save |',
    '| --- | ---: | ---: | ---: | ---: | ---: |');
  for (const system of systems) {
    const x = summary.find((r) => r.suite === 'concurrent' && r.system === system && r.workload === preset);
    md.push(`| ${label.get(system) ?? system} | ${fmt(x.syncMedianUs, 'us')} | ${fmt(x.syncP95Us, 'us')} | ${fmt(x.syncTotalMs, 'ms')} | ${fmt(x.localOpMeanUs, 'us')} | ${fmt(x.saveBytes, 'B')} |`);
  }
  md.push('');
}
writeFileSync(join(RESULTS, 'primary-comparison-repeated.md'), md.join('\n') + '\n');
console.log(`wrote repeated primary JSON and Markdown (${rows.length} observations)`);
