// Workload (a): sequential replay of a real editing trace, per-char apply.
// Usage: node --expose-gc workloads/seq.mjs <system> <trace>
// Writes results/seq-<system>-<trace>.json
//
// Metrics: per-op apply time (median/p95/p99, warmup excluded), total wall
// time, save size + save time per native variant, load time from the save
// (median of 5), heap (baseline / sampled peak / retained after GC).
// Gate: final text must equal the trace's endContent.

import { writeFileSync, mkdirSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { loadTrace, flattenOps } from '../lib/traces.mjs';
import { getAdapter, byteLength } from '../lib/adapters/index.mjs';
import { gcNow, memSnap, timedLoop, opStats, timed, timedMedian, environment } from '../lib/bench.mjs';

const [system, traceName] = process.argv.slice(2);
if (!system || !traceName) {
  console.error('usage: node --expose-gc workloads/seq.mjs <system> <trace>');
  process.exit(2);
}

const HERE = dirname(fileURLToPath(import.meta.url));
const RESULTS = join(HERE, '..', 'results');
mkdirSync(RESULTS, { recursive: true });

const doc = loadTrace(traceName);
const ops = flattenOps(doc);
const adapter = await getAdapter(system);

gcNow();
const baseline = memSnap();

const d = adapter.create();
const { totalMs, samplesNs, peakHeap } = timedLoop(ops, (op) => {
  if (op.t === 'i') adapter.ins(d, op.pos, op.ch);
  else adapter.del(d, op.pos);
});

const finalText = adapter.text(d);
const textOk = finalText === doc.endContent;

// Document-resident memory: measured HERE, before any save/load/compaction
// allocates large transient artifacts.
gcNow();
const end = memSnap();

// --- saves (each variant timed in isolation) + loads (median of 5)
const saves = [];
for (const v of adapter.saveVariants(d)) {
  if (v.estimate) {
    saves.push({ label: v.label, bytes: v.estimate(), timeMs: null,
      note: v.note ?? null, estimated: true });
  } else {
    const [data, timeMs] = timed(v.mk);
    saves.push({ label: v.label, bytes: byteLength(data), timeMs,
      note: v.note ?? null, estimated: false });
  }
}

const loads = [];
if (adapter.load) {
  const first = adapter.saveVariants(d).find((v) => v.mk);
  const data = first.mk();
  const l = timedMedian(() => adapter.load(data), 5);
  loads.push({ label: first.label, medianMs: l.medianMs, runs: l.runs, allMs: l.allMs });
}

// --- compaction (ours only; single-writer trace end = settled cut)
let compaction = null;
if (adapter.compact) {
  const { ms, stats, compacted } = adapter.compact(d);
  const compSaves = [];
  const { saveJson, binaryEstimate } = await import('../lib/adapters/sal.mjs');
  const [json, jsonMs] = timed(() => saveJson(compacted.state));
  compSaves.push({ label: 'json-shipped+compacted', bytes: byteLength(json), timeMs: jsonMs });
  compSaves.push({ label: 'binary-estimate+compacted',
    bytes: binaryEstimate(compacted.state), timeMs: null, estimated: true });
  const { embedRGA } = await import('../../runtime/src/datatypes/embedRGA.js');
  const compTextOk = embedRGA.read(compacted.state).join('') === doc.endContent;
  compaction = { ms, stats, saves: compSaves, textOk: compTextOk };
}

const result = {
  workload: 'seq', system, systemVersion: adapter.version, trace: traceName,
  env: environment(),
  ops: { total: ops.length, inserts: ops.filter((o) => o.t === 'i').length },
  finalChars: doc.endContent.length,
  apply: { totalMs, ...opStats(samplesNs) },
  gates: { textOk },
  saves, loads, compaction,
  memory: {
    baselineHeap: baseline.heapUsed,
    peakHeapSampled: peakHeap,
    retainedHeapAfterGc: end.heapUsed - baseline.heapUsed,
    externalDelta: end.external - baseline.external,
    arrayBuffersDelta: end.arrayBuffers - baseline.arrayBuffers,
    rssEnd: end.rss,
    caveat: 'peak sampled every 500 ops without forced GC (includes garbage); wasm memory shows in external/arrayBuffers, not heapUsed',
  },
};

const out = join(RESULTS, `seq-${system}-${traceName}.json`);
writeFileSync(out, JSON.stringify(result, null, 1));
console.log(`${system} ${traceName}: ${ops.length} ops in ${totalMs.toFixed(0)} ms ` +
  `(median ${result.apply.medianUs.toFixed(2)} us, p95 ${result.apply.p95Us.toFixed(2)} us), ` +
  `textOk=${textOk}${compaction ? `, compactionOk=${compaction.textOk}` : ''}`);
if (!textOk) process.exit(1);
