// Workload (b): synthetic two-replica concurrent session, deterministic
// seed. Usage: node --expose-gc workloads/concurrent.mjs <system> <preset>
// presets: freq = 60 rounds x 25 ops/replica/round (frequent small merges)
//          bulk = 6 rounds x 500 ops/replica/round  (rare large merges)
//
// Each round: replica A does its burst (80% insert of a random char at a
// uniform random position of ITS OWN doc, 20% delete at a uniform random
// position if non-empty), then B likewise, then one sync (both directions;
// system-native mechanism, see adapters). The rng stream is consumed in a
// fixed order and doc LENGTHS evolve identically across systems, so every
// system sees the byte-identical op sequence. Timed: each sync call; local
// ops timed as one wall-clock total per burst. Gate: textA == textB after
// the final sync (intra-system convergence; cross-system merge ORDER may
// legitimately differ).

import { writeFileSync, mkdirSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { mulberry32, randChar } from '../lib/traces.mjs';
import { getAdapter, byteLength } from '../lib/adapters/index.mjs';
import { gcNow, memSnap, timed, opStats, environment } from '../lib/bench.mjs';
import { writeRawResult } from '../lib/result.mjs';

const [system, preset = 'freq'] = process.argv.slice(2);
if (!system) {
  console.error('usage: node --expose-gc workloads/concurrent.mjs <system> <preset>');
  process.exit(2);
}
const PRESETS = {
  freq: { rounds: 60, burst: 25 },
  bulk: { rounds: 6, burst: 500 },
};
const { rounds, burst } = PRESETS[preset];
const SEED = 42;

const HERE = dirname(fileURLToPath(import.meta.url));
const RESULTS = join(HERE, '..', 'results');
mkdirSync(RESULTS, { recursive: true });

const adapter = await getAdapter(system);
const rng = mulberry32(SEED);

gcNow();
const baseline = memSnap();
let peakHeap = 0;
const sampleHeap = () => {
  const h = process.memoryUsage().heapUsed;
  if (h > peakHeap) peakHeap = h;
};

const p = adapter.pair();
const syncSamplesNs = [];
const payloads = [];
let localOpsTotalMs = 0, localOps = 0;

const doBurst = (ins, del, len) => {
  const [, ms] = timed(() => {
    for (let k = 0; k < burst; k++) {
      const n = len();
      if (rng() < 0.8 || n === 0) {
        ins(Math.floor(rng() * (n + 1)), randChar(rng));
      } else {
        del(Math.floor(rng() * n));
      }
    }
  });
  localOpsTotalMs += ms; localOps += burst;
};

for (let r = 0; r < rounds; r++) {
  doBurst(p.insA, p.delA, p.lenA);
  doBurst(p.insB, p.delB, p.lenB);
  const { ms, payloadBytes } = p.sync();
  syncSamplesNs.push(ms * 1e6);
  if (payloadBytes !== null) payloads.push(payloadBytes);
  sampleHeap();
}

const textA = p.textA(), textB = p.textB();
const converged = textA === textB;
const adapterCost = p.costBreakdown?.() ?? null;

const saves = p.saveVariants().map((v) =>
  v.estimate
    ? { label: v.label, bytes: v.estimate(), estimated: true }
    : { label: v.label, bytes: byteLength(v.mk()), estimated: false });

let compaction = null;
if (p.compactFinal) {
  const { ms, stats, saves } = p.compactFinal();
  compaction = { ms, stats, saves };
}

gcNow();
const end = memSnap();

const syncArr = Float64Array.from(syncSamplesNs);
const result = {
  workload: 'concurrent', system, systemVersion: adapter.version, preset,
  config: { rounds, burst, seed: SEED, insRatio: 0.8 },
  env: environment(),
  finalChars: textA.length,
  gates: { converged },
  sync: { count: rounds, ...opStats(syncArr, 0),
    totalMs: syncSamplesNs.reduce((a, b) => a + b, 0) / 1e6 },
  syncPayloadBytes: payloads.length
    ? { total: payloads.reduce((a, b) => a + b, 0), perSyncMean: payloads.reduce((a, b) => a + b, 0) / payloads.length }
    : null,
  localOps: { count: localOps, totalMs: localOpsTotalMs, meanUs: (localOpsTotalMs * 1e3) / localOps },
  saves, compaction, adapterCost,
  runtimeGcMsTotal: p.gcMsTotal ?? null,
  memory: {
    baselineHeap: baseline.heapUsed,
    peakHeapSampled: peakHeap,
    retainedHeapAfterGc: end.heapUsed - baseline.heapUsed,
    externalDelta: end.external - baseline.external,
    caveat: 'peak sampled once per round without forced GC; wasm memory in external, not heapUsed',
  },
};

writeFileSync(join(RESULTS, `concurrent-${system}-${preset}.json`), JSON.stringify(result, null, 1));
writeRawResult(RESULTS, `concurrent-${system}-${preset}.json`, {
  suite: 'plain-text', workload: 'concurrent', system, preset,
  config: result.config, environment: result.env, gates: { converged },
  metrics: { operations: localOps, finalChars: result.finalChars,
    syncTotalMs: result.sync.totalMs, syncMedianUs: result.sync.medianUs,
    syncP95Us: result.sync.p95Us,
    syncPayloadBytes: result.syncPayloadBytes?.total ?? null,
    localOpMeanUs: result.localOps.meanUs, primarySaveBytes: saves[0]?.bytes ?? null,
    runtimeGcMs: result.runtimeGcMsTotal,
    positionIndexMs: adapterCost?.indexTotalMs ?? null,
    positionIndexRebuildMs: adapterCost?.rebuildTotalMs ?? null,
    datatypeApplyMs: adapterCost?.datatypeTotalMs ?? null },
  detail: result,
});
console.log(`${system} ${preset}: ${rounds} syncs, median ${(result.sync.medianUs / 1e3).toFixed(3)} ms, ` +
  `p95 ${(result.sync.p95Us / 1e3).toFixed(3)} ms, converged=${converged}, finalChars=${textA.length}`);
if (!converged) process.exit(1);
