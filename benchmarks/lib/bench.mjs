// Shared measurement helpers: per-op timing, robust stats, heap sampling.
//
// METHODOLOGY NOTES (stated once, referenced by README):
// * Per-op timing uses process.hrtime.bigint() around each op. Timer
//   overhead is ~30-60 ns/op on this machine; sub-microsecond medians
//   (Yjs, Loro) carry that additive bias. Totals are wall-clock over the
//   whole loop (one hrtime pair), so they do not accumulate the per-op
//   timer cost beyond the calls themselves.
// * Warmup: the first WARMUP ops are excluded from median/p95/p99 (JIT,
//   wasm lazy init). Totals INCLUDE warmup ops (stated in README).
// * Heap: workers run under --expose-gc. baseline = heapUsed after two
//   forced GCs before the loop; peak = max heapUsed sampled every
//   SAMPLE_EVERY ops WITHOUT forcing GC (so it includes garbage - a
//   documented caveat); retained = heapUsed after two forced GCs at the
//   end, minus baseline. external/arrayBuffers deltas are recorded too:
//   for wasm-backed libraries (automerge, loro) most state lives outside
//   the JS heap.

import { cpus, totalmem } from 'node:os';

export const WARMUP = 1000;
export const SAMPLE_EVERY = 500;

export function gcNow() {
  if (typeof globalThis.gc === 'function') { globalThis.gc(); globalThis.gc(); }
}

export function memSnap() {
  const m = process.memoryUsage();
  return { heapUsed: m.heapUsed, external: m.external, arrayBuffers: m.arrayBuffers, rss: m.rss };
}

/** Run fn(op, i) over ops; returns {totalMs, samplesNs, peakHeap}. */
export function timedLoop(ops, fn) {
  const n = ops.length;
  const samples = new Float64Array(n);
  let peakHeap = 0;
  const t0 = process.hrtime.bigint();
  for (let i = 0; i < n; i++) {
    const a = process.hrtime.bigint();
    fn(ops[i], i);
    const b = process.hrtime.bigint();
    samples[i] = Number(b - a);
    if (i % SAMPLE_EVERY === 0) {
      const h = process.memoryUsage().heapUsed;
      if (h > peakHeap) peakHeap = h;
    }
  }
  const t1 = process.hrtime.bigint();
  const h = process.memoryUsage().heapUsed;
  if (h > peakHeap) peakHeap = h;
  return { totalMs: Number(t1 - t0) / 1e6, samplesNs: samples, peakHeap };
}

export function quantile(sorted, q) {
  if (sorted.length === 0) return NaN;
  const idx = Math.min(sorted.length - 1, Math.floor(q * sorted.length));
  return sorted[idx];
}

/** Stats in microseconds over samples[warmup:]. */
export function opStats(samplesNs, warmup = WARMUP) {
  const body = samplesNs.slice(Math.min(warmup, Math.floor(samplesNs.length / 2)));
  const sorted = Float64Array.from(body).sort();
  let sum = 0;
  for (const v of body) sum += v;
  return {
    count: samplesNs.length,
    warmupExcluded: samplesNs.length - body.length,
    meanUs: sum / body.length / 1e3,
    medianUs: quantile(sorted, 0.5) / 1e3,
    p95Us: quantile(sorted, 0.95) / 1e3,
    p99Us: quantile(sorted, 0.99) / 1e3,
    maxUs: sorted[sorted.length - 1] / 1e3,
  };
}

/** Time one call; returns [result, ms]. */
export function timed(fn) {
  const a = process.hrtime.bigint();
  const r = fn();
  const b = process.hrtime.bigint();
  return [r, Number(b - a) / 1e6];
}

/** Median of k timed runs of fn (fresh work each run); returns {medianMs, runs}. */
export function timedMedian(fn, k = 5) {
  const times = [];
  for (let i = 0; i < k; i++) times.push(timed(fn)[1]);
  times.sort((x, y) => x - y);
  return { medianMs: times[Math.floor(times.length / 2)], runs: k, allMs: times };
}

export function environment() {
  return {
    node: process.version,
    platform: `${process.platform} ${process.arch}`,
    cpu: cpus()[0]?.model ?? 'unknown',
    logicalCpus: cpus().length,
    memoryBytes: totalmem(),
    exposeGc: typeof globalThis.gc === 'function',
    date: new Date().toISOString(),
  };
}
