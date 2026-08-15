// Workload (c): delete-heavy churn, single writer -- the storage-growth-
// on-delete axis. Usage: node --expose-gc workloads/churn.mjs <system>
//
// 5 cycles of { insert 2000 chars at uniform random positions, delete
// 1800 chars at uniform random positions }, then a final 200-char insert
// phase. After EVERY phase, record each native save variant's byte size
// (and, for ours, the compacted sizes: single writer, so every op is
// settled -- a legitimate cut). The anomaly-matrix cell under test:
// Automerge.save GROWS across a delete phase (history-carrying save);
// ours SHRINKS (delete = pure record removal).

import { writeFileSync, mkdirSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { mulberry32, randChar } from '../lib/traces.mjs';
import { getAdapter, byteLength } from '../lib/adapters/index.mjs';
import { gcNow, memSnap, timed, environment } from '../lib/bench.mjs';
import { writeRawResult } from '../lib/result.mjs';

const [system] = process.argv.slice(2);
if (!system) {
  console.error('usage: node --expose-gc workloads/churn.mjs <system>');
  process.exit(2);
}
const CYCLES = 5, INS = 2000, DEL = 1800, FINAL_INS = 200, SEED = 7;

const HERE = dirname(fileURLToPath(import.meta.url));
const RESULTS = join(HERE, '..', 'results');
mkdirSync(RESULTS, { recursive: true });

const adapter = await getAdapter(system);
const rng = mulberry32(SEED);

gcNow();
const baseline = memSnap();

const d = adapter.create();
let live = 0;
const phases = [];

const record = (phase, phaseMs) => {
  const saves = {};
  for (const v of adapter.saveVariants(d)) {
    saves[v.label] = v.estimate ? v.estimate() : byteLength(v.mk());
  }
  if (adapter.compact) {
    const { compacted } = adapter.compact(d);
    const saved = adapter.saveCompacted(compacted.state);
    saves[saved.label] = byteLength(saved.data);
  }
  phases.push({ phase, liveChars: live, phaseMs, saves });
};

const insertPhase = (n) => {
  const [, ms] = timed(() => {
    for (let k = 0; k < n; k++) {
      adapter.ins(d, Math.floor(rng() * (live + 1)), randChar(rng));
      live++;
    }
  });
  return ms;
};
const deletePhase = (n) => {
  const [, ms] = timed(() => {
    for (let k = 0; k < n; k++) {
      adapter.del(d, Math.floor(rng() * live));
      live--;
    }
  });
  return ms;
};

record('start', 0);
for (let c = 1; c <= CYCLES; c++) {
  record(`cycle${c}-ins`, insertPhase(INS));
  record(`cycle${c}-del`, deletePhase(DEL));
}
record('final-ins', insertPhase(FINAL_INS));

// The anomaly cell: per save variant, does a delete phase ever grow the save?
const growthOnDelete = {};
for (const label of Object.keys(phases[0].saves)) {
  const deltas = [];
  for (let i = 1; i < phases.length; i++) {
    if (phases[i].phase.endsWith('-del')) {
      deltas.push(phases[i].saves[label] - phases[i - 1].saves[label]);
    }
  }
  growthOnDelete[label] = {
    deltasBytes: deltas,
    growsOnDelete: deltas.every((x) => x > 0) ? 'always'
      : deltas.some((x) => x > 0) ? 'sometimes' : 'never',
  };
}

gcNow();
const end = memSnap();

const result = {
  workload: 'churn', system, systemVersion: adapter.version,
  config: { cycles: CYCLES, insPerCycle: INS, delPerCycle: DEL, finalIns: FINAL_INS, seed: SEED },
  env: environment(),
  finalChars: live,
  gates: { lenOk: adapter.text(d).length === live },
  phases, growthOnDelete,
  memory: {
    baselineHeap: baseline.heapUsed,
    retainedHeapAfterGc: end.heapUsed - baseline.heapUsed,
    externalDelta: end.external - baseline.external,
  },
};

writeFileSync(join(RESULTS, `churn-${system}.json`), JSON.stringify(result, null, 1));
writeRawResult(RESULTS, `churn-${system}.json`, {
  suite: 'plain-text', workload: 'delete-churn', system,
  config: result.config, environment: result.env, gates: result.gates,
  metrics: { operations: CYCLES * (INS + DEL) + FINAL_INS, finalChars: live,
    finalPrimarySaveBytes: phases.at(-1).saves[Object.keys(phases.at(-1).saves)[0]],
    retainedHeapBytes: result.memory.retainedHeapAfterGc },
  detail: result,
});
const summary = Object.entries(growthOnDelete)
  .map(([l, g]) => `${l}: ${g.growsOnDelete}`).join('; ');
console.log(`${system} churn: final ${live} chars, growth-on-delete { ${summary} }`);
