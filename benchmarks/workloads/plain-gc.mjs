// Sal plain-text GC ablation over the production DistributedReplica.
// Usage: node --expose-gc plain-gc.mjs <none|history|state|both|both-delayed> <freq|bulk>

import { mkdirSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { DistributedReplica, syncReplicas } from '../../runtime/src/replica.js';
import { compactibleEmbedRGA } from '../../runtime/src/compact.js';
import { compactibleSharedEmbedRGA } from '../../runtime/src/shared-compact.js';
import { mulberry32, randChar } from '../lib/traces.mjs';
import { environment, timed } from '../lib/bench.mjs';

const [mode = 'both', preset = 'freq', representation = 'absolute'] = process.argv.slice(2);
const MODES = new Set(['none', 'history', 'state', 'both', 'both-delayed']);
if (!MODES.has(mode)) throw new Error(`unknown GC mode: ${mode}`);
const cfg = preset === 'bulk' ? { rounds: 6, burst: 500 } : { rounds: 60, burst: 25 };
const seed = 42, rng = mulberry32(seed);
const stateGc = mode === 'state' || mode.startsWith('both');
const historyGc = mode === 'history' || mode.startsWith('both');
const datatype = representation === 'shared' ? compactibleSharedEmbedRGA : compactibleEmbedRGA;
if (!['absolute', 'shared'].includes(representation)) throw new Error(`unknown representation: ${representation}`);
const a = new DistributedReplica(datatype, 'A');
const b = new DistributedReplica(datatype, 'B');
a.register('B'); b.register('A');
let next = 1, historyGcMs = 0, historyDropped = 0, syncMs = 0;

function burst(r) {
  for (let k = 0; k < cfg.burst; k++) {
    const ids = datatype.readIds(r.head.state);
    if (rng() < 0.8 || ids.length === 0) {
      const pos = Math.floor(rng() * (ids.length + 1));
      r.commit({ type: 'ins', id: next++, el: randChar(rng), anchorId: pos === 0 ? null : ids[pos - 1] });
    } else {
      r.commit({ type: 'del', id: ids[Math.floor(rng() * ids.length)] });
    }
  }
}

const start = performance.now();
for (let round = 0; round < cfg.rounds; round++) {
  burst(a); burst(b);
  const [, ms] = timed(() => syncReplicas(a, b)); syncMs += ms;
  // When both collectors are enabled, state GC consumes the causal ancestry
  // first. Pruning that ancestry earlier weakens its stable-cut evidence.
  // History-only mode may collect incrementally; the production both-GC mode
  // compacts state at the final settled cut, receives the peer receipt, then
  // prunes history to the epoch base.
  if (historyGc && !stateGc) {
    for (const r of [a, b]) {
      const [g, gcMs] = timed(() => r.gc());
      historyGcMs += gcMs; historyDropped += g.dropped;
    }
  }
}

const converged = a.read().join('') === b.read().join('');
const commitsBeforeFinalGc = a.dag.size;
let stateCompaction = null, pruneBeforeAck = null, epochPrune = null;
let commitsWhileAwaitingAck = null;
if (stateGc) {
  const [c, ms] = timed(() => a.compactStable({ fuseSpines: true }));
  stateCompaction = { ...c, ms };
  if (c.compacted) {
    if (mode === 'both-delayed') {
      pruneBeforeAck = { ...a.pruneToEpochBase(), delayedRounds: 10 };
      commitsWhileAwaitingAck = a.dag.size;
    }
    syncReplicas(a, b);
    if (historyGc) epochPrune = a.pruneToEpochBase();
  }
}
if (historyGc && !stateGc) {
  const [g, ms] = timed(() => a.gc());
  historyGcMs += ms; historyDropped += g.dropped;
}

const result = {
  schemaVersion: 1,
  suite: 'plain-text', workload: 'concurrent-gc-ablation', system: representation === 'shared' ? 'sal-shared' : 'sal', mode, preset,
  config: { ...cfg, seed, representation, acknowledgementDelayRounds: mode === 'both-delayed' ? 10 : 0 },
  environment: environment(),
  gates: { converged, stateCompactionFired: !stateGc || stateCompaction?.compacted === true,
    delayedPruneRefused: mode !== 'both-delayed' || pruneBeforeAck?.pruned === 0 },
  metrics: {
    operations: 2 * cfg.rounds * cfg.burst,
    elapsedMs: performance.now() - start,
    syncMs, historyGcMs, historyDropped,
    commitsBeforeFinalGc, commitsAfter: a.dag.size,
    durableStateBytes: a.saveBytes(), visibleChars: a.read().length,
    coordinateSymbols: a.symbolCount(), stateGcMs: stateCompaction?.ms ?? 0,
    epochPruned: epochPrune?.pruned ?? 0, commitsWhileAwaitingAck,
  },
};
const out = join(dirname(fileURLToPath(import.meta.url)), '..', 'results', 'raw');
mkdirSync(out, { recursive: true });
const suffix = representation === 'shared' ? '-shared' : '';
writeFileSync(join(out, `plain-gc-${mode}-${preset}${suffix}.json`), JSON.stringify(result, null, 2));
console.log(`plain-gc ${representation} ${mode}/${preset}: commits ${commitsBeforeFinalGc} -> ${a.dag.size}, state=${a.saveBytes()} B, converged=${converged}`);
if (!Object.values(result.gates).every(Boolean)) process.exit(1);
