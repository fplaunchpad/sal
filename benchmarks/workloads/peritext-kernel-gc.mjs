// Focused Peritext text-kernel comparison: RGA vs EmbedRGA under identical
// text churn and GC modes. No marks are generated, so this isolates the text
// representation rather than the marks-layer pair collector.

import { mkdirSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { DistributedReplica, syncReplicas } from '../../runtime/src/replica.js';
import { compactibleSharedPeritext } from '../../runtime/src/compact-peritext.js';
import { compactibleSidedPeritext } from '../../runtime/src/compact-peritext.js';
import { compactiblePeritextRGA } from '../../runtime/src/compact-rga-peritext.js';
import { environment } from '../lib/bench.mjs';

const [kernel = 'rga', mode = 'both', preset = 'quick', topology = 'spine'] = process.argv.slice(2);
const datatype = kernel === 'rga' ? compactiblePeritextRGA
  : kernel === 'embed-rga' ? compactibleSharedPeritext
  : kernel === 'sided-embed-rga' ? compactibleSidedPeritext : null;
if (!datatype) throw new Error(`unknown kernel ${kernel}`);
if (!['none', 'history', 'state', 'both'].includes(mode)) throw new Error(`unknown mode ${mode}`);
const cfg = preset === 'stress' ? { initial: 20000, cycles: 5, del: 3500, add: 4500 }
  : preset === 'full' ? { initial: 8000, cycles: 4, del: 1500, add: 1800 }
  : preset === 'quick' ? { initial: 3000, cycles: 3, del: 700, add: 800 }
  : null;
if (!cfg) throw new Error(`unknown preset ${preset}`);
const stateGc = mode === 'state' || mode === 'both', historyGc = mode === 'history' || mode === 'both';
const a = new DistributedReplica(datatype, 'A'), b = new DistributedReplica(datatype, 'B');
a.register('B'); b.register('A');
let next = 1, applyNs = 0n, stateGcMs = 0, historyGcMs = 0, stateCompacted = false;
const commitMany = (ops) => {
  for (let i = 0; i < ops.length; i += 256) {
    const t = process.hrtime.bigint(); a.commitBatch(ops.slice(i, i + 256));
    applyNs += process.hrtime.bigint() - t;
  }
};
const append = (n) => {
  let anchorId = topology === 'spine' ? (a.read().at(-1)?.id ?? null) : null;
  const ops = [];
  for (let i = 0; i < n; i++) {
    const id = next++; ops.push({ type: 'ins', id, anchorId, el: 'a' });
    if (topology === 'spine') anchorId = id;
  }
  commitMany(ops);
};
append(cfg.initial); syncReplicas(a, b);
for (let cycle = 0; cycle < cfg.cycles; cycle++) {
  const ids = a.read().slice(0, cfg.del).map((e) => e.id);
  commitMany(ids.map((id) => ({ type: 'del', id })));
  append(cfg.add); syncReplicas(a, b);
}
// B's authored no-op supplies post-cut frontier evidence for one final,
// directly comparable collection point.
b.commit({ type: 'del', id: 0 }); syncReplicas(a, b);
if (stateGc) {
  const t = performance.now(), c = a.compactStable(); stateGcMs += performance.now() - t;
  if (!c.compacted && !/nothing to compact/.test(c.reason)) throw new Error(`state GC refused: ${c.reason}`);
  stateCompacted = c.compacted;
  syncReplicas(a, b);
}
if (historyGc) {
  const t = performance.now();
  if (stateCompacted) { a.pruneToEpochBase(); b.pruneToEpochBase(); }
  else { a.gc(); b.gc(); }
  historyGcMs += performance.now() - t;
}
const before = JSON.stringify(a.read()); syncReplicas(a, b);
if (before !== JSON.stringify(b.read())) throw new Error('replicas did not converge');
const enc = datatype.encodeState(a.head.state), back = datatype.decodeState(enc);
if (JSON.stringify(datatype.read(back)) !== before) throw new Error('snapshot mismatch');
const result = { schemaVersion: 1, suite: 'peritext-kernel-gc',
  system: `peritext-${kernel}`, workload: `text-kernel-${topology}`, kernel, mode, preset,
  config: { ...cfg, topology },
  environment: environment(),
  metrics: { operations: cfg.initial + cfg.cycles * (cfg.del + cfg.add),
    commitBatches: a.seq + b.seq, visibleChars: a.read().length,
    applyMs: Number(applyNs) / 1e6, stateGcMs, historyGcMs,
    durableStateBytes: Buffer.byteLength(JSON.stringify(enc)), commits: a.dag.size,
    identityRecords: kernel === 'rga' ? a.head.state.text.shadow.adds.size
      : kernel === 'embed-rga' ? a.head.state.text.shadow.size
      : a.head.state.text.shadow.records.size,
    shadowRecords: kernel === 'rga' ? a.head.state.text.shadow.adds.size
      : datatype.symbolCount(a.head.state),
    deletedIds: a.head.state.text.deleted.size },
  gates: { converged: true, snapshot: true } };
const out = join(dirname(fileURLToPath(import.meta.url)), '..', 'results', 'raw',
  `peritext-kernel-${kernel}-${mode}-${preset}-${topology}.json`);
mkdirSync(dirname(out), { recursive: true }); writeFileSync(out, JSON.stringify(result, null, 2) + '\n');
console.log(JSON.stringify(result));
