// Promotion canary for the prefix-sharing EmbedRGA representation.
// Usage: node runtime/benchmarks/shared-gc-canary.mjs [quick|full]

import { performance } from 'node:perf_hooks';
import { DistributedReplica, syncReplicas } from '../src/replica.js';
import { compactibleSharedEmbedRGA } from '../src/shared-compact.js';

const preset = process.argv[2] ?? 'quick';
const cfg = preset === 'full'
  ? { initial: 1000, rounds: 20, burst: 100 }
  : { initial: 200, rounds: 8, burst: 25 };
let seed = 4242;
const rnd = () => (seed = (seed * 1664525 + 1013904223) >>> 0) / 2 ** 32;

function pair() {
  const a = new DistributedReplica(compactibleSharedEmbedRGA, 'A');
  const b = new DistributedReplica(compactibleSharedEmbedRGA, 'B');
  a.register('B'); b.register('A'); return { a, b };
}

function run(scenario) {
  const { a, b } = pair(); let next = 1, gcMs = 0, compactions = 0, pruned = 0;
  const sync = () => syncReplicas(a, b);
  const op = (r) => {
    const ids = compactibleSharedEmbedRGA.readIds(r.head.state);
    if (ids.length === 0 || rnd() < .72) {
      const pos = Math.floor(rnd() * (ids.length + 1)), id = next++;
      r.commit({ type: 'ins', id, anchorId: pos ? ids[pos - 1] : null,
        el: String.fromCharCode(97 + (id % 26)) });
    } else r.commit({ type: 'del', id: ids[Math.floor(rnd() * ids.length)] });
  };
  for (let i = 0; i < cfg.initial; i++) op(a);
  sync();
  const compact = () => {
    b.commit({ type: 'del', id: 0 }); sync();
    const before = JSON.stringify(a.read()), t = performance.now();
    const c = a.compactStable({ fuseSpines: true }); gcMs += performance.now() - t;
    if (!c.compacted) throw new Error(`${scenario}: compaction refused: ${c.reason}`);
    if (JSON.stringify(a.read()) !== before) throw new Error(`${scenario}: compaction changed read`);
    compactions++; sync(); return c;
  };

  if (scenario === 'concurrent') {
    for (let round = 0; round < cfg.rounds; round++) {
      for (let i = 0; i < cfg.burst; i++) op(a);
      for (let i = 0; i < cfg.burst; i++) op(b);
      sync();
    }
    compact();
  } else if (scenario === 'offline') {
    for (let i = 0; i < cfg.rounds * cfg.burst; i++) op(a);
    const refused = a.compactStable({ fuseSpines: true });
    if (refused.compacted || !refused.reason.includes('certificate absent'))
      throw new Error(`${scenario}: GC did not refuse without offline evidence`);
    sync(); compact();
  } else if (scenario === 'multi-epoch') {
    for (let epoch = 0; epoch < 3; epoch++) {
      for (let i = 0; i < cfg.burst; i++) op(a);
      for (let i = 0; i < cfg.burst; i++) op(b);
      // Deterministically create a settled dead spine so every epoch has real
      // state work even if the random edits happen to leave a compact form.
      let parent = compactibleSharedEmbedRGA.readIds(a.head.state).at(-1) ?? null;
      const chain = [];
      for (let i = 0; i < 10; i++) {
        const id = next++; chain.push(id);
        a.commit({ type: 'ins', id, anchorId: parent, el: 'q' }); parent = id;
      }
      for (let i = 0; i < chain.length - 1; i++) a.commit({ type: 'del', id: chain[i] });
      sync(); compact();
      const pa = a.pruneToEpochBase(), pb = b.pruneToEpochBase();
      pruned += pa.pruned + pb.pruned;
    }
  } else throw new Error(`unknown scenario ${scenario}`);

  sync();
  const converged = JSON.stringify(a.read()) === JSON.stringify(b.read());
  const encoded = compactibleSharedEmbedRGA.encodeState(a.head.state);
  const restored = compactibleSharedEmbedRGA.decodeState(encoded);
  const snapshotOk = JSON.stringify(compactibleSharedEmbedRGA.read(restored))
    === JSON.stringify(a.read());
  if (!converged || !snapshotOk) throw new Error(`${scenario}: final semantic gate failed`);
  return { scenario, preset, operations: a.seq + b.seq, visible: a.read().length,
    retainedNodes: compactibleSharedEmbedRGA.nodeCount(a.head.state),
    snapshotBytes: encoded.length, commits: a.dag.size, compactions, pruned,
    gcMs, converged, snapshotOk };
}

for (const scenario of ['concurrent', 'offline', 'multi-epoch'])
  console.log(JSON.stringify(run(scenario)));
