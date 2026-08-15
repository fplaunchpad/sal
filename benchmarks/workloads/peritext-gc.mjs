// Sal Peritext GC ablation over the production DistributedReplica.

import { createHash } from 'node:crypto';
import { mkdirSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { DistributedReplica, syncReplicas } from '../../runtime/src/replica.js';
import { compactiblePeritext, compactibleSharedPeritext } from '../../runtime/src/compact-peritext.js';
import { mulberry32, randChar, loadTrace, flattenOps } from '../lib/traces.mjs';
import { environment, timed } from '../lib/bench.mjs';
import { writeRawResult } from '../lib/result.mjs';

const [mode = 'both', preset = 'freq', scenario = 'concurrent-rich', representation = 'absolute'] = process.argv.slice(2);
const MODES = new Set(['none', 'history', 'text-state', 'full-state', 'both', 'both-delayed']);
if (!MODES.has(mode)) throw new Error(`unknown Peritext GC mode: ${mode}`);
const cfg = preset === 'bulk'
  ? { initial: 500, rounds: 6, burst: 300 }
  : { initial: 200, rounds: 30, burst: 20 };
const seed = 1729, rng = mulberry32(seed);
const stateGc = ['text-state', 'full-state', 'both', 'both-delayed'].includes(mode);
const pairDrop = mode !== 'text-state';
const historyGc = ['history', 'both', 'both-delayed'].includes(mode);
const datatype = representation === 'shared' ? compactibleSharedPeritext : compactiblePeritext;
if (!['absolute', 'shared'].includes(representation)) throw new Error(`unknown representation: ${representation}`);
const a = new DistributedReplica(datatype, 'A');
const b = new DistributedReplica(datatype, 'B');
a.register('B'); b.register('A');
let next = 1, syncMs = 0, syncBytes = 0, historyGcMs = 0;
let intermediateEpochs = 0, intermediateStateGcMs = 0, intermediatePruned = 0;
const knownMarks = { A: [], B: [] };

// The benchmark process is the deterministic timestamp allocator. Operations
// still land on divergent replica heads, but every new id is greater than any
// anchor either replica can have observed.
const alloc = () => next++;
const live = (r) => r.read();
function oneOp(r, who) {
  const doc = live(r), q = rng();
  if (q < 0.45 || doc.length === 0) {
    const pos = Math.floor(rng() * (doc.length + 1));
    r.commit({ type: 'ins', id: alloc(who), el: randChar(rng),
      anchorId: pos === 0 ? null : doc[pos - 1].id });
  } else if (q < 0.65) {
    r.commit({ type: 'del', id: doc[Math.floor(rng() * doc.length)].id });
  } else if (q < 0.90 || knownMarks[who].length === 0) {
    const i = Math.floor(rng() * doc.length), j = Math.floor(rng() * doc.length);
    const lo = Math.min(i, j), hi = Math.max(i, j), mid = alloc(who);
    const mtype = ['bold', 'italic', 'link'][Math.floor(rng() * 3)];
    const m = { mid, mtype, value: mtype === 'link' ? `u${mid % 7}` : null,
      startId: doc[lo].id, endId: doc[hi].id, startSide: 'before', endSide: 'after' };
    knownMarks[who].push(m);
    r.commit({ type: 'addMark', ...m });
  } else {
    const m = knownMarks[who][Math.floor(rng() * knownMarks[who].length)];
    r.commit({ type: 'removeMark', ...m, mid: alloc(who) });
  }
}
function sync() {
  const toB = a.delta(b.ancestryGids()), toA = b.delta(a.ancestryGids());
  syncBytes += Buffer.byteLength(JSON.stringify(toA)) + Buffer.byteLength(JSON.stringify(toB));
  const [, ms] = timed(() => syncReplicas(a, b)); syncMs += ms;
}

function addLinear(r, who, n) {
  let anchorId = live(r).at(-1)?.id ?? null;
  for (let i = 0; i < n; i++) {
    const id = alloc();
    r.commit({ type: 'ins', id, el: randChar(rng), anchorId });
    anchorId = id;
  }
}
function addRandomMark(r, who) {
  const doc = live(r);
  if (doc.length === 0) return;
  const i = Math.floor(rng() * doc.length), j = Math.floor(rng() * doc.length);
  const lo = Math.min(i, j), hi = Math.max(i, j), mid = alloc();
  const mtype = ['bold', 'italic', 'link'][Math.floor(rng() * 3)];
  const m = { mid, mtype, value: mtype === 'link' ? `u${mid % 7}` : null,
    startId: doc[lo].id, endId: doc[hi].id, startSide: 'before', endSide: 'after' };
  knownMarks[who].push(m); r.commit({ type: 'addMark', ...m });
}
function removeKnownMark(r, who) {
  if (knownMarks[who].length === 0) return;
  const m = knownMarks[who][Math.floor(rng() * knownMarks[who].length)];
  r.commit({ type: 'removeMark', ...m, mid: alloc() });
}

function runScenario() {
  if (scenario === 'concurrent-rich') {
    for (let i = 0; i < cfg.initial; i++) oneOp(a, 'A');
    sync();
    for (let round = 0; round < cfg.rounds; round++) {
      for (let k = 0; k < cfg.burst; k++) oneOp(a, 'A');
      for (let k = 0; k < cfg.burst; k++) oneOp(b, 'B');
      sync();
      if (historyGc && !stateGc) for (const r of [a, b]) {
        const [, ms] = timed(() => r.gc()); historyGcMs += ms;
      }
    }
    return;
  }

  addLinear(a, 'A', cfg.initial); sync();
  if (scenario === 'format-trace') {
    const ops = flattenOps(loadTrace('friendsforever_flat'));
    const limit = preset === 'bulk' ? ops.length : Math.min(3000, ops.length);
    const ids = live(a).map((e) => e.id);
    for (let i = 0; i < limit; i++) {
      const op = ops[i];
      if (op.t === 'i') {
        const id = alloc(), pos = Math.min(op.pos, ids.length);
        a.commit({ type: 'ins', id, el: op.ch, anchorId: pos === 0 ? null : ids[pos - 1] });
        ids.splice(pos, 0, id);
      } else if (ids.length) {
        const pos = Math.min(op.pos, ids.length - 1);
        a.commit({ type: 'del', id: ids[pos] }); ids.splice(pos, 1);
      }
      if (i % 200 === 199 && ids.length) addRandomMark(a, 'A');
      if (i % 600 === 599) removeKnownMark(a, 'A');
    }
    sync(); return;
  }
  if (scenario === 'mark-churn') {
    const n = preset === 'bulk' ? 2000 : 400;
    for (let i = 0; i < n; i++) {
      const r = i % 2 ? b : a, who = i % 2 ? 'B' : 'A', doc = live(r);
      const x = Math.floor(rng() * doc.length), y = Math.floor(rng() * doc.length);
      const lo = Math.min(x, y), hi = Math.max(x, y), mid = alloc();
      const m = { mid, mtype: `churn:${i}`, value: null, startId: doc[lo].id,
        endId: doc[hi].id, startSide: 'before', endSide: 'after' };
      knownMarks[who].push(m); r.commit({ type: 'addMark', ...m });
      if (i % 50 === 49) sync();
    }
    sync();
    for (const who of ['A', 'B']) {
      const r = who === 'A' ? a : b;
      for (const m of knownMarks[who]) r.commit({ type: 'removeMark', ...m, mid: alloc() });
    }
    sync(); return;
  }
  if (scenario === 'marked-delete-churn') {
    const marks = preset === 'bulk' ? 800 : 160;
    for (let i = 0; i < marks; i++) addRandomMark(a, 'A');
    sync();
    const ids = live(a).map((e) => e.id);
    for (let i = 0; i < Math.floor(ids.length * 0.8); i++) a.commit({ type: 'del', id: ids[i] });
    for (let i = 0; i < Math.floor(marks / 2); i++) removeKnownMark(a, 'A');
    sync(); return;
  }
  if (scenario === 'offline-rich') {
    const n = preset === 'bulk' ? 2000 : 400;
    for (let i = 0; i < n; i++) oneOp(a, 'A'); // B remains offline
    sync(); return;
  }
  if (scenario === 'empty-rich') {
    // Unique mark types make each add/remove pair independently collectible.
    // This lets the full-state modes exercise the true empty-document floor.
    for (let i = 0; i < 100; i++) {
      const doc = live(a), mid = alloc();
      const m = { mid, mtype: `empty:${i}`, value: null,
        startId: doc[i % doc.length].id, endId: doc[(doc.length - 1 - i) % doc.length].id,
        startSide: 'before', endSide: 'after' };
      knownMarks.A.push(m); a.commit({ type: 'addMark', ...m });
    }
    for (const m of knownMarks.A) a.commit({ type: 'removeMark', ...m, mid: alloc() });
    for (const e of live(a)) a.commit({ type: 'del', id: e.id });
    sync(); b.commit({ type: 'del', id: 1 }); sync(); return;
  }
  if (scenario === 'multi-epoch-rich') {
    for (let cycle = 0; cycle < 3; cycle++) {
      for (let i = 0; i < cfg.burst; i++) oneOp(a, 'A');
      for (let i = 0; i < cfg.burst; i++) oneOp(b, 'B');
      sync();
      // Compact the first two settled cuts here. The common finalization below
      // compacts the third, so this workload crosses three real GC epochs.
      if (stateGc && cycle < 2) {
        b.commit({ type: 'del', id: 0 }); sync();
        const [c, ms] = timed(() => a.compactStable({ pairDrop }));
        intermediateStateGcMs += ms;
        if (!c.compacted) throw new Error(`multi-epoch compaction ${cycle} refused`);
        sync();
        if (historyGc) {
          // Both replicas have acknowledged the compacted cut. Advance them
          // together so later deltas remain ancestor-closed across the epoch.
          const pa = a.pruneToEpochBase(), pb = b.pruneToEpochBase();
          intermediatePruned += pa.pruned + pb.pruned;
        }
        intermediateEpochs++;
      }
    }
    return;
  }
  throw new Error(`unknown Peritext scenario: ${scenario}`);
}

const start = performance.now();
runScenario();
// Give B an authored, state-idempotent checkpoint after it absorbed the final
// workload cut. This is causal frontier evidence, not a benchmarked document
// change. Without it, certified state GC must refuse single-writer scenarios.
b.commit({ type: 'del', id: 0 });
sync();
const renderBefore = JSON.stringify(a.read());
const converged = renderBefore === JSON.stringify(b.read());
const commitsBeforeFinalGc = a.dag.size;
let compact = null, preAck = null, pruned = null, awaitingAck = null;
if (stateGc) {
  const [c, ms] = timed(() => a.compactStable({ pairDrop })); compact = { ...c, ms };
  if (c.compacted) {
    if (mode === 'both-delayed') { preAck = a.pruneToEpochBase(); awaitingAck = a.dag.size; }
    sync();
    if (historyGc) pruned = a.pruneToEpochBase();
  }
}
if (historyGc && !stateGc) {
  const [, ms] = timed(() => a.gc()); historyGcMs += ms;
}
const renderAfter = JSON.stringify(a.read());
const roundTrip = datatype.decodeState(datatype.encodeState(a.head.state));
const snapshotOk = JSON.stringify(datatype.read(roundTrip)) === renderAfter;
const digest = createHash('sha256').update(renderAfter).digest('hex');
const st = a.head.state;
const emptyFloorExpected = scenario === 'empty-rich' && pairDrop && stateGc;
const record = {
  suite: 'peritext', workload: scenario, system: representation === 'shared' ? 'sal-peritext-shared' : 'sal-peritext', mode, preset,
  config: { ...cfg, seed, pairDrop, scenario, representation }, environment: environment(),
  gates: { converged, gcRenderPreserved: renderBefore === renderAfter, snapshotOk,
    stateCompactionFiredOrExpectedNoop: !stateGc || compact?.compacted === true
      || (['mark-churn', 'empty-rich'].includes(scenario) && mode === 'text-state'),
    delayedPruneRefused: mode !== 'both-delayed' || preAck?.pruned === 0,
    emptyMetadataFloor: !emptyFloorExpected || (a.read().length === 0
      && st.text.shadow.size === 0 && st.text.deleted.size === 0 && st.marks.size === 0),
    multiEpochCompaction: scenario !== 'multi-epoch-rich' || !stateGc
      || intermediateEpochs + (compact?.compacted ? 1 : 0) === 3 },
  metrics: { operations: a.seq + b.seq,
    elapsedMs: performance.now() - start, syncMs, syncBytes, historyGcMs,
    stateGcMs: intermediateStateGcMs + (compact?.ms ?? 0),
    intermediateEpochs, intermediatePruned, commitsBeforeFinalGc, commitsAfter: a.dag.size,
    commitsWhileAwaitingAck: awaitingAck, epochPruned: pruned?.pruned ?? 0,
    epochPruneReason: pruned?.reason ?? null,
    durableStateBytes: a.saveBytes(), visibleChars: a.read().length,
    shadowRecords: st.text.shadow.size, deletedIds: st.text.deleted.size,
    markRecords: st.marks.size, coordinateSymbols: a.symbolCount(), renderDigest: digest },
};
const RESULTS = join(dirname(fileURLToPath(import.meta.url)), '..', 'results');
const suffix = representation === 'shared' ? '-shared' : '';
writeRawResult(RESULTS, `peritext-${scenario}-${mode}-${preset}${suffix}.json`, record);
console.log(`peritext ${representation} ${scenario} ${mode}/${preset}: state=${record.metrics.durableStateBytes} B, commits ${commitsBeforeFinalGc} -> ${a.dag.size}, marks=${st.marks.size}`);
if (!Object.values(record.gates).every(Boolean)) process.exit(1);
