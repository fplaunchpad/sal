// THE GC-SAFETY PBT.
//
// Twin execution: the same random head-sync run (3-5 replicas, random
// commit/sync interleavings, tens of steps) is replayed on two identical
// runtimes; on the SECOND twin gc() is invoked aggressively at random
// points. Empirical statement of gc_safety: at every step every replica
// reads identically on both twins, and after the final sync passes the
// per-replica head states are identical. Any wrong-LCA merge after pruning
// (the thing the keep-set must prevent) shows up as a read divergence, a
// resurrected delete, a criss-cross-verdict flip, or a thrown error.
//
// Criss-cross: it genuinely arises under honest head-sync (two disjoint
// replica pairs merge the same diverged heads x,y into rival merge
// commits; any later sync across them has MCAs {x,y}). The runtime GATES
// such merges (CrissCrossError, task #90), so the PBT skips them, like
// pbt.py's "skipped illegal merges" -- but BOTH twins must return the same
// verdict: the criss-cross decision is computed from the (possibly pruned)
// DAG, so twin agreement on it is part of gc-safety and is asserted.
// A consequence of the gate: full convergence is not always reachable, so
// the LIVE oracle checks each replica's read against the implicit event
// set of its OWN head (dag.events), not a single converged head.
//
// Ops are generated from the gc'd twin's OWN current read (honest clients),
// after asserting it equals the control twin's read.

import test from 'node:test';
import assert from 'node:assert/strict';
import { Runtime } from '../src/runtime.js';
import { CrissCrossError } from '../src/lca.js';
import { embedRGA } from '../src/datatypes/embedRGA.js';
import { orset } from '../src/datatypes/orset.js';

function mulberry32(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
const pick = (rng, xs) => xs[Math.floor(rng() * xs.length)];
// canonical multiset form: sorted, duplicates preserved (a DUP still fails)
const canon = (xs) => [...xs].map((x) => JSON.stringify(x)).sort();

const P = { pSync: 0.35, pDel: 0.3, pGc: 0.35 };

function runTrial(DT, genOp, liveOracle, seed) {
  const rng = mulberry32(seed);
  const nRep = 3 + (seed % 3);                 // 3..5 replicas
  const nSteps = 25 + Math.floor(rng() * 26);  // 25..50 steps
  const twins = [new Runtime(DT), new Runtime(DT)];
  const reps = twins.map((rt) =>
    Array.from({ length: nRep }, (_, i) => rt.replica('r' + i)));
  const mint = { next: 1 };
  const stats = { dropped: 0, gcs: 0, syncs: 0, skipped: 0 };

  // sync on both twins; the criss-cross verdict must agree (gc-safety!)
  const doSync = (r, j) => {
    const attempt = (t) => {
      try { reps[t][r].sync(reps[t][j]); return null; }
      catch (e) { if (e instanceof CrissCrossError) return e; throw e; }
    };
    const e0 = attempt(0);
    const e1 = attempt(1);
    assert.equal(e0 === null, e1 === null,
      `twins disagree on the criss-cross verdict for r${r}~r${j}`);
    if (e0) stats.skipped++; else stats.syncs++;
  };

  for (let step = 0; step < nSteps; step++) {
    const r = Math.floor(rng() * nRep);
    if (rng() < P.pSync) {
      const j = Math.floor(rng() * nRep);
      if (j !== r) doSync(r, j);
    } else {
      // twin agreement FIRST, then generate the op from the gc'd twin's read
      assert.deepEqual(reps[1][r].read(), reps[0][r].read(), `pre-op read @${step} r${r}`);
      const op = genOp(rng, reps[1][r], mint);
      reps[0][r].commit(op);
      reps[1][r].commit(op);
    }
    if (rng() < P.pGc) { stats.dropped += twins[1].gc().dropped; stats.gcs++; }
    for (let i = 0; i < nRep; i++) {
      assert.deepEqual(reps[1][i].read(), reps[0][i].read(), `read @${step} r${i}`);
    }
  }

  // drive both twins toward convergence (criss-cross pairs stay gated)
  for (let pass = 0; pass < 3; pass++) {
    for (let i = 0; i < nRep; i++) {
      for (let j = i + 1; j < nRep; j++) doSync(i, j);
    }
  }
  for (let i = 0; i < nRep; i++) {
    assert.deepEqual(reps[1][i].read(), reps[0][i].read(), 'final read');
    assert.equal(DT.fingerprint(reps[1][i].head.state),
                 DT.fingerprint(reps[0][i].head.state), 'final state');
    // LIVE oracle: replica i's read = fold of its head's implicit event set
    // (computed on the control twin; the gc'd twin's history is truncated)
    const evs = twins[0].dag.events(reps[0][i].head.id).map((o) => o.payload);
    assert.deepEqual(canon(reps[0][i].read()), canon(liveOracle(evs)), `LIVE oracle r${i}`);
  }
  return stats;
}

// --- embedRGA generator + oracle (element = its own id) ---
const genEmbedOp = (rng, replica, mint) => {
  const doc = replica.read();
  if (doc.length > 0 && rng() < P.pDel) return { type: 'del', id: pick(rng, doc) };
  const id = mint.next++;
  const anchorId = doc.length > 0 && rng() < 0.6 ? pick(rng, doc) : null;
  return { type: 'ins', id, el: id, anchorId };
};
const embedOracle = (evs) => {
  const del = new Set(evs.filter((p) => p.type === 'del').map((p) => p.id));
  return evs.filter((p) => p.type === 'ins' && !del.has(p.id)).map((p) => p.id);
};

// --- orset generator + oracle ---
const genOrsetOp = (rng, replica, mint) => {
  const doc = replica.read();
  if (doc.length > 0 && rng() < P.pDel) {
    const el = pick(rng, doc);
    return { type: 'rm', tags: orset.observe(replica.head.state, el) };
  }
  return { type: 'add', tag: 't' + mint.next++, el: 'e' + Math.floor(rng() * 8) };
};
const orsetOracle = (evs) => {
  const killed = new Set(evs.flatMap((p) => (p.type === 'rm' ? p.tags : [])));
  const els = evs.filter((p) => p.type === 'add' && !killed.has(p.tag)).map((p) => p.el);
  return [...new Set(els)].sort();
};

test('GC-safety PBT: embedRGA, 220 twin trials', (t) => {
  const tot = { dropped: 0, gcs: 0, syncs: 0, skipped: 0 };
  for (let seed = 0; seed < 220; seed++) {
    const s = runTrial(embedRGA, genEmbedOp, embedOracle, seed * 100003 + 17);
    for (const k of Object.keys(tot)) tot[k] += s[k];
  }
  t.diagnostic(`embedRGA: ${JSON.stringify(tot)}`);
  assert.ok(tot.dropped > 1000, `gc must actually bite (dropped ${tot.dropped})`);
  assert.ok(tot.skipped > 0, 'expected some criss-cross-gated syncs across 220 trials');
});

test('GC-safety PBT: orset, 120 twin trials (pluggability)', (t) => {
  const tot = { dropped: 0, gcs: 0, syncs: 0, skipped: 0 };
  for (let seed = 0; seed < 120; seed++) {
    const s = runTrial(orset, genOrsetOp, orsetOracle, seed * 7919 + 3);
    for (const k of Object.keys(tot)) tot[k] += s[k];
  }
  t.diagnostic(`orset: ${JSON.stringify(tot)}`);
  assert.ok(tot.dropped > 500, `gc must actually bite (dropped ${tot.dropped})`);
});
