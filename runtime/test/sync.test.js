// The runtime sync/gossip layer: the delta/op WIRE protocol (src/sync.js) and
// the EVIDENCE-CERTIFICATE producer (frontier -> stableCut -> certified
// compaction, src/frontier.js + Replica.compactStable). One subsystem: the
// evidence frontier is fed by wire arrivals.
//
// (3a) delta-sync convergence + bounded payload   -- the wire, N peers, gossip
// (3b) evidence correctness (refuse-then-fire)     -- the discriminating remove
// (3c) twin PBT: certified GC vs no-GC control     -- both branches exercised

import test from 'node:test';
import assert from 'node:assert/strict';
import { Runtime } from '../src/runtime.js';
import { CrissCrossError } from '../src/lca.js';
import { compactibleEmbedRGA } from '../src/compact.js';
import { embedRGA } from '../src/datatypes/embedRGA.js';
import {
  Peer, syncPeers, deltaOrSnapshot, encodeWire, decodeWire,
  wireBytes, jsonWireBytes,
} from '../src/sync.js';

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

// -------------------------------------------------------------- (3a) the wire
test('binary delta codec is deterministic, lossless, compact, and rejects damage', () => {
  const A = new Peer(embedRGA, 'replica-with-a-long-name');
  for (let id = 1; id <= 80; id++) A.commit({
    type: 'ins', id, el: String.fromCharCode(96 + (id % 26 || 26)), anchorId: id === 1 ? null : id - 1,
  });
  const message = { t: 'delta', c: A.delta(new Set()) };
  const a = encodeWire(message), b = encodeWire(message);
  assert.deepEqual(a, b, 'canonical input has deterministic bytes');
  const decoded = decodeWire(a);
  assert.equal(decoded.c.length, message.c.length, 'binary wire preserves the complete commit run');
  assert.equal(decoded.c.at(-1).gid, message.c.at(-1).gid, 'run endpoint authenticates the run');
  assert.ok(decoded.c.slice(0, -1).some((c) => c.gid === null), 'linear intermediate ids are implicit');
  const B = new Peer(embedRGA, 'B'); B.ingest(decoded.c);
  assert.equal(B.byGid.has(message.c.at(-1).gid), true, 'ingest reconstructs and validates the endpoint');
  const tampered = decodeWire(a);
  tampered.c[0].payload.el = 'tampered';
  const C = new Peer(embedRGA, 'C');
  assert.throws(() => C.ingest(tampered.c), /content-address mismatch/,
    'the explicit run endpoint authenticates every implicit intermediate commit');
  assert.equal(wireBytes(message), a.length);
  assert.ok(a.length < jsonWireBytes(message) * 0.55,
    `binary ${a.length} must materially beat JSON ${jsonWireBytes(message)}`);
  assert.throws(() => decodeWire(a.subarray(0, a.length - 1)), /truncated/);
  const bad = a.slice(); bad[0] ^= 1;
  assert.throws(() => decodeWire(bad), /bad magic/);
});

test('delta-sync convergence: N peers gossip over the wire, converge to equal reads', (t) => {
  const N = 4, ROUNDS = 50, BURST = 5;
  const rng = mulberry32(0xC0FFEE);
  const peers = Array.from({ length: N }, (_, i) => new Peer(embedRGA, 'p' + i));
  let mint = 0, crisses = 0;
  const perRoundDelta = [], perRoundBase = [];
  for (let round = 0; round < ROUNDS; round++) {
    for (let i = 0; i < N; i++) {
      for (let k = 0; k < BURST; k++) {
        const view = embedRGA.readIds(peers[i].head.state);
        if (view.length > 3 && rng() < 0.25) { peers[i].commit({ type: 'del', id: pick(rng, view) }); continue; }
        const id = ++mint; // global Lamport tick: strictly increasing, so id > any live anchor
        const anchorId = view.length && rng() < 0.7 ? pick(rng, view) : null;
        peers[i].commit({ type: 'ins', id, el: String.fromCharCode(97 + (id % 26)), anchorId });
      }
    }
    // criss-cross-free gossip: linear fold into peer0, then broadcast back
    let rd = 0, rb = 0;
    for (let pass = 0; pass < 2; pass++) {
      for (let k = 1; k < N; k++) {
        const r = syncPeers(peers[0], peers[k]);
        rd += r.bytes; rb += r.baseline; if (!r.merged) crisses++;
      }
    }
    perRoundDelta.push(rd); perRoundBase.push(rb);
    const reads = peers.map((p) => p.read().join(''));
    for (let i = 1; i < N; i++) assert.equal(reads[i], reads[0], `round ${round}: p${i} diverged`);
  }
  assert.equal(crisses, 0, 'linear-fold gossip must be criss-cross-free');
  // payload bounded by the DELTA, not whole state: the per-round delta is a
  // function of that round's ops (constant across rounds), while a whole-state
  // resync grows with the document. In steady state (second half, big doc) the
  // delta is well below the whole-state baseline, and the last round tighter.
  // (Thresholds account for the SHA-40 content-id cost: a 40-hex commit id +
  // its parent refs cost more per wire commit, inflating the ratio, but the
  // two STRUCTURAL claims stand -- the delta beats whole-state resync, and
  // per-round it stays bounded by the ops, not the document.)
  const half = ROUNDS >> 1;
  const sum = (a, lo) => a.slice(lo).reduce((x, y) => x + y, 0);
  const dHalf = sum(perRoundDelta, half), bHalf = sum(perRoundBase, half);
  const lastDelta = perRoundDelta[ROUNDS - 1], lastBase = perRoundBase[ROUNDS - 1];
  assert.ok(dHalf < bHalf * 0.75,
    `steady-state delta ${dHalf} must beat whole-state-resync ${bHalf}`);
  assert.ok(lastDelta < lastBase * 0.6,
    `last-round delta ${lastDelta} not bounded vs whole-state ${lastBase}`);
  // and the per-round delta does NOT grow with the document (bounded by ops):
  assert.ok(lastDelta < perRoundDelta[half] * 2.5,
    'per-round delta stays bounded as the doc grows (not a whole-state cost)');
  // the FRONTIER was built from the wire: peer0 has heard of everyone and can
  // certify a non-empty stable cut (the two halves are one subsystem).
  assert.equal(peers[0].registered.size, N, 'peer0 must have heard of all replicas over the wire');
  const sc = peers[0].stableCut();
  assert.ok(sc.complete, 'after convergence the certificate is complete');
  assert.ok(sc.meet.size > 0, 'converged gossip yields a non-empty certified cut');
  t.diagnostic(`N=${N} rounds=${ROUNDS} docLen=${peers[0].read().length} ` +
    `steadyDelta=${dHalf}B steadyBase=${bHalf}B ratio=${(dHalf / bHalf).toFixed(3)} ` +
    `lastRatio=${(lastDelta / lastBase).toFixed(3)} cut=${sc.meet.size}`);
});

test('wire delta is the difference, not the whole state; snapshot only for bulk catch-up', () => {
  const A = new Peer(embedRGA, 'A'), B = new Peer(embedRGA, 'B');
  let id = 0;
  for (let k = 0; k < 200; k++) A.commit({ type: 'ins', id: ++id, el: 'a', anchorId: null });
  // a brand-new peer B is FAR behind: the encoder prefers a bulk snapshot.
  const bulk = deltaOrSnapshot(A, B.ancestryGids());
  assert.equal(bulk.kind, 'snapshot', 'a far-behind peer gets a bulk snapshot, not a giant delta');
  // catch B up, then A does ONE more op: the incremental delta is tiny.
  syncPeers(A, B);
  A.commit({ type: 'ins', id: ++id, el: 'z', anchorId: null });
  const inc = deltaOrSnapshot(A, B.ancestryGids());
  assert.equal(inc.kind, 'delta', 'a caught-up peer gets a delta');
  assert.equal(inc.commits.length, 1, 'the delta carries exactly the one new commit');
  assert.ok(inc.bytes < A.snapshotBytes(), 'the incremental delta is far below a whole-state snapshot');
  syncPeers(A, B);
  assert.equal(A.read().join(''), B.read().join(''), 'converged');
});

// ------------------------------------------------ (3b) evidence correctness
// The discriminating-remove / SettledAt countermodel at runtime level.
// Replica A wants to compact; replica C (lagging) holds an op CONCURRENT with
// the cut that A has not absorbed. The certificate is ABSENT -> compactStable
// REFUSES. Once C is heard from, the certificate appears -> it FIRES, reads
// preserved. The FAIL companion forces the asserted compaction at the same
// point and shows it DIVERGES, proving the not-heard breaker is load-bearing.

/** Build the forked scenario in a fresh runtime; returns {rt,A,B,C}. After
 *  this: A = {10:x, 30:w, 40:y} (30 authored by B and absorbed), C = {10,20:z}
 *  with C's insert 20 CONCURRENT with A's 40 and NOT yet absorbed by A. Ids
 *  are ordered so display is deterministic; z(20) sits BELOW w(30),y(40). */
function forkedScenario(dt) {
  const rt = new Runtime(dt);
  const A = rt.replica('A'), B = rt.replica('B'), C = rt.replica('C');
  A.commit({ type: 'ins', id: 10, el: 'x', anchorId: null }); // A:{10}
  A.sync(C);                                                   // C ff -> {10} (no C commit)
  A.sync(B);                                                   // B ff -> {10}
  B.commit({ type: 'ins', id: 30, el: 'w', anchorId: 10 });   // B:{10,30}
  A.sync(B);                                                   // A ff -> {10,30}; absorbs B#30
  A.commit({ type: 'ins', id: 40, el: 'y', anchorId: 10 });   // A:{10,30,40}
  C.commit({ type: 'ins', id: 20, el: 'z', anchorId: 10 });   // C:{10,20} concurrent, unheard by A
  return { rt, A, B, C };
}

test('evidence correctness: compactStable REFUSES without the certificate, FIRES with it, reads == control', () => {
  const main = forkedScenario(compactibleEmbedRGA);
  const ctrl = forkedScenario(compactibleEmbedRGA); // identical, never compacts

  // hand-derived reads (NOT #eval'd): x is the anchor (sorts above); its
  // children display newest-first by delta descending: y(d30) > w(d20) > z(d10).
  assert.equal(main.A.read().join(''), 'xyw', 'A before hearing C: x, y(40), w(30)');

  // (1) certificate ABSENT: C authored 20 but A has not absorbed it.
  const before = main.A.stableCut();
  assert.equal(before.complete, false, 'not heard from C since the cut');
  assert.deepEqual(before.missing, ['C']);
  const refused = main.A.compactStable();
  assert.equal(refused.compacted, false, 'compaction refused: certificate absent');
  assert.deepEqual(refused.missing, ['C']);
  assert.equal(main.A.read().join(''), ctrl.A.read().join(''), 'refuse is a no-op: reads == control');

  // (2) hear from C: the evidence commit for C now reaches A's head.
  main.A.sync(main.C); ctrl.A.sync(ctrl.C);
  const after = main.A.stableCut();
  assert.equal(after.complete, true, 'certificate complete once C is heard from');
  const fired = main.A.compactStable();
  assert.equal(fired.compacted, true, 'compaction fires with the certificate present');
  // the certified cut is exactly the common prefix {10}: 20,30,40 are each in
  // only one branch, so only id 10 is settled at every replica.
  assert.equal(fired.cutSize, 1, 'certified cut = {10}, the events heard everywhere');
  assert.equal(main.A.read().join(''), ctrl.A.read().join(''), 'fire preserves reads == control');
  assert.equal(main.A.read().join(''), 'xywz', 'x, y(40), w(30), z(20) after absorbing C');

  // (3) keep going past the compaction: a fresh mint anchored on a RECODED
  // coordinate (10) and a full sync round; reads stay == control throughout.
  main.A.commit({ type: 'ins', id: 50, el: 'q', anchorId: 40 });
  ctrl.A.commit({ type: 'ins', id: 50, el: 'q', anchorId: 40 });
  main.A.sync(main.B); ctrl.A.sync(ctrl.B);
  main.B.sync(main.C); ctrl.B.sync(ctrl.C);
  main.A.sync(main.B); ctrl.A.sync(ctrl.B);
  assert.equal(main.A.read().join(''), ctrl.A.read().join(''), 'post-compaction ops preserve reads');
  assert.equal(main.B.read().join(''), ctrl.B.read().join(''), 'and at other replicas');
});

test('FAIL companion: the ASSERTED (uncertified) compaction at the same point DIVERGES', () => {
  const bad = forkedScenario(compactibleEmbedRGA);
  const ctrl = forkedScenario(compactibleEmbedRGA);
  // Force the asserted path with an OVER-BROAD cut: claim 10,30,40 settled
  // while C's concurrent 20 is still in flight (unheard). This is exactly what
  // compactStable REFUSES above. Dense renumber of {30,40} shrinks their
  // deltas (20,30 -> 1,2), so C's frozen delta-10 z later sorts ABOVE them.
  bad.A.compact({ settledIds: new Set([10, 30, 40]), inflight: [] });
  bad.A.sync(bad.C);  // absorb the concurrent z(20), lifted into the new epoch
  ctrl.A.sync(ctrl.C);
  const correct = ctrl.A.read().join('');
  const forced = bad.A.read().join('');
  assert.equal(correct, 'xywz', 'control (never compacted) is correct');
  assert.notEqual(forced, correct, 'the uncertified compaction diverges (the countermodel)');
  assert.ok(forced.indexOf('z') < forced.indexOf('y'),
    'z has jumped above y: the frozen-delta order flip the certificate prevents');
});

// ------------------------------------------------ (3c) twin PBT: certified GC
// Twin runs: identical random head-sync gossip on two runtimes; twin[1] also
// runs the CERTIFIED state GC (compactStable) at random points, twin[0] never
// compacts. Per step every replica reads identically on both twins -- the
// runtime witness that a certificate-gated compaction preserves reads. BOTH
// certificate branches must be exercised: the GC
// FIRES (certificate present) and REFUSES (not heard from everyone / stale
// epoch / empty cut). Ops are generated from the compacting twin's own read
// (honest clients) after asserting it equals the control twin's read.

const P3 = { pSync: 0.4, pGather: 0.2, pDel: 0.28 };

const genEmbedOp = (rng, replica, mint) => {
  const doc = replica.read();
  if (doc.length > 0 && rng() < P3.pDel) return { type: 'del', id: pick(rng, doc) };
  const id = mint.next++;
  const anchorId = doc.length > 0 && rng() < 0.6 ? pick(rng, doc) : null;
  return { type: 'ins', id, el: id, anchorId };
};
const embedOracle = (evs) => {
  const del = new Set(evs.filter((p) => p.type === 'del').map((p) => p.id));
  return evs.filter((p) => p.type === 'ins' && !del.has(p.id)).map((p) => p.id);
};
const canon = (xs) => [...xs].map((x) => JSON.stringify(x)).sort();

function twinTrial(seed, stats) {
  const rng = mulberry32(seed);
  const nRep = 3 + (seed % 3);
  const nSteps = 25 + Math.floor(rng() * 26);
  const twins = [new Runtime(compactibleEmbedRGA), new Runtime(compactibleEmbedRGA)];
  const reps = twins.map((rt) => Array.from({ length: nRep }, (_, i) => rt.replica('r' + i)));
  const mint = { next: 1 };

  // sync on BOTH twins; the criss-cross verdict must agree (as in gc-pbt)
  const doSync = (r, j) => {
    const attempt = (twin) => {
      try { reps[twin][r].sync(reps[twin][j]); return null; }
      catch (e) { if (e instanceof CrissCrossError) return e; throw e; }
    };
    const e0 = attempt(0), e1 = attempt(1);
    assert.equal(e0 === null, e1 === null, `twins disagree on criss-cross r${r}~r${j}`);
    if (e0) stats.skipped++; else stats.syncs++;
  };
  const compact1 = (r) => { // certified GC on twin[1] ONLY
    const res = reps[1][r].compactStable();
    if (res.compacted) stats.fires++; else stats.refuses++;
  };
  const checkReads = (label) => {
    for (let i = 0; i < nRep; i++) {
      assert.deepEqual(reps[1][i].read(), reps[0][i].read(), `${label} r${i}`);
    }
  };

  for (let step = 0; step < nSteps; step++) {
    const r = Math.floor(rng() * nRep);
    const roll = rng();
    if (roll < P3.pSync) {
      const j = Math.floor(rng() * nRep);
      if (j !== r) doSync(r, j);
    } else if (roll < P3.pSync + P3.pGather) {
      // gather r's view of everyone (both twins), then compact only twin[1]:
      // exercises a mid-run FIRE and the post-compaction merges after it.
      for (let j = 0; j < nRep; j++) if (j !== r) doSync(r, j);
      compact1(r);
    } else {
      assert.deepEqual(reps[1][r].read(), reps[0][r].read(), `pre-op @${step} r${r}`);
      const op = genEmbedOp(rng, reps[1][r], mint);
      reps[0][r].commit(op); reps[1][r].commit(op);
    }
    checkReads(`step ${step}`);
  }

  // drive toward convergence, then a certified compaction on each replica
  for (let pass = 0; pass < 3; pass++) {
    for (let i = 0; i < nRep; i++) for (let j = i + 1; j < nRep; j++) doSync(i, j);
  }
  checkReads('post-converge');
  for (let i = 0; i < nRep; i++) compact1(i);
  checkReads('post-compact');
  // LIVE oracle: each replica's read = fold of its head's implicit event set
  for (let i = 0; i < nRep; i++) {
    const evs = twins[0].dag.events(reps[0][i].head.id).map((o) => o.payload);
    assert.deepEqual(canon(reps[0][i].read()), canon(embedOracle(evs)), `LIVE oracle r${i}`);
  }
}

test('twin PBT: certified GC vs no-GC control, 160 trials, both branches exercised', (t) => {
  const stats = { fires: 0, refuses: 0, syncs: 0, skipped: 0 };
  for (let seed = 0; seed < 160; seed++) twinTrial(seed * 100003 + 17, stats);
  t.diagnostic(`certified-GC PBT: ${JSON.stringify(stats)}`);
  assert.ok(stats.fires > 0, 'the certified GC must FIRE in some trials (certificate present)');
  assert.ok(stats.refuses > 0, 'the certified GC must REFUSE in some trials (not-heard / stale epoch)');
  assert.ok(stats.skipped > 0, 'expected some criss-cross-gated syncs across 160 trials');
});
