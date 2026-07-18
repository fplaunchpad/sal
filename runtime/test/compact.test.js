// compactEliasDelta v1 tests (task #97, practical tail).
//
// EXPECTED VALUES ARE HAND-DERIVED from the flipped Elias-delta code, never
// evaluated from the implementation under test. Reference codewords:
//   enc(1)='0'  enc(2)='1000'  enc(3)='1001'  enc(4)='10100'  enc(5)='10101'
//   enc(7)='10111'  enc(8)='11000000'  enc(18)='110010010'
//   enc(19)='110010011'  enc(20)='110010100'  enc(22)='110010110'
//   enc(25)='110011001'
// (dEnc d = binEnc(bitlen d) ++ low bits of d; binEnc L = 1^(len-1) 0 ++
// low bits of L; checked against the kernel-pinned values in code.test.js.)
//
// Suites:
//   1. decoder round-trip (decodeChain is enc's inverse);
//   2. directed delete-heavy compaction: reads identical, symbol count
//      strictly drops, both pinned (31 -> 10);
//   3. the IN-FLIGHT NEGATIVE CONTROL: a deliberately unguarded dense
//      renumbering flips an order against a frozen in-flight delta;
//      the guarded compactEliasDelta skips that group and stays sound;
//   4. lazy translation on ingest: a replica that never compacted merges
//      in, its records translated (stable prefix re-mapped, fresh delta
//      kept verbatim), coordinate pinned;
//   5. a dead range with a known in-flight coordinate through it is KEPT
//      (step 1's in-flight condition);
//   6. future mints after compaction anchor correctly: Lamport freshness
//      sorts them newest-first past the compacted block;
//   7. v1 guards: stale-epoch compaction refused, non-compactible
//      datatype refused;
//   8. twin PBT: compaction at explicitly-settled points vs a control
//      that never compacts; per-step read equality everywhere, including
//      post-compaction merges with replicas that never compacted.

import test from 'node:test';
import assert from 'node:assert/strict';
import { Runtime } from '../src/runtime.js';
import { CrissCrossError } from '../src/lca.js';
import { orset } from '../src/datatypes/orset.js';
import {
  compactEliasDelta, compactibleEmbedRGA as D, decodeChain,
} from '../src/compact.js';

const range = (a, b) => Array.from({ length: b - a + 1 }, (_, i) => a + i);

// ---------------------------------------------------------------- 1. decoder

test('decodeChain inverts enc on singletons and chains', () => {
  for (const d of [1, 2, 3, 4, 5, 7, 8, 18, 100, 12345]) {
    assert.deepEqual(decodeChain(D.code.enc(d)), [d]);
  }
  assert.deepEqual(decodeChain(D.code.enc(18) + D.code.enc(3) + D.code.enc(1)),
    [18, 3, 1]);
  assert.deepEqual(decodeChain(''), []);
  assert.throws(() => decodeChain('1'), /codeword/);   // truncated header
  assert.throws(() => decodeChain('1000' + '10'), /codeword/); // trailing junk
});

// ------------------------------------------------- 2. directed delete-heavy

// Root-anchored inserts 1..20, one child 21 under 18, then delete 1..18.
// Live: 19 (enc 19, 9 bits), 20 (enc 20, 9 bits), 21 (enc 18 ++ enc 3,
// 13 bits) = 31 symbols. Settled cut over everything renumbers the root
// group {18, 19, 20} -> {1, 2, 3} and 18's group {3} -> {1}:
//   19 -> enc 2 = '1000' (4), 20 -> enc 3 = '1001' (4), 21 -> '00' (2),
// 10 symbols. Display order [e20, e19, e21] on both sides.
function deleteHeavyReplica() {
  const rt = new Runtime(D);
  const r = rt.replica('A');
  for (const id of range(1, 20)) r.commit({ type: 'ins', id, el: 'e' + id, anchorId: null });
  r.commit({ type: 'ins', id: 21, el: 'e21', anchorId: 18 });
  for (const id of range(1, 18)) r.commit({ type: 'del', id });
  return { rt, r };
}
const fullCut = () => ({ settledIds: new Set(range(1, 21)), inflight: [] });

test('directed delete-heavy: reads identical, symbols 31 -> 10 (datatype level)', () => {
  const { r } = deleteHeavyReplica();
  const s = r.head.state;
  assert.deepEqual(D.read(s), ['e20', 'e19', 'e21']);          // hand-derived
  assert.equal(D.symbolCount(s), 31);                          // 9 + 9 + 13
  const { state: s2, translate, stats } = compactEliasDelta(s, fullCut());
  assert.deepEqual(D.read(s2), ['e20', 'e19', 'e21']);         // reads identical
  assert.equal(D.symbolCount(s2), 10);                         // 4 + 4 + 2
  assert.ok(D.symbolCount(s2) < D.symbolCount(s));             // strictly drops
  assert.notEqual(D.fingerprint(s2), D.fingerprint(s));        // NOT a no-op
  assert.equal(s2.get(19).coord, '1000');
  assert.equal(s2.get(20).coord, '1001');
  assert.equal(s2.get(21).coord, '00');
  assert.equal(stats.groupsRenumbered, 2);
  assert.equal(stats.groupsSkippedInflight + stats.groupsSkippedUnstable, 0);
  // the stable-prefix map, pinned pointwise
  assert.equal(translate('110010011'), '1000');                // live 19
  assert.equal(translate('110010010'), '0');                   // dead chain node 18
  assert.equal(translate('1100100101001'), '00');              // live 21 via 18
  assert.equal(translate('110011001'), '110011001');           // unknown root delta 25: verbatim
});

test('directed delete-heavy through the runtime hook replica.compact', () => {
  const { r } = deleteHeavyReplica();
  const before = r.read();
  const { stats } = r.compact(fullCut());
  assert.deepEqual(r.read(), before);
  assert.equal(stats.symbolsBefore, 31);
  assert.equal(stats.symbolsAfter, 10);
});

// --------------------------------------- 3. the in-flight negative control

// Settled siblings at the root: x = id 2 (enc 2 = '1000'), y = id 7
// (enc 7 = '10111'). A concurrent replica that saw x but NOT y minted
// z = id 5, root-anchored, coord enc 5 = '10101' -- still in flight at the
// compactor. True order (all delivered): y(7) > z(5) > x(2).
// UNGUARDED dense renumbering maps x -> enc 1 = '0', y -> enc 2 = '1000';
// the frozen '10101' now beats the ex-7's '1000': z JUMPS OVER y. The
// guarded pass skips the group (known in-flight child) and stays sound.
function xyState() {
  let s = D.init();
  s = D.apply(s, { type: 'ins', id: 2, el: 'x', anchorId: null });
  s = D.apply(s, { type: 'ins', id: 7, el: 'y', anchorId: null });
  return s;
}
const Z = '10101'; // enc(5), minted elsewhere, in flight
const inflightCut = () => ({ settledIds: new Set([2, 7]), inflight: [Z] });
const ingest = (state, translate) => {
  const s = new Map(state);
  s.set(5, Object.freeze({ coord: translate(Z), el: 'z' }));
  return s;
};

test('negative control: unguarded dense renumber FLIPS the order (datatype level)', () => {
  const s = xyState();
  const full = D.apply(s, { type: 'ins', id: 5, el: 'z', anchorId: null });
  assert.deepEqual(D.read(full), ['y', 'z', 'x']);             // the true order
  const { state: s2, translate, stats } =
    compactEliasDelta(s, inflightCut(), { unguardedRenumber: true });
  assert.equal(stats.groupsRenumbered, 1);
  assert.equal(s2.get(2).coord, '0');
  assert.equal(s2.get(7).coord, '1000');
  assert.equal(translate(Z), Z);                               // frozen delta verbatim
  const readAfter = D.read(ingest(s2, translate));
  assert.deepEqual(readAfter, ['z', 'y', 'x']);                // z jumped over y
  assert.notDeepEqual(readAfter, D.read(full));                // THE FLIP
});

test('guarded compactEliasDelta skips the in-flight group and stays sound', () => {
  const s = xyState();
  const full = D.apply(s, { type: 'ins', id: 5, el: 'z', anchorId: null });
  const { state: s2, translate, stats } = compactEliasDelta(s, inflightCut());
  assert.equal(stats.groupsRenumbered, 0);
  assert.equal(stats.groupsSkippedInflight, 1);                // the skip, pinned
  assert.equal(s2.get(2).coord, '1000');                       // untouched
  assert.equal(s2.get(7).coord, '10111');
  assert.equal(stats.symbolsAfter, stats.symbolsBefore);
  assert.deepEqual(D.read(ingest(s2, translate)), D.read(full)); // sound
});

test('negative control through the runtime: unguarded flip vs guarded soundness', () => {
  for (const unguarded of [true, false]) {
    const mk = () => {
      const rt = new Runtime(D);
      const a = rt.replica('A'), c = rt.replica('C');
      a.commit({ type: 'ins', id: 2, el: 'x', anchorId: null });
      a.commit({ type: 'ins', id: 7, el: 'y', anchorId: null });
      c.commit({ type: 'ins', id: 5, el: 'z', anchorId: null }); // concurrent: in flight
      return { a, c };
    };
    const control = mk();
    control.a.sync(control.c);
    assert.deepEqual(control.a.read(), ['y', 'z', 'x']);
    const subj = mk();
    subj.a.compact(inflightCut(), unguarded ? { unguardedRenumber: true } : undefined);
    subj.a.sync(subj.c);                                       // z translated on ingest
    assert.equal(subj.a.head.state.get(5).coord, Z);           // frozen delta verbatim
    if (unguarded) {
      assert.deepEqual(subj.a.read(), ['z', 'y', 'x']);        // the flip, end to end
      assert.notDeepEqual(subj.a.read(), control.a.read());
    } else {
      assert.deepEqual(subj.a.read(), control.a.read());       // guarded: sound
      assert.deepEqual(subj.c.read(), control.a.read());
    }
  }
});

// ------------------------------- 4. lazy translation on ingest (settled cut)

// A and B share x = id 2, y = id 7 (fully settled, no in-flight). A
// compacts: x -> enc 1 = '0', y -> enc 2 = '1000'. B, which NEVER
// compacted, then mints w = id 9 anchored at x in the OLD code:
// w = enc 2 ++ enc 7 = '1000'+'10111'. The merge lifts B's state into A's
// epoch: w's stable prefix is re-mapped, its fresh delta kept verbatim:
// '0'+'10111' = '010111'. Reads match the never-compacted control.
test('lazy translation: a never-compacted replica merges in, records translated', () => {
  const mk = () => {
    const rt = new Runtime(D);
    const a = rt.replica('A'), b = rt.replica('B');
    a.commit({ type: 'ins', id: 2, el: 'x', anchorId: null });
    a.commit({ type: 'ins', id: 7, el: 'y', anchorId: null });
    b.sync(a); // fully delivered: the cut below is genuinely settled
    return { a, b };
  };
  const control = mk();
  control.b.commit({ type: 'ins', id: 9, el: 'w', anchorId: 2 });
  control.a.sync(control.b);
  assert.deepEqual(control.a.read(), ['y', 'x', 'w']);
  const subj = mk();
  subj.a.compact({ settledIds: new Set([2, 7]), inflight: [] });
  subj.b.commit({ type: 'ins', id: 9, el: 'w', anchorId: 2 }); // old-code mint
  assert.equal(subj.b.head.state.get(9).coord, '100010111');   // pre-merge, old code
  subj.a.sync(subj.b);
  assert.equal(subj.a.head.state.get(9).coord, '010111');      // translated on ingest
  assert.equal(subj.a.head.state.get(2).coord, '0');
  assert.deepEqual(subj.a.read(), control.a.read());            // reads identical
  assert.deepEqual(subj.b.read(), control.a.read());
});

// --------------------- 5. dead range with an in-flight coordinate through it

// a = id 1 (root, enc 1 = '0') is shared, then deleted at A after a
// concurrent replica minted z = id 9 UNDER a (coord '0'+enc 8 =
// '011000000', in flight). A's live set is only b = id 4 (enc 4 =
// '10100'). The dead range {1} has an in-flight coordinate through it, so
// it is KEPT as a chain node (and takes ordinal 1 in the renumbered root
// group: '0', unchanged); b takes ordinal 2: '1000'. z ingests through the
// kept node, order preserved vs the control.
test('dead range with in-flight through it is kept, not dropped', () => {
  const mk = () => {
    const rt = new Runtime(D);
    const a = rt.replica('A'), c = rt.replica('C');
    a.commit({ type: 'ins', id: 1, el: 'a', anchorId: null });
    c.sync(a);
    c.commit({ type: 'ins', id: 9, el: 'z', anchorId: 1 });    // in flight to A
    a.commit({ type: 'ins', id: 4, el: 'b', anchorId: null });
    a.commit({ type: 'del', id: 1 });
    return { a, c };
  };
  const control = mk();
  control.a.sync(control.c);
  assert.deepEqual(control.a.read(), ['b', 'z']);
  const subj = mk();
  const { stats } = subj.a.compact({
    settledIds: new Set([1, 4]), inflight: ['011000000'],
  });
  assert.equal(stats.groupsRenumbered, 1);                     // the root group
  assert.equal(stats.groupsSkippedInflight, 1);                // dead 1's group
  assert.equal(subj.a.head.state.get(4).coord, '1000');        // ordinal 2
  subj.a.sync(subj.c);
  assert.equal(subj.a.head.state.get(9).coord, '011000000');   // prefix '0' kept
  assert.deepEqual(subj.a.read(), control.a.read());
});

// ------------------------------------------------------ 6. future mints

// After the delete-heavy compaction (root group renumbered to ordinals
// 1..3), a fresh root mint id 22 has delta 22: enc 22 = '110010110' beats
// every ordinal codeword lexicographically, so it sorts newest-first past
// the whole compacted block; a mint under renumbered 21 extends 21's NEW
// coordinate: '00' ++ enc(23-21) = '001000'.
test('future mints anchor correctly among renumbered siblings', () => {
  const { r } = deleteHeavyReplica();
  r.compact(fullCut());
  r.commit({ type: 'ins', id: 22, el: 'e22', anchorId: null });
  r.commit({ type: 'ins', id: 23, el: 'e23', anchorId: 21 });
  assert.equal(r.head.state.get(22).coord, '110010110');
  assert.equal(r.head.state.get(23).coord, '001000');
  assert.deepEqual(r.read(), ['e22', 'e20', 'e19', 'e21', 'e23']);
});

// ------------------------------------------------------------- 7. v1 guards

test('stale-epoch compaction refused; non-compactible datatype refused', () => {
  const rt = new Runtime(D);
  const a = rt.replica('A'), b = rt.replica('B');
  a.commit({ type: 'ins', id: 1, el: 'a', anchorId: null });
  b.sync(a);
  b.commit({ type: 'ins', id: 2, el: 'b', anchorId: null });   // b diverges at epoch 0
  a.compact({ settledIds: new Set([1]), inflight: [] });       // epoch 1
  assert.throws(() => b.compact({ settledIds: new Set([1, 2]), inflight: [] }),
    /stale-epoch/);
  b.sync(a);                                                   // lifts b to epoch 1
  b.compact({ settledIds: new Set([1, 2]), inflight: [] });    // now legal
  const rt2 = new Runtime(orset);
  assert.throws(() => rt2.replica('X').compact({}), /does not support/);
});

// ----------------------------------------------------------------- 8. PBT

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
const canon = (xs) => [...xs].map((x) => JSON.stringify(x)).sort();
const P = { pSync: 0.3, pDel: 0.3, pCompact: 0.2 };

// Twin execution: identical random head-sync runs; the SUBJECT twin
// compacts at explicitly-settled points (a full sync round after which all
// heads coincide: everyone has heard from everyone, so the whole event set
// is settled and cut.inflight = []); the CONTROL twin never compacts.
// Asserted per step, per replica: reads identical across twins. Merges of
// never-compacted replicas into compacted heads (the lazy translation
// path) arise constantly and are counted.
function runCompactTrial(seed) {
  const rng = mulberry32(seed);
  const nRep = 3 + (seed % 3);
  const nSteps = 25 + Math.floor(rng() * 26);
  const control = new Runtime(D);
  const subject = new Runtime(D);
  const cReps = Array.from({ length: nRep }, (_, i) => control.replica('r' + i));
  const sReps = Array.from({ length: nRep }, (_, i) => subject.replica('r' + i));
  const mint = { next: 1 };
  const insMinted = new Set();
  const stats = { compactions: 0, saved: 0, syncs: 0, skipped: 0, liftedMerges: 0 };

  const doSync = (i, j) => {
    // a real merge across epochs on the subject = the lazy translation path
    const a = sReps[i].head, b = sReps[j].head;
    if (a.id !== b.id
        && !subject.dag.isAncestor(a.id, b.id) && !subject.dag.isAncestor(b.id, a.id)
        && subject.epochOf.get(a.id) !== subject.epochOf.get(b.id)) {
      stats.liftedMerges++;
    }
    const attempt = (reps) => {
      try { reps[i].sync(reps[j]); return null; }
      catch (e) { if (e instanceof CrissCrossError) return e; throw e; }
    };
    const e0 = attempt(cReps), e1 = attempt(sReps);
    assert.equal(e0 === null, e1 === null, `criss-cross verdicts diverge r${i}~r${j}`);
    if (e0) stats.skipped++; else stats.syncs++;
  };

  const settleAndCompact = () => {
    for (let pass = 0; pass < 3; pass++) {
      for (let i = 0; i < nRep; i++) for (let j = i + 1; j < nRep; j++) doSync(i, j);
    }
    const h = sReps[0].head.id;
    if (!sReps.every((r) => r.head.id === h)) return;  // criss-cross gated: not settled
    const r = pick(rng, sReps);
    const before = r.read();
    const { stats: cs } = r.compact({ settledIds: new Set(insMinted), inflight: [] });
    assert.deepEqual(r.read(), before, 'compaction changed the read');
    assert.ok(cs.symbolsAfter <= cs.symbolsBefore, 'compaction grew the state');
    stats.compactions++;
    stats.saved += cs.symbolsBefore - cs.symbolsAfter;
  };

  for (let step = 0; step < nSteps; step++) {
    const r = Math.floor(rng() * nRep);
    if (rng() < P.pCompact) {
      settleAndCompact();
    } else if (rng() < P.pSync) {
      const j = Math.floor(rng() * nRep);
      if (j !== r) doSync(r, j);
    } else {
      assert.deepEqual(sReps[r].read(), cReps[r].read(), `pre-op read @${step} r${r}`);
      const doc = sReps[r].read();
      let op;
      if (doc.length > 0 && rng() < P.pDel) {
        op = { type: 'del', id: pick(rng, doc) };
      } else {
        const id = mint.next++;
        insMinted.add(id);
        op = { type: 'ins', id, el: id, anchorId: doc.length > 0 && rng() < 0.6 ? pick(rng, doc) : null };
      }
      cReps[r].commit(op);
      sReps[r].commit(op);
    }
    for (let i = 0; i < nRep; i++) {
      assert.deepEqual(sReps[i].read(), cReps[i].read(), `read @${step} r${i}`);
    }
  }

  for (let pass = 0; pass < 3; pass++) {
    for (let i = 0; i < nRep; i++) for (let j = i + 1; j < nRep; j++) doSync(i, j);
  }
  for (let i = 0; i < nRep; i++) {
    assert.deepEqual(sReps[i].read(), cReps[i].read(), 'final read');
    // LIVE oracle: read = fold of the head's implicit event set
    const evs = subject.dag.events(sReps[i].head.id).map((o) => o.payload);
    const del = new Set(evs.filter((p) => p.type === 'del').map((p) => p.id));
    const live = evs.filter((p) => p.type === 'ins' && !del.has(p.id)).map((p) => p.id);
    assert.deepEqual(canon(sReps[i].read()), canon(live), `LIVE oracle r${i}`);
  }
  return stats;
}

test('twin PBT: compaction at settled points vs control, 140 trials', (t) => {
  const tot = { compactions: 0, saved: 0, syncs: 0, skipped: 0, liftedMerges: 0 };
  for (let seed = 0; seed < 140; seed++) {
    const s = runCompactTrial(seed * 60013 + 29);
    for (const k of Object.keys(tot)) tot[k] += s[k];
  }
  t.diagnostic(`compact PBT: ${JSON.stringify(tot)}`);
  assert.ok(tot.compactions > 100, `compaction must fire (${tot.compactions})`);
  assert.ok(tot.saved > 500, `compaction must actually save symbols (${tot.saved})`);
  assert.ok(tot.liftedMerges > 50,
    `the lazy-translation merge path must be exercised (${tot.liftedMerges})`);
});
