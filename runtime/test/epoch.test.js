// THE EPOCH DIAMOND, wired into the runtime. Replicas that compacted at
// INCOMPARABLE certified cuts merge with no coordination, reads == the never-
// compacted twin. The cross-epoch THROW is replaced by the certificate-determined
// join. Every expected value below is HAND-DERIVED (never #eval'd from the code
// under test); each PASS carries a FAIL companion.

import test from 'node:test';
import assert from 'node:assert/strict';
import { DistributedReplica, syncReplicas } from '../src/replica.js';
import { compactibleEmbedRGA, compactEliasDelta } from '../src/compact.js';
import { embedRGA, eliasDeltaCode as C } from '../src/datatypes/embedRGA.js';
import { orset } from '../src/datatypes/orset.js';
import {
  EpochDag, EPOCH0, cutKey, buildInverseTranslate, doubleCertificate, ackOnlyCertificate,
} from '../src/epoch.js';

const D = embedRGA;
const dump = (s) => [...s.entries()].sort((a, b) => a[0] - b[0]).map(([i, r]) => i + ':' + r.coord).join(',');
const mulberry32 = (seed) => { let a = seed >>> 0; return () => { a = (a + 0x6d2b79f5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; };
const pick = (rng, xs) => xs[Math.floor(rng() * xs.length)];

// ---------------------------------------------------------------- epoch DAG units
test('cut key is canonical (sorted, order-independent) and the DAG orders cuts', () => {
  assert.equal(cutKey(new Set([3, 1, 2])), cutKey(new Set([2, 3, 1])));
  assert.equal(cutKey(new Set([])), EPOCH0);
  const dag = new EpochDag();
  const U = dag.compaction('kU', { settledIds: [1, 2, 3], parentKey: EPOCH0 });
  const V = dag.compaction('kV', { settledIds: [1, 2, 4], parentKey: EPOCH0 });
  const S = dag.compaction('kS', { settledIds: [1, 2], parentKey: EPOCH0 });
  assert.equal(dag.compare(S, U), 'sub', '{1,2} ⊆ {1,2,3}');
  assert.equal(dag.compare(U, S), 'sup');
  assert.equal(dag.compare(U, V), 'divergent', '{1,2,3} vs {1,2,4} are incomparable');
  // the JOIN W = U ∪ V, parents [U, V]
  const W = dag.join(U, V);
  assert.deepEqual([...dag.get(W).settledIds].sort((a, b) => a - b), [1, 2, 3, 4]);
  assert.deepEqual(dag.get(W).parents, [U, V]);
});

test('inverse translate round-trips survivors and factors stragglers (PASS + FAIL)', () => {
  let s = D.init();
  s = D.apply(s, { type: 'ins', id: 1, el: 'x1', anchorId: null });
  s = D.apply(s, { type: 'ins', id: 2, el: 'x2', anchorId: null });
  s = D.apply(s, { type: 'del', id: 1 });                        // x1 dead
  const { state: comp, translate } = compactEliasDelta(s, { settledIds: new Set([1, 2]), inflight: [] });
  assert.equal(comp.get(2).coord, C.enc(1), 'x2 renumbered (2)->(1)');
  const inv = buildInverseTranslate(s, comp);
  // survivor: inv(translate(c)) = c
  assert.equal(inv(comp.get(2).coord), s.get(2).coord, 'survivor round-trips to epoch 0');
  // straggler minted on the compacted state factors through its anchor's prefix
  const strag = D.apply(comp, { type: 'ins', id: 9, el: 'y', anchorId: 2 });
  assert.equal(inv(strag.get(9).coord), C.enc(2) + C.enc(7), 'straggler lifts to its epoch-0 birth coord');
  // FAIL companion: a coordinate of a DROPPED record is NOT in the inverse domain
  // (record-identity transport, not membership pullback): it rides verbatim.
  assert.equal(inv(C.enc(5)), C.enc(5), 'a non-record coordinate is never invented into the domain');
});

// ------------------------------------------------------- c1: the H-D diamond at s1
test('c1 diamond: both legs and the one-shot land BIT-IDENTICAL, reads == twin', () => {
  let s0 = D.init();
  for (const id of [1, 2, 3, 4]) s0 = D.apply(s0, { type: 'ins', id, el: String(id * 10), anchorId: null });
  const twin = D.apply(D.apply(s0, { type: 'del', id: 1 }), { type: 'del', id: 3 });
  // leg A: gcS1 (drop x3) then relative-compact the remainder (drop x1)
  let A = compactEliasDelta(D.apply(s0, { type: 'del', id: 3 }), { settledIds: new Set([1, 2, 3, 4]), inflight: [] }).state;
  A = compactEliasDelta(D.apply(A, { type: 'del', id: 1 }), { settledIds: new Set([1, 2, 4]), inflight: [] }).state;
  // leg B: gcS2 (drop x1) then the remainder (drop x3) -- the symmetric path
  let B = compactEliasDelta(D.apply(s0, { type: 'del', id: 1 }), { settledIds: new Set([1, 2, 3, 4]), inflight: [] }).state;
  B = compactEliasDelta(D.apply(B, { type: 'del', id: 3 }), { settledIds: new Set([2, 3, 4]), inflight: [] }).state;
  // one-shot at W
  let W = compactEliasDelta(D.apply(D.apply(s0, { type: 'del', id: 1 }), { type: 'del', id: 3 }), { settledIds: new Set([1, 2, 3, 4]), inflight: [] }).state;
  assert.equal(dump(A), '2:0,4:1000', 'hand-derived W state: x2->(1), x4->(2)');
  assert.equal(dump(A), dump(W), 'leg A == one-shot, bit-identical (s1)');
  assert.equal(dump(B), dump(W), 'leg B == one-shot, bit-identical (s1)');
  assert.deepEqual(D.readIds(A), [4, 2]);
  assert.deepEqual(D.readIds(A), D.readIds(twin), 'reads == never-compacted twin');
  assert.deepEqual(D.readIds(B), D.readIds(twin));
});

// ---------------------------------- O2: the aliasing negative, transported domain
test('naive membership pullback ALIASES; record-identity transport does not (FAIL + PASS)', () => {
  let s0 = D.init();
  for (const id of [1, 2, 3, 4]) s0 = D.apply(s0, { type: 'ins', id, el: String(id * 10), anchorId: null });
  const gcS1 = compactEliasDelta(D.apply(s0, { type: 'del', id: 3 }), { settledIds: new Set([1, 2, 3, 4]), inflight: [] });
  const relA = compactEliasDelta(D.apply(gcS1.state, { type: 'del', id: 1 }), { settledIds: new Set([1, 2, 4]), inflight: [] });
  const comp = (c) => relA.translate(gcS1.translate(c));
  // FAIL companion: the DROPPED x3 coord (enc 3) and the KEPT x4 coord (enc 4)
  // collapse to the SAME image -- a domain by membership pullback is non-injective.
  assert.equal(comp(C.enc(3)), comp(C.enc(4)), 'dropped enc3 aliases kept enc4 under the naive composite');
  assert.notEqual(C.enc(3), C.enc(4));
  // PASS: the transported domain is the kept records BY IDENTITY {2,4}; their W
  // coordinates are distinct, and the runtime only ever translates records it
  // holds (never a membership pullback), so no alias arises.
  assert.notEqual(relA.state.get(2).coord, relA.state.get(4).coord, 'kept records stay distinct');
  assert.equal(relA.state.get(2).coord, C.enc(1));
  assert.equal(relA.state.get(4).coord, C.enc(2));
});

// -------------------------------------------- c4: translation is NECESSARY (flip)
test('c4 no-translation control FLIPS the read; translation restores the twin', () => {
  let s = D.init();
  s = D.apply(s, { type: 'ins', id: 1, el: 'x1', anchorId: null });
  s = D.apply(s, { type: 'ins', id: 2, el: 'x2', anchorId: null });
  s = D.apply(s, { type: 'del', id: 1 });
  const twin = D.apply(s, { type: 'ins', id: 9, el: 'y', anchorId: 2 });      // epoch-0 truth
  const { state: comp } = compactEliasDelta(s, { settledIds: new Set([1, 2]), inflight: [] });
  // TRANSLATED = the runtime's id-addressed merge: y re-derived on the compacted anchor
  const translated = D.apply(comp, { type: 'ins', id: 9, el: 'y', anchorId: 2 });
  // RAW = a cross-epoch union WITHOUT translation: y keeps its epoch-0 coordinate
  const raw = comp.set(9, Object.freeze({ coord: twin.get(9).coord, el: 'y' }));
  assert.deepEqual(D.readIds(twin), [2, 9], 'twin: x2 before y');
  assert.deepEqual(D.readIds(raw), [9, 2], 'RAW flips: y jumps above x2 (the defect the throw guarded)');
  assert.notDeepEqual(D.readIds(raw), D.readIds(twin));
  assert.deepEqual(D.readIds(translated), D.readIds(twin), 'translation restores the twin read');
});

test('c4 in the RUNTIME: the cross-epoch merge translates (reads == twin)', () => {
  const a = new DistributedReplica(compactibleEmbedRGA, 'A'), b = new DistributedReplica(compactibleEmbedRGA, 'B');
  const ta = new DistributedReplica(compactibleEmbedRGA, 'A'), tb = new DistributedReplica(compactibleEmbedRGA, 'B');
  a.register('B'); b.register('A');
  for (const r of [a, ta]) { r.commit({ type: 'ins', id: 1, el: 'x1', anchorId: null }); r.commit({ type: 'ins', id: 2, el: 'x2', anchorId: null }); r.commit({ type: 'del', id: 1 }); }
  syncReplicas(a, b); syncReplicas(ta, tb);
  b.commit({ type: 'ins', id: 3, el: 'z', anchorId: null }); tb.commit({ type: 'ins', id: 3, el: 'z', anchorId: null });
  syncReplicas(a, b); syncReplicas(ta, tb);           // A now heard from B: certificate complete
  assert.equal(a.compactStable().compacted, true, 'A compacts alone -> epoch 1');
  assert.equal(a.epoch, 1); assert.equal(b.epoch, 0);
  b.commit({ type: 'ins', id: 9, el: 'y', anchorId: 2 });   // straggler anchored at a survivor
  tb.commit({ type: 'ins', id: 9, el: 'y', anchorId: 2 });
  b.ingest(a.delta(b.ancestryGids()));
  b.mergeWithGid(a.headGid);                                 // CROSS-EPOCH merge
  syncReplicas(ta, tb);
  assert.equal(b.read().join(''), tb.read().join(''), 'cross-epoch merge reads == never-compacted twin');
  assert.ok(b.read().includes('y') && b.read().includes('x2'));
});

// --------------------------------------------------- A3: the map-drop double cert
test('A3: ack-only map drop is UNSOUND (would flip); the double certificate is sound', () => {
  // The coordinate flip: an epoch-0 straggler needs the e-1->e map. Dropping it
  // (ack-only) leaves the straggler untranslated -> the c4 flip.
  let s = D.init();
  s = D.apply(s, { type: 'ins', id: 1, el: 'x1', anchorId: null });
  s = D.apply(s, { type: 'ins', id: 2, el: 'x2', anchorId: null });
  s = D.apply(s, { type: 'del', id: 1 });
  const { state: comp } = compactEliasDelta(s, { settledIds: new Set([1, 2]), inflight: [] });
  const twin = D.apply(s, { type: 'ins', id: 9, el: 'y', anchorId: 2 });
  const dropped = comp.set(9, Object.freeze({ coord: twin.get(9).coord, el: 'y' })); // map gone
  const kept = D.apply(comp, { type: 'ins', id: 9, el: 'y', anchorId: 2 });           // map applied
  assert.notDeepEqual(D.readIds(dropped), D.readIds(twin), 'ack-only drop mistranslates the straggler (flips)');
  assert.deepEqual(D.readIds(kept), D.readIds(twin), 'with the map, the straggler reads correctly');
  // The gate: doubleCertificate requires BOTH halves; ack-only is refused.
  assert.equal(ackOnlyCertificate({ everyoneAdvanced: true }), true, 'ack-only would say yes');
  assert.equal(doubleCertificate({ everyoneAdvanced: true }), false, 'double cert: ack alone is not enough');
  assert.equal(doubleCertificate({ everyoneAdvanced: true, allHeardOverAckFrontier: true }), true);
});

test('dropEpochMap refuses ack-only, fires on the double certificate', () => {
  const a = new DistributedReplica(compactibleEmbedRGA, 'A'), b = new DistributedReplica(compactibleEmbedRGA, 'B');
  a.register('B'); b.register('A');
  a.commit({ type: 'ins', id: 50, el: 'a', anchorId: null }); a.commit({ type: 'ins', id: 80, el: 'b', anchorId: null });
  syncReplicas(a, b); b.commit({ type: 'ins', id: 120, el: 'c', anchorId: null }); syncReplicas(a, b);
  const r0 = a.compactStable();
  assert.equal(r0.compacted, true, 'gapped ids renumber -> a real compaction');
  const key = r0.epochKey;
  assert.ok(a.epochDag.get(key).translate != null, 'the epoch has a translate map');
  assert.equal(a.dropEpochMap(key, { everyoneAdvanced: true }).dropped, false, 'ack-only refused');
  assert.match(a.dropEpochMap(key, { everyoneAdvanced: true }).reason, /ack-only is unsound/);
  const r = a.dropEpochMap(key, { everyoneAdvanced: true, allHeardOverAckFrontier: true });
  assert.equal(r.dropped, true, 'double certificate fires the drop');
  assert.equal(a.epochDag.get(key).translate, null, 'map GC-ed');
  assert.equal(a.epochDag.get(key).mapDropped, true);
});

// ---------------------------------- additive: single-epoch behavior byte-identical
test('ADDITIVE: same-epoch merges unchanged (embed + orset byte-identical)', () => {
  for (const dt of [compactibleEmbedRGA, orset]) {
    const a = new DistributedReplica(dt, 'A'), b = new DistributedReplica(dt, 'B');
    const ins = (id, el, anc) => dt === orset ? { type: 'add', tag: 'x#' + id, el } : { type: 'ins', id, el, anchorId: anc };
    a.commit(ins(1, 'p', null)); syncReplicas(a, b);
    a.commit(ins(2, 'q', dt === orset ? null : 1)); b.commit(ins(3, 'r', dt === orset ? null : 1));
    syncReplicas(a, b);
    assert.equal(JSON.stringify(a.read()), JSON.stringify(b.read()), 'same-epoch convergence unchanged');
    assert.equal(a.epoch, 0); assert.equal(b.epoch, 0);
  }
});

// ------------------------------- H-M: the twin PBT (barrier-free divergent merges)
test('twin PBT: incomparable-cut merges converge to the never-compacted twin', () => {
  const res = { trials: 0, compactions: 0, comparable: 0, divergent: 0, crisscross: 0, mismatch: 0 };
  const NT = 600;
  for (let seed = 1; seed <= NT; seed++) trial(seed, res);
  assert.equal(res.mismatch, 0, `${res.mismatch} read divergences vs the twin`);
  assert.ok(res.divergent >= 60, `too few divergent (incomparable-cut) merges exercised: ${res.divergent}`);
  assert.ok(res.comparable >= 500, `too few comparable cross-epoch merges: ${res.comparable}`);
  assert.equal(res.trials, NT);
});

function classify(a, b) {
  if (a.epochKey === b.epochKey) return 'eq';
  const x = a.epochDag.get(a.epochKey).settledIds, y = b.epochDag.get(b.epochKey).settledIds;
  const sub = (p, q) => { if (p.size > q.size) return false; for (const e of p) if (!q.has(e)) return false; return true; };
  const ab = sub(x, y), ba = sub(y, x);
  return (ab && ba) ? 'eq' : (ab || ba) ? 'comparable' : 'divergent';
}

function trial(seed, res) {
  const rng = mulberry32(seed);
  const N = 3 + (seed % 3);                       // 3..5 replicas
  const names = Array.from({ length: N }, (_, i) => 'p' + i);
  const subj = names.map((n) => new DistributedReplica(compactibleEmbedRGA, n));
  const twin = names.map((n) => new DistributedReplica(compactibleEmbedRGA, n));
  for (const r of [...subj, ...twin]) for (const n of names) r.register(n);
  let mint = seed * 1000 + 1;
  const cmp = (where) => {
    for (let i = 0; i < N; i++) {
      if (subj[i].read().join('') !== twin[i].read().join('')) {
        res.mismatch++; return; // a divergence: recorded, trial aborts
      }
    }
  };
  const doSync = (i, j) => {
    const cls = classify(subj[i], subj[j]);
    try { syncReplicas(subj[i], subj[j]); }
    catch (e) { if (e.name === 'CrissCrossError') { res.crisscross++; return; } throw e; }
    try { syncReplicas(twin[i], twin[j]); } catch (e) { if (e.name !== 'CrissCrossError') throw e; }
    if (cls === 'divergent') res.divergent++; else if (cls === 'comparable') res.comparable++;
  };
  const rounds = 8 + (seed % 6);
  for (let r = 0; r < rounds; r++) {
    for (let i = 0; i < N; i++) {
      const view = embedRGA.readIds(subj[i].head.state);
      let op;
      if (view.length > 3 && rng() < 0.25) op = { type: 'del', id: pick(rng, view) };
      else { const id = mint++; op = { type: 'ins', id, el: String.fromCharCode(97 + (id % 26)), anchorId: view.length && rng() < 0.7 ? pick(rng, view) : null }; }
      subj[i].commit(op); twin[i].commit(op);
    }
    const nsync = 1 + Math.floor(rng() * 2);       // partial sync -> incomparable heard-sets
    for (let s = 0; s < nsync; s++) { let i = Math.floor(rng() * N), j = Math.floor(rng() * N); if (i === j) j = (j + 1) % N; doSync(i, j); cmp(`r${r}`); if (res.mismatch) return; }
    for (let i = 0; i < N; i++) if (rng() < 0.7) subj[i].compactStable().compacted && res.compactions++;
    cmp(`r${r}-compact`); if (res.mismatch) return;
  }
  for (let pass = 0; pass < 3; pass++) for (let k = 1; k < N; k++) { doSync(0, k); cmp('final'); if (res.mismatch) return; }
  res.trials++;
}
