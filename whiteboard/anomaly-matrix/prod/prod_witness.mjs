// prod_witness.mjs — anomaly witnesses against PRODUCTION sequence CRDTs.
// Rows: Yjs (YATA), Automerge (RGA-lineage), Loro (Fugue-lineage), list-positions
// (Weidner's Fugue reference). These are op-based/state-sync libraries, driven by
// SCENARIOS (not the ternary-merge harness):
//   S1 sequential naive-list conformance (incl. delete-middle witness + 200-script PBT)
//   S2 forward interleaving   (concurrent runs, each char after own previous)
//   S3 backward interleaving  (concurrent runs, every char at the same fixed index)
//   S4 pairwise display stability + strong-list acyclicity over all recorded reads
//   S5 tombstone retention (serialized size / internal structs after delete-all)
import * as Y from 'yjs';
import { next as AM } from '@automerge/automerge';
import { LoroDoc } from 'loro-crdt';
import { AbsList } from 'list-positions';

// ---------------------------------------------------------------- checkers
function contiguous(text, run) {
  const idx = [...run].map(c => text.indexOf(c)).filter(i => i >= 0).sort((a, b) => a - b);
  if (idx.length !== run.length) return false;
  return idx[idx.length - 1] - idx[0] === idx.length - 1;
}
class Obs {
  constructor() { this.m = new Map(); }
  display(text) {
    for (let i = 0; i < text.length; i++)
      for (let j = i + 1; j < text.length; j++) {
        const x = text[i], y = text[j];
        const k = x < y ? x + y : y + x;
        if (!this.m.has(k)) this.m.set(k, new Set());
        this.m.get(k).add(x === k[0] ? '<' : '>');
      }
  }
  flips() { return [...this.m.entries()].filter(([, s]) => s.size > 1).map(([k]) => k); }
  acyclic() {
    const g = new Map();
    for (const [k, s] of this.m) {
      if (s.size !== 1) continue;
      const [x, y] = s.has('<') ? [k[0], k[1]] : [k[1], k[0]];
      if (!g.has(x)) g.set(x, new Set());
      g.get(x).add(y);
    }
    const color = new Map();
    const dfs = v => {
      color.set(v, 1);
      for (const w of g.get(v) ?? []) {
        if (color.get(w) === 1) return false;
        if (!color.has(w) && !dfs(w)) return false;
      }
      color.set(v, 2); return true;
    };
    for (const v of g.keys()) if (!color.has(v) && !dfs(v)) return false;
    return true;
  }
}

// ---------------------------------------------------------------- adapters
// Each: fork(baseText) -> {A, B}; ins(doc,i,ch); del(doc,i); read(doc);
// syncAB({A,B}) -> merged text as seen by both (assert equal).
const Adapters = {
  yjs: {
    fork(base) {
      const b = new Y.Doc(); b.getText('t').insert(0, base);
      const A = new Y.Doc(), B = new Y.Doc();
      Y.applyUpdate(A, Y.encodeStateAsUpdate(b));
      Y.applyUpdate(B, Y.encodeStateAsUpdate(b));
      return { A, B };
    },
    single() { const d = new Y.Doc(); return d; },
    ins(d, i, ch) { d.getText('t').insert(i, ch); },
    del(d, i) { d.getText('t').delete(i, 1); },
    read(d) { return d.getText('t').toString(); },
    sync(p) {
      const ua = Y.encodeStateAsUpdate(p.A), ub = Y.encodeStateAsUpdate(p.B);
      Y.applyUpdate(p.A, ub); Y.applyUpdate(p.B, ua);
      const ra = this.read(p.A), rb = this.read(p.B);
      if (ra !== rb) throw new Error(`yjs diverged: ${ra} vs ${rb}`);
      return ra;
    },
    graves(d) {  // walk struct store: count items, deleted items, bytes
      let n = 0, dead = 0;
      d.store.clients.forEach(arr => arr.forEach(it => {
        n++; if (it.deleted) dead++;
      }));
      return { structs: n, deleted: dead, bytes: Y.encodeStateAsUpdate(d).byteLength };
    },
  },
  automerge: {
    fork(base) {
      let b = AM.from({ t: '' });
      b = AM.change(b, d => AM.splice(d, ['t'], 0, 0, base));
      return { A: AM.clone(b), B: AM.clone(b) };
    },
    single() { return AM.from({ t: '' }); },
    ins(d, i, ch) { return AM.change(d, dd => AM.splice(dd, ['t'], i, 0, ch)); },
    del(d, i) { return AM.change(d, dd => AM.splice(dd, ['t'], i, 1)); },
    read(d) { return d.t; },
    sync(p) {
      const M1 = AM.merge(AM.clone(p.A), AM.clone(p.B));
      const M2 = AM.merge(AM.clone(p.B), AM.clone(p.A));
      if (M1.t !== M2.t) throw new Error(`automerge asym: ${M1.t} vs ${M2.t}`);
      p.A = M1; p.B = M2;
      return M1.t;
    },
    graves(d) {
      return { changes: AM.getAllChanges(d).length, bytes: AM.save(d).byteLength };
    },
  },
  loro: {
    _pid: 1,
    fork(base) {
      const b = new LoroDoc(); b.setPeerId(BigInt(this._pid++));
      b.getText('t').insert(0, base); b.commit();
      const snap = b.export({ mode: 'snapshot' });
      const A = new LoroDoc(); A.setPeerId(BigInt(this._pid++)); A.import(snap);
      const B = new LoroDoc(); B.setPeerId(BigInt(this._pid++)); B.import(snap);
      return { A, B };
    },
    single() { const d = new LoroDoc(); d.setPeerId(BigInt(this._pid++)); return d; },
    ins(d, i, ch) { d.getText('t').insert(i, ch); d.commit(); },
    del(d, i) { d.getText('t').delete(i, 1); d.commit(); },
    read(d) { return d.getText('t').toString(); },
    sync(p) {
      p.A.import(p.B.export({ mode: 'update' }));
      p.B.import(p.A.export({ mode: 'update' }));
      const ra = this.read(p.A), rb = this.read(p.B);
      if (ra !== rb) throw new Error(`loro diverged: ${ra} vs ${rb}`);
      return ra;
    },
    graves(d) { return { bytes: d.export({ mode: 'snapshot' }).byteLength }; },
  },
  'list-positions': {
    // AbsList: self-contained positions (Fugue tree paths). "Sync" = union of
    // (pos, value) entries minus deletions, exactly the library's intended
    // collaboration mode (broadcast set/delete of AbsPositions).
    fork(base) {
      const mk = id => new AbsList();  // replicaID is inside Order; defaults random
      const b = new AbsList();
      for (const ch of base) b.insertAt(b.length, ch);
      const entries = [...b.entries()];
      const A = new AbsList(), B = new AbsList();
      for (const [pos, v] of entries) { A.set(pos, v); B.set(pos, v); }
      return { A, B, deleted: [] };
    },
    single() { return { l: new AbsList(), deleted: [] }; },
    ins(d, i, ch) { (d.l ?? d).insertAt(i, ch); },
    del(d, i) {
      const l = d.l ?? d;
      const pos = l.positionAt(i);
      (d.deleted ?? []).push?.(pos);
      l.delete(pos);
    },
    read(d) { return [...(d.l ?? d).values()].join(''); },
    sync(p) {
      // exchange all entries + deletions
      const ea = [...p.A.entries()], eb = [...p.B.entries()];
      for (const [pos, v] of eb) p.A.set(pos, v);
      for (const [pos, v] of ea) p.B.set(pos, v);
      for (const pos of p.deleted) { p.A.delete(pos); p.B.delete(pos); }
      const ra = this.read({ l: p.A }), rb = this.read({ l: p.B });
      if (ra !== rb) throw new Error(`list-positions diverged: ${ra} vs ${rb}`);
      return ra;
    },
    graves(d) {
      const l = d.l ?? d;
      return { savedChars: JSON.stringify(l.save()).length };
    },
  },
};

// ---------------------------------------------------------------- scenarios
const A_RUN = 'DEF', B_RUN = 'xyz';   // unique chars; base uses '[' ']'

function s1_sequential(name, ad) {
  // delete-middle witness: build "bac" by anchored inserts, delete 'a' -> want "bc"
  let d = ad.single();
  const step = (f, ...args) => { const r = f.call(ad, d, ...args); if (r) d = r; };
  step(ad.ins, 0, 'a'); step(ad.ins, 0, 'b'); step(ad.ins, 2, 'c'); // "bac"
  const before = ad.read(d.l ? d : d);
  step(ad.del, 1);                                                   // del 'a'
  const after = ad.read(d.l ? d : d);
  const okW = before === 'bac' && after === 'bc';
  // 200-script PBT vs a plain JS array reference
  let fails = 0, firstFail = null;
  for (let t = 0; t < 200; t++) {
    let doc = ad.single(); const ref = [];
    let rng = 987654321 + t * 2654435761;
    const rnd = n => { rng ^= rng << 13; rng ^= rng >>> 17; rng ^= rng << 5; rng >>>= 0; return rng % n; };
    for (let k = 0; k < 10; k++) {
      if (ref.length > 0 && rnd(100) < 35) {
        const i = rnd(ref.length);
        const r = ad.del.call(ad, doc, i); if (r) doc = r;
        ref.splice(i, 1);
      } else {
        const i = rnd(ref.length + 1);
        const ch = String.fromCharCode(97 + (t + k) % 26);
        const r = ad.ins.call(ad, doc, i, ch); if (r) doc = r;
        ref.splice(i, 0, ch);
      }
      const got = ad.read(doc);
      if (got !== ref.join('')) { fails++; if (!firstFail) firstFail = { t, k, got, want: ref.join('') }; break; }
    }
  }
  console.log(`[${name}] S1 seq: witness bac->${after} ${okW ? 'PASS' : 'FAIL'}; PBT fails ${fails}/200${firstFail ? ' first=' + JSON.stringify(firstFail) : ''}`);
  return okW && fails === 0;
}

function s2s3_interleave(name, ad, backward, trials = 30) {
  // base "[ ]": runs typed between '[' and ']'. forward: each char after previous
  // (index grows); backward: every char at the same index (right after '[').
  const outcomes = new Map(); let inter = 0;
  const obs = new Obs();
  for (let t = 0; t < trials; t++) {
    const p = ad.fork('[]');
    const typeRun = (doc, run) => {
      for (let i = 0; i < run.length; i++) {
        const at = backward ? 1 : 1 + i;
        const r = ad.ins.call(ad, doc === 'A' ? p.A : p.B, at, run[i]);
        if (r) { if (doc === 'A') p.A = r; else p.B = r; }
        obs.display(ad.read(doc === 'A' ? p.A : p.B));
      }
    };
    typeRun('A', A_RUN); typeRun('B', B_RUN);
    const m = ad.sync.call(ad, p);
    obs.display(m);
    const ok = contiguous(m, A_RUN) && contiguous(m, B_RUN);
    if (!ok) inter++;
    outcomes.set(m, (outcomes.get(m) ?? 0) + 1);
  }
  const lbl = backward ? 'S3 bwd' : 'S2 fwd';
  console.log(`[${name}] ${lbl}: interleaved ${inter}/${trials}; outcomes: ${[...outcomes.entries()].map(([k, v]) => `"${k}"x${v}`).join(' ')}`);
  return { inter, trials, outcomes, obs };
}

// Fugue, Appendix A.1.9 / Proposition 16: Yjs backward interleaving needs
// three replicas and an asymmetric causal shape. Replica 1 first observes b
// from replica 3 and then inserts a before it; replica 2 concurrently inserts
// x into the empty document. After all updates arrive, x splits the run ab.
function yjsThreeReplicaBackwardWitness() {
  const docs = [new Y.Doc(), new Y.Doc(), new Y.Doc()];
  docs.forEach((d, i) => { d.clientID = i + 1; });
  const [d1, d2, d3] = docs;

  d3.getText('t').insert(0, 'b');
  Y.applyUpdateV2(d1, Y.encodeStateAsUpdateV2(d3));
  d1.getText('t').insert(0, 'a');
  d2.getText('t').insert(0, 'x');

  const updates = docs.map(d => Y.encodeStateAsUpdateV2(d));
  for (const d of docs) for (const u of updates) Y.applyUpdateV2(d, u);
  const reads = docs.map(d => d.getText('t').toString());
  if (!reads.every(r => r === 'axb'))
    throw new Error(`expected converged axb, got ${reads.join(', ')}`);
  console.log(`[yjs] S3 directed 3-replica: "ab" split as "axb" PASS`);
}

function s4_stability(name, ad, trials = 30) {
  // two-epoch scenario with deletes; record every read everywhere; check flips+cycles
  let flips = 0, cycles = 0; let firstFlip = null;
  for (let t = 0; t < trials; t++) {
    const obs = new Obs();
    const p = ad.fork('mg');            // base: m, g
    const rd = w => { obs.display(ad.read(w === 'A' ? p.A : p.B)); };
    let r = ad.ins.call(ad, p.A, 0, 'x'); if (r) p.A = r; rd('A');   // A: x before m
    r = ad.del.call(ad, p.A, 2); if (r) p.A = r; rd('A');            // A: del g ("xm")
    r = ad.ins.call(ad, p.B, 2, 'y'); if (r) p.B = r; rd('B');       // B: y after g
    r = ad.del.call(ad, p.B, 0); if (r) p.B = r; rd('B');            // B: del m ("gy")
    let m = ad.sync.call(ad, p); obs.display(m);
    // epoch 2: concurrent inserts at both ends + delete
    r = ad.ins.call(ad, p.A, 0, 'p'); if (r) p.A = r; rd('A');
    r = ad.ins.call(ad, p.B, ad.read(p.B).length, 'q'); if (r) p.B = r; rd('B');
    m = ad.sync.call(ad, p); obs.display(m);
    if (obs.flips().length) { flips++; if (!firstFlip) firstFlip = obs.flips(); }
    if (!obs.acyclic()) cycles++;
  }
  console.log(`[${name}] S4 stability: pair-flip trials ${flips}/${trials}${firstFlip ? ' e.g. ' + firstFlip : ''}; cycle trials ${cycles}/${trials}`);
  return { flips, cycles, trials };
}

function s5_graves(name, ad) {
  let d = ad.single();
  const step = (f, ...args) => { const r = f.call(ad, d, ...args); if (r) d = r; };
  const N = 20;
  for (let i = 0; i < N; i++) step(ad.ins, i, String.fromCharCode(97 + i));
  const full = ad.graves.call(ad, d);
  for (let i = 0; i < N; i++) step(ad.del, 0);
  const empty = ad.graves.call(ad, d);
  console.log(`[${name}] S5 graves: after ${N} ins: ${JSON.stringify(full)}; after deleting ALL: ${JSON.stringify(empty)} (text now "${ad.read(d)}")`);
  // fresh empty doc for byte comparison
  let d0 = ad.single();
  const fresh = ad.graves.call(ad, d0);
  console.log(`[${name}]    fresh empty doc: ${JSON.stringify(fresh)}`);
}

// ---------------------------------------------------------------- main
for (const [name, ad] of Object.entries(Adapters)) {
  console.log('='.repeat(72));
  try { s1_sequential(name, ad); } catch (e) { console.log(`[${name}] S1 ERROR: ${e.message}`); }
  try { s2s3_interleave(name, ad, false); } catch (e) { console.log(`[${name}] S2 ERROR: ${e.message}`); }
  try { s2s3_interleave(name, ad, true); } catch (e) { console.log(`[${name}] S3 ERROR: ${e.message}`); }
  try { s4_stability(name, ad); } catch (e) { console.log(`[${name}] S4 ERROR: ${e.message}`); }
  try { s5_graves(name, ad); } catch (e) { console.log(`[${name}] S5 ERROR: ${e.message}`); }
}

yjsThreeReplicaBackwardWitness();
