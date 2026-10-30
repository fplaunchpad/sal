// E3: interacting causal gaps across replicas (issue 829).
//
// Two clients each hold a gap for the other: replica A has integrated (v14,
// behind a Skip) or parked (v13, pendingStructs) client B's struct b2 while
// B's earlier struct b1 is withheld, and replica B symmetrically holds a2
// while a1 is withheld. A relay replica C holds both gaps. All three edit on
// top of their partial states, relaying edits but never a1 or b1, then the
// withheld updates arrive last under several delivery protocols, and a
// fourth replica D joins late by syncing from a gap-bearing replica only.
//
// Oracle: a failure is counted only when every replica has received the same
// complete update set, no replica has pending structs or a pending delete
// set, exchange is quiescent, and the views or the reloaded fingerprints
// still differ. A quiescent exchange that leaves pending state is counted
// separately as "stuck" (the sync protocol failed to recover a gap).
//
// Usage: node e3-interacting-gaps.mjs [versions=14,13] [count=5000] [start=1]
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { load, rng, shuffle, permutations } from './lib.mjs';

const versions = (process.argv[2] || '14,13').split(',');
const count = Number(process.argv[3] || 5000);
const start = Number(process.argv[4] || 1);
const MAX_ROUNDS = 12;
const PROTOCOLS = ['direct-ab', 'direct-ba', 'direct-merged', 'direct-mixed', 'sync-only'];
const BASE_CHARS = 'xyzuvw';

const b64 = (u) => Buffer.from(u).toString('base64');
const sameBytes = (u, v) => Buffer.compare(Buffer.from(u), Buffer.from(v)) === 0;
const pick = (r, items) => items[Math.floor(r() * items.length)];

/** Positions in s whose left and right neighbours are both base characters or document ends. */
const baseBoundaryPositions = (s) => {
  const out = [];
  for (let p = 0; p <= s.length; p++) {
    const left = p === 0 || BASE_CHARS.includes(s[p - 1]);
    const right = p === s.length || BASE_CHARS.includes(s[p]);
    if (left && right) out.push(p);
  }
  return out;
};

/** Builds the mutual-gap state and the edit phase; deterministic in (seed, editCount). */
function build(L, gc, seed, editCount = null) {
  const r = rng(seed);
  const trace = [];
  const recs = [L.doc(1, { gc }), L.doc(2, { gc }), L.doc(3, { gc })];
  const [A, B, C] = recs;
  const docs = recs.map((x) => x.d);
  const apply = (rec, u, note) => { L.Y.applyUpdate(rec.d, u); if (note) trace.push(note); };
  const last = (rec) => rec.updates.at(-1);
  const emitted = (rec, f) => { const n = rec.updates.length; f(); assert.equal(rec.updates.length, n + 1, 'one local transaction emits one update'); return last(rec); };
  /** A local edit that may be a no-op (for example unbolding plain text) emits at most one update. */
  const maybeEmitted = (rec, f) => { const n = rec.updates.length; f(); assert.ok(rec.updates.length <= n + 1); return rec.updates.length === n + 1 ? last(rec) : null; };
  assert.equal(A.updates.length + B.updates.length + C.updates.length, 0, 'type access emits no update');

  // Shared base authored by C, delivered to A and B.
  const baseLen = 2 + Math.floor(r() * 4);
  const base = BASE_CHARS.slice(0, baseLen);
  const baseUpdates = [];
  baseUpdates.push(emitted(C, () => L.text(C.d).insert(0, base)));
  if (r() < 0.4) { const from = Math.floor(r() * baseLen), len = 1 + Math.floor(r() * (baseLen - from)); baseUpdates.push(emitted(C, () => L.text(C.d).format(from, len, { bold: true }))); trace.push({ op: 'base-format', from, len }); }
  for (const u of baseUpdates) { apply(A, u); apply(B, u); }
  trace.push({ op: 'base', base });

  // Client X makes x1 (withheld) and then x2 whose origins usually sit in the base.
  const firstThenSecond = (rec, c1, c2) => {
    const t = L.text(rec.d);
    const p1 = Math.floor(r() * (t.length + 1));
    const v1 = c1.repeat(1 + Math.floor(r() * 2));
    const u1 = emitted(rec, () => t.insert(p1, v1));
    trace.push({ op: 'insert', replica: rec.d.clientID, pos: p1, value: v1, withheld: true });
    const s = t.toString();
    let u2, eligible = true;
    if (r() < 0.3) {
      // Second struct is a format whose boundary items sit at base positions.
      const positions = baseBoundaryPositions(s).filter((p) => p < s.length);
      const from = positions.length && r() < 0.85 ? pick(r, positions) : Math.floor(r() * s.length);
      const len = 1 + Math.floor(r() * Math.min(2, s.length - from));
      const attrs = r() < 0.5 ? { italic: true } : { underline: true };
      u2 = emitted(rec, () => t.format(from, len, attrs));
      eligible = positions.includes(from);
      trace.push({ op: 'format', replica: rec.d.clientID, from, len, attrs, second: true, eligible });
    } else {
      const positions = baseBoundaryPositions(s);
      const p2 = r() < 0.85 ? pick(r, positions) : Math.floor(r() * (s.length + 1));
      const v2 = c2.repeat(1 + Math.floor(r() * 2));
      const attrs = r() < 0.3 ? { bold: true } : {};
      u2 = emitted(rec, () => t.insert(p2, v2, attrs));
      eligible = positions.includes(p2);
      trace.push({ op: 'insert', replica: rec.d.clientID, pos: p2, value: v2, attrs, second: true, eligible });
    }
    return { u1, u2, eligible };
  };
  const a = firstThenSecond(A, 'A', 'a');
  const b = firstThenSecond(B, 'B', 'b');

  // Cross delivery of the second structs only. C sometimes misses one.
  const deliveries = shuffle([
    () => apply(B, a.u2, { op: 'deliver', what: 'a2', to: 2 }),
    () => apply(C, a.u2, { op: 'deliver', what: 'a2', to: 3 }),
    () => apply(A, b.u2, { op: 'deliver', what: 'b2', to: 1 }),
    () => apply(C, b.u2, { op: 'deliver', what: 'b2', to: 3 }),
  ], r);
  const cGets = { a2: r() < 0.85, b2: r() < 0.85 };
  for (const f of deliveries) { const s = f.toString(); if ((s.includes("'a2', to: 3") && !cGets.a2) || (s.includes("'b2', to: 3") && !cGets.b2)) continue; f(); }
  const gapViews = docs.map(L.view), gapPending = docs.map(L.pending), gapSvs = docs.map(L.sv);
  // A replica that displays the foreign second struct while its state vector reports that client at clock 0.
  const svAt = (svText, client) => { const e = JSON.parse(svText).find((x) => x[0] === client); return e ? e[1] : 0; };
  const svHidesIntegrated = (gapViews[0].text.includes('b') && svAt(gapSvs[0], 2) === 0) || (gapViews[1].text.includes('a') && svAt(gapSvs[1], 1) === 0);

  // Edits on top of partial states. Targets prefer the foreign gap-after characters.
  const n = editCount ?? 1 + Math.floor(r() * 8);
  const foreign = ['b', 'a', 'ab'];
  for (let k = 0; k < n; k++) {
    const idx = r() < 0.4 ? 0 : r() < 0.67 ? 1 : 2;
    const rec = recs[idx], t = L.text(rec.d), s = t.toString(), len = s.length;
    const targets = [...s].map((ch, i) => (foreign[idx].includes(ch) ? i : -1)).filter((i) => i >= 0);
    const target = targets.length && r() < 0.6 ? pick(r, targets) : null;
    const choice = len === 0 ? 0 : Math.floor(r() * 4);
    const value = String.fromCharCode(0x30 + (k % 10));
    let u = null;
    if (choice < 2) {
      const pos = target !== null ? target + (r() < 0.5 ? 0 : 1) : Math.floor(r() * (len + 1));
      const attrs = r() < 0.5 ? {} : { bold: r() < 0.5, italic: r() < 0.5 };
      u = emitted(rec, () => t.insert(pos, value, attrs));
      trace.push({ op: 'insert', replica: rec.d.clientID, pos, value, attrs, targeted: target !== null });
    } else {
      const from = target !== null ? Math.max(0, target - (r() < 0.3 ? 1 : 0)) : Math.floor(r() * len);
      const length = 1 + Math.floor(r() * Math.min(3, len - from));
      if (choice === 2) { u = emitted(rec, () => t.delete(from, length)); trace.push({ op: 'delete', replica: rec.d.clientID, from, length, targeted: target !== null }); }
      else { const attrs = r() < 0.5 ? { bold: null } : { bold: true, italic: r() < 0.5 ? true : null }; u = maybeEmitted(rec, () => t.format(from, length, attrs)); trace.push({ op: 'format', replica: rec.d.clientID, from, length, attrs, targeted: target !== null, noop: u === null }); }
    }
    // Relay the edit just made to one or both other replicas; a1 and b1 are never relayed.
    if (u !== null) assert.ok(!sameBytes(u, a.u1) && !sameBytes(u, b.u1));
    if (u !== null && r() < 0.6) {
      const others = [0, 1, 2].filter((j) => j !== idx);
      const dests = r() < 0.5 ? [pick(r, others)] : others;
      for (const j of dests) apply(recs[j], u, { op: 'relay', from: rec.d.clientID, to: recs[j].d.clientID });
    }
  }
  const editViews = docs.map(L.view), editPending = docs.map(L.pending);
  return { recs, withheld: { a1: a.u1, b1: b.u1 }, eligible: { a: a.eligible, b: b.eligible }, cGets, trace, n, gapViews, gapPending, gapSvs, svHidesIntegrated, editViews, editPending };
}

/** Deduplicated set of every update any replica has emitted, in replica then emission order. */
const allUpdates = (recs) => { const seen = new Set(), all = []; for (const rec of recs) for (const u of rec.updates) { const k = b64(u); if (!seen.has(k)) { seen.add(k); all.push(u); } } return all; };

/** All-pairs state-vector anti-entropy until views, state vectors and update counts stop changing. */
function antiEntropy(L, recs, r, maxRounds = MAX_ROUNDS) {
  const docs = recs.map((x) => x.d);
  const total = () => recs.reduce((s, x) => s + x.updates.length, 0);
  const fingerprint = () => JSON.stringify([docs.map(L.key), docs.map(L.sv), docs.map(L.pending)]);
  let rounds = 0, quiescent = false, converged = null;
  for (; rounds < maxRounds; rounds++) {
    const before = total(), old = fingerprint();
    const order = r ? shuffle(docs.map((_, i) => i), r) : docs.map((_, i) => i);
    for (const i of order) for (const j of (r ? shuffle(order, r) : order)) if (i !== j) L.sync(docs[i], docs[j]);
    if (converged === null && L.equal(docs) && !docs.some((d) => { const p = L.pending(d); return p.structs || p.ds; })) converged = rounds + 1;
    if (total() === before && fingerprint() === old) { quiescent = true; break; }
  }
  return { rounds, quiescent, converged };
}

/** Closes a built state under one protocol, with the late joiner D, and returns the verdict. */
function close(L, gc, state, protocol, seed) {
  const r = rng((seed ^ 0x5bd1e995) >>> 0 || 7);
  const { recs, withheld } = state;
  const D = L.doc(4, { gc });
  const src = pick(r, recs);
  L.sync(src.d, D.d);
  const joinView = L.view(D.d), joinPending = L.pending(D.d), joinSv = L.sv(D.d);
  const all4 = [...recs, D];
  const docs = all4.map((x) => x.d);
  const out = { protocol, joinFrom: src.d.clientID, joinView, joinPending, joinSv, joinSvMismatch: joinSv !== L.sv(src.d) };
  if (protocol !== 'sync-only') {
    // Identical complete update set to every replica; the withheld pair last in every order.
    let deliveryQuiescent = false, rounds = 0;
    for (; rounds < MAX_ROUNDS; rounds++) {
      const all = allUpdates(all4), before = all.length;
      const rest = all.filter((u) => !sameBytes(u, withheld.a1) && !sameBytes(u, withheld.b1));
      assert.equal(rest.length, all.length - 2, 'the withheld updates occur once each in the complete set');
      for (const rec of all4) {
        const ordered = shuffle(rest, r), chunks = [];
        for (let i = 0; i < ordered.length;) { const size = 1 + Math.floor(r() * 3); chunks.push(ordered.slice(i, i + size)); i += size; }
        let tail;
        if (protocol === 'direct-ab') tail = [[withheld.a1], [withheld.b1]];
        else if (protocol === 'direct-ba') tail = [[withheld.b1], [withheld.a1]];
        else if (protocol === 'direct-merged') tail = [r() < 0.5 ? [withheld.a1, withheld.b1] : [withheld.b1, withheld.a1]];
        else { const mixA = [withheld.a1, ...shuffle(rest, r).slice(0, 1 + Math.floor(r() * 2))], mixB = [withheld.b1, ...shuffle(rest, r).slice(0, 1 + Math.floor(r() * 2))]; tail = r() < 0.5 ? [shuffle(mixA, r), shuffle(mixB, r)] : [shuffle(mixB, r), shuffle(mixA, r)]; }
        for (const chunk of [...chunks, ...tail]) { const u = chunk.length === 1 ? chunk[0] : L.Y.mergeUpdates(chunk); L.Y.applyUpdate(rec.d, u); if (r() < 0.3) L.Y.applyUpdate(rec.d, u); }
      }
      if (allUpdates(all4).length === before) { deliveryQuiescent = true; break; }
    }
    out.deliveryRounds = rounds; out.deliveryQuiescent = deliveryQuiescent;
    out.delivered = docs.map(L.view); out.deliveredPending = docs.map(L.pending);
    out.mismatchAfterDelivery = !L.equal(docs);
    out.unresolvedAfterDelivery = out.deliveredPending.some((p) => p.structs || p.ds);
  }
  Object.assign(out, antiEntropy(L, all4, r));
  const v = L.verdict(docs);
  out.final = docs.map(L.view); out.verdict = v;
  out.clientIDs = docs.map((d) => d.clientID);
  assert.deepEqual(out.clientIDs, [1, 2, 3, 4], 'clientIDs unchanged');
  out.failure = out.quiescent && !v.unresolved && (v.divergence || v.reloadDivergence);
  out.stuck = out.quiescent && v.unresolved;
  out.nonquiescent = !out.quiescent || out.deliveryQuiescent === false;
  out.svMismatch = out.quiescent && !v.unresolved && v.svs !== 1;
  out.interesting = out.failure || out.stuck || out.nonquiescent || out.svMismatch;
  for (const d of docs) d.destroy();
  return out;
}

function trial(L, gc, seed, protocol, editCount = null) {
  const state = build(L, gc, seed, editCount);
  const closing = close(L, gc, state, protocol, seed);
  const { recs, ...rest } = state;
  return { seed, gc, ...rest, ...closing };
}

/** Exhaustive delivery-order enumeration of a fixed six-update case with one deterministic edit per replica per step. */
function enumerate(L, gc, protocol) {
  const counts = { trials: 0, failures: 0, stuck: 0, nonquiescent: 0, svMismatch: 0, mismatchAfterDelivery: 0, unresolvedAfterDelivery: 0, joinPending: 0, gapObserved: 0, findings: [], transients: [] };
  const names = ['a1', 'a2', 'b1', 'b2', 'c1', 'c2'];
  for (const perm of permutations([0, 1, 2, 3, 4, 5])) {
    const recs = [L.doc(1, { gc }), L.doc(2, { gc }), L.doc(3, { gc })];
    const [A, B, C] = recs;
    const docs = recs.map((x) => x.d);
    L.text(C.d).insert(0, 'xyz');
    const base = C.updates.at(-1);
    L.Y.applyUpdate(A.d, base); L.Y.applyUpdate(B.d, base);
    L.text(A.d).insert(3, 'A'); const a1 = A.updates.at(-1);
    L.text(A.d).insert(1, 'a'); const a2 = A.updates.at(-1);
    L.text(B.d).insert(0, 'B'); const b1 = B.updates.at(-1);
    L.text(B.d).insert(3, 'b'); const b2 = B.updates.at(-1);
    L.text(C.d).format(1, 1, { bold: true }); const c1 = C.updates.at(-1);
    L.text(C.d).delete(2, 1); const c2 = C.updates.at(-1);
    const updates = [a1, a2, b1, b2, c1, c2], authors = [0, 0, 1, 1, 2, 2];
    const trace = [];
    let gapObserved = false;
    // D joins after the third delivery by syncing from one replica, then hears nothing until closing.
    const D = L.doc(4, { gc });
    const src = recs[perm.reduce((x, y) => x + y, 0) % 3];
    let joinPending = null;
    for (let k = 0; k < perm.length; k++) {
      if (k === 3) { L.sync(src.d, D.d); joinPending = L.pending(D.d); trace.push({ step: k, join: 4, from: src.d.clientID, text: L.text(D.d).toString(), pending: joinPending }); }
      const which = perm[k];
      for (let j = 0; j < 3; j++) if (j !== authors[which]) L.Y.applyUpdate(docs[j], updates[which]);
      trace.push({ step: k, deliver: names[which] });
      for (let j = 0; j < 3; j++) {
        const t = L.text(docs[j]), len = t.length, kind = (k + j) % 3, pos = (k * 5 + j * 3) % (len + 1);
        const n = recs[j].updates.length;
        if (kind === 0 || len === 0) { t.insert(pos, String.fromCharCode(0x30 + k * 3 + j)); trace.push({ step: k, replica: j + 1, op: 'insert', pos }); }
        else if (kind === 1) { t.delete(pos % len, 1); trace.push({ step: k, replica: j + 1, op: 'delete', pos: pos % len }); }
        else { t.format(pos % len, 1, { bold: k % 2 === 0 ? true : null }); trace.push({ step: k, replica: j + 1, op: 'format', pos: pos % len }); }
        if (recs[j].updates.length > n) { const u = recs[j].updates.at(-1); for (let i = 0; i < 3; i++) if (i !== j) L.Y.applyUpdate(docs[i], u); }
      }
      // A gap at B: a2 integrated (v14) or parked (v13) while a1 is still undelivered.
      const sB = L.text(B.d).toString();
      if (!gapObserved && perm.indexOf(1) <= k && perm.indexOf(0) > k && (sB.includes('a') !== sB.includes('A') || L.pending(B.d).structs)) gapObserved = true;
    }
    const all4 = [...recs, D], docs4 = all4.map((x) => x.d);
    const out = { perm: perm.map((i) => names[i]), gc, protocol, trace, joinFrom: src.d.clientID, joinPending, gapObserved };
    if (protocol !== 'sync-only') {
      let deliveryQuiescent = false;
      for (let round = 0; round < MAX_ROUNDS; round++) {
        const all = allUpdates(all4), before = all.length;
        const rest = all.filter((u) => !sameBytes(u, a1) && !sameBytes(u, b1));
        const tail = protocol === 'direct-ab' ? [a1, b1] : protocol === 'direct-ba' ? [b1, a1] : [L.Y.mergeUpdates([a1, b1])];
        for (const rec of all4) for (const u of [...rest, ...tail]) L.Y.applyUpdate(rec.d, u);
        if (allUpdates(all4).length === before) { deliveryQuiescent = true; break; }
      }
      out.deliveryQuiescent = deliveryQuiescent;
      out.mismatchAfterDelivery = !L.equal(docs4);
      out.delivered = docs4.map(L.view);
      out.deliveredPending = docs4.map(L.pending);
      out.deliveredSvs = docs4.map(L.sv);
      out.unresolvedAfterDelivery = out.deliveredPending.some((p) => p.structs || p.ds);
    }
    Object.assign(out, antiEntropy(L, all4, null));
    const v = L.verdict(docs4);
    out.final = docs4.map(L.view); out.verdict = v;
    assert.deepEqual(docs4.map((d) => d.clientID), [1, 2, 3, 4]);
    out.failure = out.quiescent && !v.unresolved && (v.divergence || v.reloadDivergence);
    out.stuck = out.quiescent && v.unresolved;
    out.nonquiescent = !out.quiescent || out.deliveryQuiescent === false;
    out.svMismatch = out.quiescent && !v.unresolved && v.svs !== 1;
    counts.trials++;
    for (const k of ['failures', 'stuck', 'nonquiescent', 'svMismatch', 'mismatchAfterDelivery', 'unresolvedAfterDelivery', 'joinPending', 'gapObserved']) {
      const flag = k === 'failures' ? out.failure : k === 'joinPending' ? joinPending.structs || joinPending.ds : out[k];
      if (flag) counts[k]++;
    }
    if (out.failure || out.stuck || out.nonquiescent || out.svMismatch) { if (counts.findings.length < 10) counts.findings.push(out); console.log(JSON.stringify({ event: 'ENUM-FINDING', version: L.pkg.version, ...out })); }
    else if (out.mismatchAfterDelivery || out.unresolvedAfterDelivery) { if (counts.transients.length < 10) counts.transients.push(out); console.log(JSON.stringify({ event: 'ENUM-TRANSIENT', version: L.pkg.version, ...out })); }
    for (const d of docs4) d.destroy();
  }
  return counts;
}

/**
 * Fixed sequence in which a replica holding a gap receives every update exactly once, the withheld
 * struct last, and may keep pending structs: the parked update's recorded missing client is not the
 * client that fills the gap, so the fill triggers no retry. See e3-stuck-pending-replay.mjs.
 */
function stuckPendingScenario(L, gc) {
  const { Y } = L;
  const A = L.doc(1, { gc }), B = L.doc(2, { gc }), C = L.doc(3, { gc });
  L.text(C.d).insert(0, 'xyz'); const base = C.updates.at(-1);
  Y.applyUpdate(A.d, base); Y.applyUpdate(B.d, base);
  L.text(A.d).insert(0, 'A'); const a1 = A.updates.at(-1);
  L.text(A.d).insert(3, 'a'); const a2 = A.updates.at(-1);
  Y.applyUpdate(B.d, a1); Y.applyUpdate(B.d, a2);
  L.text(B.d).insert(0, 'q'); const q = B.updates.at(-1);
  Y.applyUpdate(A.d, q);
  A.d.transact(() => { L.text(A.d).insert(6, 'k'); L.text(A.d).insert(1, 'w'); }); const kw = A.updates.at(-1);
  Y.applyUpdate(B.d, kw);
  const seq = [a2, q, kw, a1];
  for (const u of seq) Y.applyUpdate(C.d, u);
  const once = { text: L.text(C.d).toString(), pending: L.pending(C.d), missing: C.d.store.pendingStructs ? [...C.d.store.pendingStructs.missing.entries()] : null };
  const stuck = once.pending.structs || once.text !== L.text(A.d).toString();
  for (const u of seq) Y.applyUpdate(C.d, u);
  const twice = { text: L.text(C.d).toString(), pending: L.pending(C.d) };
  const S = L.doc(9, { gc }); for (const u of [base, ...seq]) Y.applyUpdate(S.d, u); L.sync(A.d, S.d);
  const synced = { text: L.text(S.d).toString(), pending: L.pending(S.d) };
  const v = L.verdict([A.d, B.d, C.d, S.d]);
  for (const x of [A, B, C, S]) x.d.destroy();
  return { gc, othersText: 'qwAxyazk', afterOnePass: once, stuckAfterOnePass: stuck, afterSecondPass: twice, afterSvSync: synced, finalVerdict: v };
}

function controls(L) {
  const { Y } = L;
  // Oracle controls: a missing insert, a missing format, and a reload mismatch must be detected.
  { const a = new Y.Doc(), b = new Y.Doc(); L.text(a).insert(0, 'x'); assert.equal(L.equal([a, b]), false); Y.applyUpdate(b, Y.encodeStateAsUpdate(a)); assert.equal(L.equal([a, b]), true); L.text(a).format(0, 1, { bold: true }); assert.equal(L.equal([a, b]), false); Y.applyUpdate(b, Y.encodeStateAsUpdate(a)); assert.equal(L.equal([a, b]), true); a.destroy(); b.destroy(); }
  { const a = new Y.Doc(), b = new Y.Doc(); L.text(a).insert(0, 'xy'); Y.applyUpdate(b, Y.encodeStateAsUpdate(a)); L.text(b).delete(0, 1); let v = L.verdict([a, b]); assert.equal(v.divergence, true); assert.equal(v.reloadDivergence, true); L.text(b).insert(0, 'z'); v = L.verdict([a, b]); assert.equal(v.svs, 2); a.destroy(); b.destroy(); }
  // Mechanism controls: the mutual gap with no edits shows the version-specific partial state, then converges.
  for (const gc of [false, true]) {
    const state = build(L, gc, 829, 0);
    const [vA, vB, vC] = state.gapViews, [pA, pB] = state.gapPending;
    assert.ok(!vA.text.includes('B') && !vB.text.includes('A'), 'withheld content absent');
    if (L.version === '14') { assert.ok(vA.text.includes('b') || state.trace.some((t) => t.second && t.op === 'format'), 'v14 integrates b2 behind a Skip'); assert.equal(pA.structs, false); assert.equal(pB.structs, false); }
    else { assert.ok(!vA.text.includes('b') && !vB.text.includes('a'), 'v13 parks the successor'); assert.equal(pA.structs, true); assert.equal(pB.structs, true); }
    for (const protocol of PROTOCOLS) { const st = build(L, gc, 829, 0); const c = close(L, gc, st, protocol, 829); assert.equal(c.failure, false); assert.equal(c.stuck, false); assert.equal(c.quiescent, true); assert.equal(c.verdict.svs, 1); }
    for (const x of state.recs) x.d.destroy();
  }
}

const summary = { experiment: 'E3 interacting gaps', node: process.version, start, count, protocols: PROTOCOLS, started: new Date().toISOString(), versions: [] };
for (const version of versions) {
  const L = await load(version);
  controls(L);
  const V = { package: L.pkg.name, version: L.pkg.version, random: [], enumeration: [], stuckPendingScenario: [], findings: [], transients: [] };
  console.log(JSON.stringify({ event: 'START', version: L.pkg.version, count, start }));
  for (const gc of [false, true]) { const r = stuckPendingScenario(L, gc); V.stuckPendingScenario.push(r); console.log(JSON.stringify({ event: 'STUCK-SCENARIO', version: L.pkg.version, ...r })); }
  for (const gc of [false, true]) for (const protocol of PROTOCOLS) {
    const g = { gc, protocol, trials: 0, failures: 0, stuck: 0, nonquiescent: 0, svMismatch: 0, mismatchAfterDelivery: 0, unresolvedAfterDelivery: 0, joinPending: 0, joinSvMismatch: 0, skipEligibleBoth: 0, cMissedOne: 0, gapSkipVisible: 0, gapPendingAny: 0, svHidesIntegrated: 0, maxSyncRounds: 0, syncRoundsToConverge: {} };
    for (let k = 0; k < count; k++) {
      const seed = Math.imul(start + k, 0x9e3779b1) >>> 0;
      const t = trial(L, gc, seed, protocol);
      g.trials++;
      if (t.failure) g.failures++;
      if (t.stuck) g.stuck++;
      if (t.nonquiescent) g.nonquiescent++;
      if (t.svMismatch) g.svMismatch++;
      if (t.mismatchAfterDelivery) g.mismatchAfterDelivery++;
      if (t.unresolvedAfterDelivery) g.unresolvedAfterDelivery++;
      if (t.joinPending.structs || t.joinPending.ds) g.joinPending++;
      if (t.joinSvMismatch) g.joinSvMismatch++;
      if (t.eligible.a && t.eligible.b) g.skipEligibleBoth++;
      if (!t.cGets.a2 || !t.cGets.b2) g.cMissedOne++;
      if (t.gapViews[0].text.includes('b') || t.gapViews[1].text.includes('a')) g.gapSkipVisible++;
      if (t.gapPending.some((p) => p.structs || p.ds)) g.gapPendingAny++;
      if (t.svHidesIntegrated) g.svHidesIntegrated++;
      g.maxSyncRounds = Math.max(g.maxSyncRounds, t.rounds);
      if (t.converged !== null) g.syncRoundsToConverge[t.converged] = (g.syncRoundsToConverge[t.converged] || 0) + 1;
      if (t.interesting) { if (V.findings.length < 20) V.findings.push(t); console.log(JSON.stringify({ event: 'FINDING', version: L.pkg.version, ...t })); }
      else if (t.mismatchAfterDelivery || t.unresolvedAfterDelivery) { if (V.transients.length < 20) V.transients.push(t); console.log(JSON.stringify({ event: 'TRANSIENT', version: L.pkg.version, ...t })); }
      if (k % 1000 === 999) console.log(JSON.stringify({ event: 'PROGRESS', version: L.pkg.version, ...g }));
    }
    V.random.push(g);
    console.log(JSON.stringify({ event: 'GROUP', version: L.pkg.version, ...g }));
  }
  for (const gc of [false, true]) for (const protocol of ['direct-ab', 'direct-ba', 'direct-merged', 'sync-only']) {
    const e = enumerate(L, gc, protocol);
    const { findings, transients, ...counts } = e;
    V.enumeration.push({ gc, protocol, ...counts });
    V.findings.push(...findings);
    V.transients.push(...transients);
    console.log(JSON.stringify({ event: 'ENUM', version: L.pkg.version, gc, protocol, ...counts }));
  }
  summary.versions.push(V);
}
summary.finished = new Date().toISOString();
writeFileSync(new URL('e3-interacting-gaps-results.json', import.meta.url), JSON.stringify(summary, null, 2) + '\n');
console.log(JSON.stringify({ event: 'DONE', versions: summary.versions.map((V) => ({ version: V.version, stuckAfterOnePass: V.stuckPendingScenario.map((r) => r.stuckAfterOnePass), random: V.random.map((g) => [g.gc, g.protocol, g.trials, g.failures, g.stuck, g.nonquiescent]), enumeration: V.enumeration.map((g) => [g.gc, g.protocol, g.trials, g.failures, g.stuck, g.nonquiescent]) })) }));
