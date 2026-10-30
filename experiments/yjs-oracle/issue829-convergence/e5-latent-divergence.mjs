// E5: latent divergence after an apparent convergence.
//
// Mechanism. Two replicas can display the same text and formatting and still
// hold different internal state (a Skip left in the store, a pending delete
// set, items merged differently) that surfaces only under later edits. The
// three gap families of search.mjs are run with four replicas and up to
// twenty edits on the gap-bearing ones; after the complete set is delivered
// and state vectors exchanged, every replica makes three more concurrent
// edits, the set is closed again, and the final views, re-encoded states,
// state vectors, pending stores and (v14) skip stores are compared.
// Usage: node e5-latent-divergence.mjs <13|14> [seeds]

import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { load, rng, shuffle } from './lib.mjs';

const version = process.argv[2] ?? '14';
const seeds = Number(process.argv[3] ?? 5000);
const L = await load(version);
const { Y, text } = L;

const skipsLeft = (d) => (d.store.skips ? [...d.store.skips.clients.keys()].length : 0);

function group(n, gc) {
  const all = [], seen = new Set(), docs = [], updates = [];
  for (let i = 0; i < n; i++) {
    const d = new Y.Doc({ gc }); d.clientID = 100 + i; text(d);
    const us = [];
    d.on('update', (u, _o, _d, tr) => { if (tr.local) us.push(u); const k = Buffer.from(u).toString('base64'); if (!seen.has(k)) { seen.add(k); all.push(u); } });
    docs.push(d); updates.push(us);
  }
  return { docs, updates, all };
}

function close(docs, all, r) {
  let deliveryQuiescent = false;
  for (let round = 0; round < 12; round++) {
    const before = all.length;
    for (const d of docs) {
      const ordered = shuffle(all.slice(), r);
      for (let i = 0; i < ordered.length;) {
        const size = 1 + Math.floor(r() * 3), chunk = ordered.slice(i, i + size); i += size;
        const u = chunk.length === 1 ? chunk[0] : Y.mergeUpdates(chunk);
        Y.applyUpdate(d, u); if (r() < 0.3) Y.applyUpdate(d, u);
      }
    }
    if (all.length === before) { deliveryQuiescent = true; break; }
  }
  let quiescent = false;
  for (let round = 0; round < 12; round++) {
    const before = all.length, old = JSON.stringify(docs.map(L.key));
    for (const i of shuffle([...docs.keys()], r)) for (const j of shuffle([...docs.keys()], r)) if (i !== j) L.sync(docs[i], docs[j]);
    if (all.length === before && JSON.stringify(docs.map(L.key)) === old) { quiescent = true; break; }
  }
  const v = L.verdict(docs);
  return { deliveryQuiescent, quiescent, ...v, skips: docs.map(skipsLeft) };
}

// The gap families of search.mjs, with the fourth replica receiving what the
// third does.
function seed(family, g) {
  const [a, b, c, e] = g.docs, [ua, ub] = g.updates;
  const apply = (d, u) => Y.applyUpdate(d, u);
  if (family === 'plain-gap') {
    text(a).insert(0, 'y'); text(b).insert(0, 'b'); apply(a, ub[0]);
    text(a).insert(text(a).toString().indexOf('b') + 1, 'h'); apply(b, ua.at(-1));
    apply(c, ub[0]); apply(c, ua.at(-1)); apply(e, ub[0]);
  } else if (family === 'delete-set-gap') {
    text(a).insert(0, 'a', { bold: true }); const base = ua.at(-1); text(a).insert(1, 'b'); text(a).format(0, 2, { bold: null });
    const late = ua.at(-1); apply(b, base); apply(b, late); apply(c, base); apply(e, base); apply(e, late);
  } else {
    text(a).insert(0, 'ab', { bold: true }); const base = ua.at(-1); apply(b, base); apply(c, base); apply(e, base);
    text(b).format(0, 2, { bold: null }); text(b).insert(1, 'q'); apply(a, ub.at(-1)); apply(c, ub.at(-1)); apply(e, ub.at(-1));
  }
}

function edit(t, r, k) {
  const len = t.length, pos = Math.floor(r() * (len + 1)), choice = Math.floor(r() * 4);
  if (choice < 2 || len === 0) t.insert(pos, String.fromCharCode(65 + (k % 26)), r() < 0.5 ? {} : { bold: r() < 0.5, italic: r() < 0.5 });
  else { const from = Math.min(pos, len - 1), length = 1 + Math.floor(r() * (len - from)); if (choice === 2) t.delete(from, length); else t.format(from, length, r() < 0.5 ? { bold: null } : { bold: true, italic: r() < 0.5 ? true : null }); }
}

function trial(family, gc, s) {
  const r = rng(s), g = group(4, gc);
  seed(family, g);
  const n = 1 + Math.floor(r() * 20);
  for (let k = 0; k < n; k++) {
    const idx = family === 'insert-before-unformat' ? [0, 2, 3][Math.floor(r() * 3)] : 1 + Math.floor(r() * 3);
    edit(text(g.docs[idx]), r, k);
    if (r() < 0.5) { const dest = (idx + 1 + Math.floor(r() * 3)) % 4, u = g.updates[idx].at(-1); if (u) Y.applyUpdate(g.docs[dest], u); }
  }
  const first = close(g.docs, g.all, r);
  for (let round = 0; round < 3; round++) for (const d of g.docs) edit(text(d), r, round);
  const second = close(g.docs, g.all, r);
  const out = { family, gc, seed: s, n, first, second, views: g.docs.map(L.view) };
  for (const d of g.docs) d.destroy();
  return out;
}

{
  const x = L.doc(1), y = L.doc(2);
  text(x.d).insert(0, 'q'); assert.equal(L.verdict([x.d, y.d]).divergence, true);
  L.sync(x.d, y.d); assert.equal(L.verdict([x.d, y.d]).divergence, false);
  text(x.d).format(0, 1, { bold: true }); assert.equal(L.verdict([x.d, y.d]).divergence, true);
  L.sync(x.d, y.d); assert.equal(L.verdict([x.d, y.d]).divergence, false);
  x.d.destroy(); y.d.destroy();
}

const bad = (c) => c.divergence || c.unresolved || c.reloadDivergence || c.svs !== 1 || !c.quiescent || !c.deliveryQuiescent || c.skips.some((x) => x > 0);
const summary = { package: L.pkg.name, version: L.pkg.version, node: process.version, started: new Date().toISOString(), groups: {}, findings: [] };
for (const family of ['plain-gap', 'delete-set-gap', 'insert-before-unformat']) for (const gc of [false, true]) {
  const key = `${family} gc=${gc}`, s = (summary.groups[key] = { trials: 0, firstFindings: 0, secondFindings: 0, skipsAfterFirst: 0 });
  for (let i = 1; i <= seeds; i++) {
    const res = trial(family, gc, Math.imul(i, 0x9e3779b1) >>> 0);
    s.trials++;
    if (bad(res.first)) s.firstFindings++;
    if (bad(res.second)) s.secondFindings++;
    if (res.first.skips.some((x) => x > 0)) s.skipsAfterFirst++;
    if (bad(res.first) || bad(res.second)) { if (summary.findings.length < 30) summary.findings.push(res); console.log(JSON.stringify({ event: 'FINDING', ...res })); }
  }
  console.log(JSON.stringify({ event: 'GROUP', key, ...s }));
}
summary.finished = new Date().toISOString();
writeFileSync(new URL(`e5-latent-divergence-results-v${version}.json`, import.meta.url), JSON.stringify(summary, null, 2) + '\n');
console.log(JSON.stringify({ event: 'DONE', groups: summary.groups, findings: summary.findings.length }));
