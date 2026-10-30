// E2: the author of a withheld update keeps editing around it, and the
// receiver edits on top of what it has after every delivery step.
//
// Mechanism. A receiver that holds a struct behind a clock gap (v14: Skip;
// v13: pendingStructs) also receives later structs of the same author whose
// origins are the withheld struct (origin missing, so pending on both
// versions), delete sets naming withheld or present items, and formatting
// markers spanning the gap. Part 1 enumerates every delivery order of the
// author's updates at one receiver, with a deterministic receiver edit after
// each step; part 2 withholds a random subset of a longer authored sequence
// from two receivers that edit and relay. After either, every replica gets
// the identical complete update set and state vectors are exchanged until
// quiescent. Usage: node e2-source-keeps-editing.mjs <13|14> [seeds]

import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { load, rng, shuffle, permutations } from './lib.mjs';

const version = process.argv[2] ?? '14';
const seeds = Number(process.argv[3] ?? 5000);
const L = await load(version);
const { Y, text } = L;

// Delivers the complete set to every document in a shuffled order, merging
// some batches, then exchanges state vectors until nothing changes.
function close(docs, all, r) {
  let deliveryQuiescent = false;
  for (let round = 0; round < 12; round++) {
    const before = all.length;
    for (const d of docs) {
      const ordered = shuffle(all.slice(), r);
      for (let i = 0; i < ordered.length;) {
        const size = 1 + Math.floor(r() * 3);
        const chunk = ordered.slice(i, i + size);
        i += size;
        Y.applyUpdate(d, chunk.length === 1 ? chunk[0] : Y.mergeUpdates(chunk));
      }
    }
    if (all.length === before) { deliveryQuiescent = true; break; }
  }
  const afterDelivery = L.verdict(docs);
  let quiescent = false;
  for (let round = 0; round < 12; round++) {
    const before = all.length, old = JSON.stringify(docs.map(L.key));
    for (const i of shuffle([...docs.keys()], r)) for (const j of shuffle([...docs.keys()], r)) if (i !== j) L.sync(docs[i], docs[j]);
    if (all.length === before && JSON.stringify(docs.map(L.key)) === old) { quiescent = true; break; }
  }
  return { deliveryQuiescent, afterDelivery, quiescent, final: L.verdict(docs) };
}

// A set of documents whose every emitted update is collected once.
function group(n, gc) {
  const all = [], seen = new Set(), docs = [], updates = [];
  for (let i = 0; i < n; i++) {
    const d = new Y.Doc({ gc }); d.clientID = 100 + i; text(d);
    const us = [];                                             // the document's own transactions only
    d.on('update', (u, _origin, _doc, tr) => { if (tr.local) us.push(u); const k = Buffer.from(u).toString('base64'); if (!seen.has(k)) { seen.add(k); all.push(u); } });
    docs.push(d); updates.push(us);
  }
  return { docs, updates, all };
}

const EDITS = [
  (t) => { t.insert(0, 'X'); },
  (t) => { t.insert(t.length, 'Z'); },
  (t) => { if (t.length) t.delete(0, 1); },
  (t) => { if (t.length) t.format(0, t.length, { bold: null }); },
  (t) => { if (t.length) t.format(0, t.length, { italic: true }); },
];

// Part 1: one author, six updates, every delivery order at the receiver.
function authored(gc) {
  const g = group(3, gc);
  const [a, b, c] = g.docs;
  text(a).insert(0, 'y');                                   // u0: withheld first
  text(b).insert(0, 'b');
  Y.applyUpdate(a, g.updates[1][0]); Y.applyUpdate(c, g.updates[1][0]);
  text(a).insert(text(a).toString().indexOf('b') + 1, 'h'); // u1: after b, clock gap at b
  text(a).insert(text(a).toString().indexOf('y') + 1, 'k'); // u2: origin y, missing at b
  text(a).delete(text(a).toString().indexOf('h'), 1);       // u3: delete set only
  text(a).format(0, text(a).length, { bold: true });        // u4: markers around the whole text
  text(a).insert(text(a).length, 'z');                      // u5: inside the bold run
  assert.equal(g.updates[0].length, 6);
  return g;
}

function part1(gc, variant, order, merged) {
  const g = authored(gc);
  const [a, b, c] = g.docs;
  const ua = g.updates[0];
  const r = rng(order.join('') + variant + 1);
  const steps = merged ? [] : order.map((i) => [i]);
  if (merged) for (let i = 0; i < order.length; i += 2) steps.push(order.slice(i, i + 2));
  const transient = [];
  for (const step of steps) {
    const us = step.map((i) => ua[i]);
    Y.applyUpdate(b, us.length === 1 ? us[0] : Y.mergeUpdates(us));
    transient.push({ step, view: text(b).toString(), pending: L.pending(b) });
    if (variant < EDITS.length) EDITS[(variant + step[0]) % EDITS.length](text(b));
    const last = g.updates[1].at(-1);
    if (last) Y.applyUpdate(c, last);                         // relay the receiver's latest update onward
  }
  const res = close(g.docs, g.all, r);
  const out = { gc, variant, order, merged, transient, ...res, views: g.docs.map(L.view) };
  for (const d of g.docs) d.destroy();
  return out;
}

// Part 2: a longer authored sequence with a random subset withheld from two
// receivers that edit and relay between each other.
function part2(gc, seed) {
  const r = rng(seed);
  const g = group(3, gc);
  const [a, b, c] = g.docs;
  text(b).insert(0, 'base');
  Y.applyUpdate(a, g.updates[1][0]); Y.applyUpdate(c, g.updates[1][0]);
  const n = 6 + Math.floor(r() * 15);
  const trace = [];
  for (let k = 0; k < n; k++) {
    const t = text(a), len = t.length, pos = Math.floor(r() * (len + 1)), choice = r();
    if (choice < 0.5 || len === 0) { const attrs = r() < 0.5 ? {} : { bold: true }; t.insert(pos, String.fromCharCode(97 + (k % 26)), attrs); trace.push(['insert', pos, attrs]); }
    else if (choice < 0.75) { const from = Math.min(pos, len - 1), length = 1 + Math.floor(r() * Math.min(3, len - from)); t.delete(from, length); trace.push(['delete', from, length]); }
    else { const from = Math.min(pos, len - 1), length = 1 + Math.floor(r() * (len - from)); const attrs = r() < 0.5 ? { bold: null } : { bold: true, italic: r() < 0.5 ? true : null }; t.format(from, length, attrs); trace.push(['format', from, length, attrs]); }
  }
  const ua = g.updates[0];
  const withheldCount = 1 + Math.floor(r() * Math.min(5, ua.length - 1));
  const withheld = new Set(shuffle([...ua.keys()], r).slice(0, withheldCount));
  const delivered = shuffle([...ua.keys()].filter((i) => !withheld.has(i)), r);
  const receivers = [b, c];
  const transient = [];
  for (const i of delivered) {
    const to = receivers[Math.floor(r() * 2)];
    Y.applyUpdate(to, ua[i]);
    if (r() < 0.7) {
      const t = text(to), len = t.length, pos = Math.floor(r() * (len + 1)), c2 = r();
      if (c2 < 0.5 || len === 0) t.insert(pos, 'X', r() < 0.5 ? {} : { italic: true });
      else if (c2 < 0.75) t.delete(Math.min(pos, len - 1), 1);
      else t.format(Math.min(pos, len - 1), 1, r() < 0.5 ? { bold: null } : { bold: true });
      const other = to === b ? c : b;
      const last = g.updates[to === b ? 1 : 2].at(-1);
      if (last && r() < 0.6) Y.applyUpdate(other, last);
    }
    transient.push({ to: to.clientID, i, b: text(b).toString(), c: text(c).toString(), pending: [L.pending(b), L.pending(c)] });
  }
  const res = close(g.docs, g.all, r);
  const out = { gc, seed, n, trace, withheld: [...withheld].sort(), delivered, transient, ...res, views: g.docs.map(L.view) };
  for (const d of g.docs) d.destroy();
  return out;
}

// Oracle controls: a missing insert and a missing format must be detected.
{
  const x = L.doc(1), y = L.doc(2);
  text(x.d).insert(0, 'q'); assert.equal(L.verdict([x.d, y.d]).divergence, true);
  L.sync(x.d, y.d); assert.equal(L.verdict([x.d, y.d]).divergence, false);
  text(x.d).format(0, 1, { bold: true }); assert.equal(L.verdict([x.d, y.d]).divergence, true);
  L.sync(x.d, y.d); assert.equal(L.verdict([x.d, y.d]).divergence, false);
  x.d.destroy(); y.d.destroy();
}
// Baseline: the transient view of the receiver after u1 alone is the reported one.
{
  const g = authored(false);
  Y.applyUpdate(g.docs[1], g.updates[0][1]);
  assert.equal(text(g.docs[1]).toString(), version === '14' ? 'bh' : 'b');
  assert.equal(L.pending(g.docs[1]).structs, version !== '14');
  for (const d of g.docs) d.destroy();
}

const summary = { package: L.pkg.name, version: L.pkg.version, node: process.version, started: new Date().toISOString(), part1: {}, part2: {}, findings: [] };
const isFinding = (res) => res.final.divergence || res.final.unresolved || res.final.reloadDivergence || res.final.svs !== 1 || !res.quiescent || !res.deliveryQuiescent;
const record = (part, key, res, extra) => {
  const s = summary[part][key] ??= { cases: 0, findings: 0, transientNonCausal: 0 };
  s.cases++;
  if (isFinding(res)) { s.findings++; if (summary.findings.length < 30) summary.findings.push({ part, ...extra, ...res }); console.log(JSON.stringify({ event: 'FINDING', part, ...extra, final: res.final, views: res.views })); }
  return s;
};

for (const gc of [false, true]) {
  for (const merged of [false, true]) {
    for (let variant = 0; variant <= EDITS.length; variant++) {
      let nonCausal = 0;
      for (const order of permutations([0, 1, 2, 3, 4, 5])) {
        const res = part1(gc, variant, order, merged);
        const s = record('part1', `gc=${gc} merged=${merged} variant=${variant}`, res, { order, variant, merged, gc });
        // A transient state that shows h or k without y is not causally closed.
        if (res.transient.some((t) => !t.view.includes('y') && (t.view.includes('h') || t.view.includes('k')))) { nonCausal++; s.transientNonCausal = nonCausal; }
      }
    }
  }
  console.log(JSON.stringify({ event: 'PART1', gc, groups: Object.fromEntries(Object.entries(summary.part1).filter(([k]) => k.startsWith(`gc=${gc}`))) }));
  for (let i = 1; i <= seeds; i++) {
    const seed = Math.imul(i, 0x9e3779b1) >>> 0;
    const res = part2(gc, seed);
    const s = record('part2', `gc=${gc}`, res, { seed });
    if (res.transient.some((t) => t.pending.some((p) => p.structs || p.ds))) s.transientPending = (s.transientPending ?? 0) + 1;
    if (i % 1000 === 0) console.log(JSON.stringify({ event: 'PROGRESS', gc, i, ...s }));
  }
}
summary.finished = new Date().toISOString();
writeFileSync(new URL(`e2-source-keeps-editing-results-v${version}.json`, import.meta.url), JSON.stringify(summary, null, 2) + '\n');
console.log(JSON.stringify({ event: 'DONE', part1: summary.part1, part2: summary.part2, findings: summary.findings.length }));
