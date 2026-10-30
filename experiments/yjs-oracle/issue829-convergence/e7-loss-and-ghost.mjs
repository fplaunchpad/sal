// E7: edits aimed at a causally inconsistent view, judged for lost and
// ghost characters and for formatting intent, not only for convergence.
//
// A replica that holds a gap (v14: a struct behind a Skip; v13: a parked
// struct or an eagerly applied delete set) displays a document no causal
// history produces. The edits below are chosen against that display: the
// character behind the gap is deleted, text is typed where the withheld
// character will land, formats and deletes span the gap position, the
// whole visible text is replaced. After closure every replica holds the
// complete set and the converged document is judged against the users'
// intents:
//
//   lost   a character someone inserted and nobody deleted is absent;
//   ghost  a character someone deleted is present;
//   format a character and key addressed by exactly one intent (its
//          insertion attributes or one format call), with the converged
//          value different from that intent.
//
// Each case is run twice with the same edit script: with the gap (the
// withheld update arrives after the edits) and as a control (it arrives
// before them, so the editing replica sees a causal state). A format
// difference that appears only with the gap is attributed to editing the
// inconsistent view. Usage: node e7-loss-and-ghost.mjs <13|14> [seeds]

import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { load, rng, shuffle } from './lib.mjs';

const version = process.argv[2] ?? '14';
const seeds = Number(process.argv[3] ?? 5000);
const L = await load(version);
const { Y, text } = L;

// Unique characters for every insertion, so intent is tracked by identity.
const POOL = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789cdefgijklmnoprstuvwxz';
function world(gc) {
  const w = { docs: [], all: [], seen: new Set(), next: 0, inserted: new Map(), deleted: new Set(), formats: new Map() };
  for (let i = 0; i < 3; i++) {
    const d = new Y.Doc({ gc }); d.clientID = 100 + i; text(d);
    d.on('update', (u) => { const k = Buffer.from(u).toString('base64'); if (!w.seen.has(k)) { w.seen.add(k); w.all.push(u); } });
    w.docs.push(d);
  }
  w.fresh = () => { const c = w.next < POOL.length ? POOL[w.next] : String.fromCharCode(0x4e00 + w.next - POOL.length); w.next++; return c; };
  // Intent-recording edits on a document.
  // Attribute objects are copied: 13.x writes the negated current attributes into the object it is given.
  w.insert = (d, pos, attrs = {}, ch = w.fresh()) => { text(d).insert(pos, ch, { ...attrs }); w.inserted.set(ch, { ...attrs }); return ch; };
  w.delete = (d, from, len) => { const s = text(d).toString().slice(from, from + len); for (const c of s) w.deleted.add(c); if (len > 0) text(d).delete(from, len); return s; };
  w.format = (d, from, len, attrs) => { const s = text(d).toString().slice(from, from + len); for (const c of s) for (const [k, v] of Object.entries(attrs)) { const key = c + '\u0000' + k; w.formats.set(key, (w.formats.get(key) ?? []).concat([v])); } if (len > 0) text(d).format(from, len, { ...attrs }); return s; };
  return w;
}

// The gap families. Each returns the withheld update and the replicas that
// hold the inconsistent view.
function seedFamily(family, w) {
  const [a, b, c] = w.docs;
  const own = (d) => { const us = []; d.on('update', (u, _o, _d, tr) => { if (tr.local) us.push(u); }); return us; };
  const ua = own(a), ub = own(b);
  if (family === 'plain-gap') {
    w.insert(a, 0, {}, 'y'); const withheld = ua[0];
    w.insert(b, 0, {}, 'b'); Y.applyUpdate(a, ub[0]); Y.applyUpdate(c, ub[0]);
    w.insert(a, text(a).toString().indexOf('b') + 1, {}, 'h');
    return { withheld, late: ua[1], gapReplicas: [b, c] };
  }
  if (family === 'delete-set-gap') {
    w.insert(a, 0, { bold: true }, 'a'); const base = ua[0];
    w.insert(a, 1, {}, 'b'); const withheld = ua[1];
    w.format(a, 0, 2, { bold: null }); const late = ua[2];
    Y.applyUpdate(b, base); Y.applyUpdate(c, base);
    return { withheld, late, gapReplicas: [b, c] };
  }
  w.insert(a, 0, { bold: true }, 'a'); w.insert(a, 1, { bold: true }, 'b');
  for (const u of ua) { Y.applyUpdate(b, u); Y.applyUpdate(c, u); }
  w.format(b, 0, 2, { bold: null }); const withheld = ub[0];
  w.insert(b, 1, {}, 'q'); const late = ub[1];
  return { withheld, late, gapReplicas: [a, c] };
}

// The targeted edit menu, each relative to the editing replica's own view.
const MENU = {
  none: () => {},
  insertStart: (w, d) => w.insert(d, 0),
  insertEnd: (w, d) => w.insert(d, text(d).length),
  insertAfterFirst: (w, d) => w.insert(d, Math.min(1, text(d).length)),
  insertBoldStart: (w, d) => w.insert(d, 0, { bold: true }),
  insertBoldEnd: (w, d) => w.insert(d, text(d).length, { bold: true }),
  deleteFirst: (w, d) => w.delete(d, 0, Math.min(1, text(d).length)),
  deleteLast: (w, d) => w.delete(d, Math.max(0, text(d).length - 1), Math.min(1, text(d).length)),
  deleteAll: (w, d) => w.delete(d, 0, text(d).length),
  boldAll: (w, d) => w.format(d, 0, text(d).length, { bold: true }),
  unboldAll: (w, d) => w.format(d, 0, text(d).length, { bold: null }),
  italicAll: (w, d) => w.format(d, 0, text(d).length, { italic: true }),
  replaceFirst: (w, d) => { w.delete(d, 0, Math.min(1, text(d).length)); w.insert(d, 0); },
  replaceAll: (w, d) => { w.delete(d, 0, text(d).length); w.insert(d, 0); },
};
const NAMES = Object.keys(MENU);

function close(w, r, mode, withheld) {
  const docs = w.docs;
  if (mode === 'alone') for (const d of docs) Y.applyUpdate(d, withheld);
  else if (mode === 'merged') { const others = shuffle(w.all.filter((u) => u !== withheld), r).slice(0, 2); const m = Y.mergeUpdates([...others, withheld]); for (const d of docs) Y.applyUpdate(d, m); }
  if (mode !== 'sync') for (let round = 0; round < 12; round++) { const before = w.all.length; for (const d of docs) for (const u of shuffle(w.all.slice(), r)) Y.applyUpdate(d, u); if (w.all.length === before) break; }
  for (let round = 0; round < 12; round++) {
    const before = w.all.length, old = JSON.stringify(docs.map(L.key));
    for (const i of shuffle([0, 1, 2], r)) for (const j of shuffle([0, 1, 2], r)) if (i !== j) L.sync(docs[i], docs[j]);
    if (w.all.length === before && JSON.stringify(docs.map(L.key)) === old) break;
  }
  return L.verdict(docs);
}

function judge(w) {
  const v = L.view(w.docs[0]);
  const present = new Set(v.text);
  const lost = [...w.inserted.keys()].filter((c) => !w.deleted.has(c) && !present.has(c));
  const ghost = [...w.deleted].filter((c) => present.has(c));
  const attrsOf = new Map();
  for (const run of v.delta) for (const c of run.insert) attrsOf.set(c, run.attributes);
  const format = [];
  for (const [c, ins] of w.inserted) {
    if (!present.has(c)) continue;
    for (const k of ['bold', 'italic']) {
      const intents = [...(k in ins ? [ins[k]] : []), ...(w.formats.get(c + '\u0000' + k) ?? [])];
      if (intents.length !== 1) continue;
      const want = intents[0] === true ? true : null, got = attrsOf.get(c)?.[k] ?? null;
      if (want !== got) format.push({ ch: c, key: k, want, got });
    }
  }
  return { text: v.text, lost, ghost, format };
}

// One case: the family, an edit script [[replicaIndex, editName], ...], a
// closure mode; run with the gap and as the control.
function runCase(family, gc, script, mode, seedNum, controlFirst) {
  const w = world(gc), r = rng(seedNum);
  const { withheld, late, gapReplicas } = seedFamily(family, w);
  if (controlFirst) for (const d of gapReplicas) Y.applyUpdate(d, withheld);
  for (const d of gapReplicas) Y.applyUpdate(d, late);
  const gapViews = gapReplicas.map((d) => text(d).toString());
  for (const [i, name] of script) { MENU[name](w, gapReplicas[i]); const u = w.all.at(-1); if (u) Y.applyUpdate(gapReplicas[1 - i], u); }
  const verdict = close(w, r, mode, withheld);
  const out = { verdict, gapViews, ...judge(w) };
  for (const d of w.docs) d.destroy();
  return out;
}

// Oracle controls: a lost character, a ghost and a format miss must be seen.
{
  const w = world(false); const d = w.docs[0];
  const c1 = w.insert(d, 0); w.inserted.set('Q', {}); let j = judge(w); assert.deepEqual(j.lost, ['Q']); assert.deepEqual(j.ghost, []);
  w.inserted.delete('Q'); w.delete(d, 0, 1); w.deleted.delete(c1); w.insert(d, 0, {}, c1); j = judge(w); assert.deepEqual(j.lost, []);
  w.deleted.add(c1); j = judge(w); assert.deepEqual(j.ghost, [c1]); w.deleted.delete(c1);
  w.format(d, 0, 1, { bold: true }); w.formats.set(c1 + '\u0000bold', [null]); j = judge(w); assert.equal(j.format.length, 1);
  d.destroy();
}

const summary = { package: L.pkg.name, version: L.pkg.version, node: process.version, started: new Date().toISOString(), exhaustive: {}, random: {}, examples: { lost: [], ghost: [], formatGapOnly: [] } };
const tally = (s, gap, ctl, family, gc, script, mode, seedNum) => {
  s.cases++;
  if (gap.verdict.divergence || gap.verdict.unresolved) s.divergence++;
  if (gap.lost.length) { s.lost++; if (summary.examples.lost.length < 10) summary.examples.lost.push({ family, gc, script, mode, seed: seedNum, gap, ctl }); }
  if (gap.ghost.length) { s.ghost++; if (summary.examples.ghost.length < 10) summary.examples.ghost.push({ family, gc, script, mode, seed: seedNum, gap, ctl }); }
  if (ctl.lost.length || ctl.ghost.length) s.controlLostOrGhost++;
  if (gap.format.length) s.format++;
  if (ctl.format.length) s.formatControl++;
  if (gap.format.length && !ctl.format.length) { s.formatGapOnly++; if (summary.examples.formatGapOnly.length < 20) summary.examples.formatGapOnly.push({ family, gc, script, mode, seed: seedNum, gap, ctl }); }
};
const fresh = () => ({ cases: 0, divergence: 0, lost: 0, ghost: 0, controlLostOrGhost: 0, format: 0, formatControl: 0, formatGapOnly: 0 });

for (const family of ['plain-gap', 'delete-set-gap', 'insert-before-unformat']) for (const gc of [false, true]) {
  const s = (summary.exhaustive[`${family} gc=${gc}`] = fresh());
  const scripts = [];
  for (const e1 of NAMES) { scripts.push([[0, e1]]); for (const e2 of NAMES) if (e2 !== 'none') scripts.push([[0, e1], [0, e2]]); }
  const withOther = scripts.flatMap((sc) => NAMES.filter((n) => n !== 'none').map((n) => sc.concat([[1, n]])));
  let n = 0;
  for (const script of scripts.concat(withOther)) for (const mode of ['alone', 'merged', 'sync']) {
    n++;
    tally(s, runCase(family, gc, script, mode, n, false), runCase(family, gc, script, mode, n, true), family, gc, script, mode, n);
  }
  console.log(JSON.stringify({ event: 'EXHAUSTIVE', family, gc, ...s }));
}

// Randomised edits on the gap view, same oracle and control.
function randomScript(r) {
  const out = []; const n = 1 + Math.floor(r() * 6);
  for (let k = 0; k < n; k++) out.push([Math.floor(r() * 2), NAMES[1 + Math.floor(r() * (NAMES.length - 1))]]);
  return out;
}
for (const family of ['plain-gap', 'delete-set-gap', 'insert-before-unformat']) for (const gc of [false, true]) {
  const s = (summary.random[`${family} gc=${gc}`] = fresh());
  for (let i = 1; i <= seeds; i++) {
    const seedNum = Math.imul(i, 0x9e3779b1) >>> 0, r = rng(seedNum);
    const script = randomScript(r), mode = ['alone', 'merged', 'sync'][Math.floor(r() * 3)];
    tally(s, runCase(family, gc, script, mode, seedNum, false), runCase(family, gc, script, mode, seedNum, true), family, gc, script, mode, seedNum);
  }
  console.log(JSON.stringify({ event: 'RANDOM', family, gc, ...s }));
}
summary.finished = new Date().toISOString();
writeFileSync(new URL(`e7-loss-and-ghost-results-v${version}.json`, import.meta.url), JSON.stringify(summary, null, 2) + '\n');
console.log(JSON.stringify({ event: 'DONE', exhaustive: summary.exhaustive, random: summary.random }));
