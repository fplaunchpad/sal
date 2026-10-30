// E6: issue 829 convergence search over the v2 update encoding and over mixed v1/v2 encodings.
// Same three gap families, three replicas and local-edit loop as search.mjs. Encodings:
//   v2     every apply, encode, merge and diff uses the V2 functions; replicas listen on 'updateV2'.
//   mixed  each replica emits and applies in its own format (at least one v1 and one v2 replica);
//          updates are converted with convertUpdateFormatV1ToV2 / V2ToV1 where the formats differ,
//          merged batches take the format of their first element, and state-vector anti-entropy
//          alternates formats per exchange.
// Deliveries:
//   individual    the complete update set, shuffled, batched by merge, sometimes duplicated (as search.mjs).
//   diff          each replica receives diffUpdateV2(merged complete set, its state vector), sometimes twice.
//   diff-partial  for eight rounds the diff is taken from a merged random subset of the set, whose
//                 clock gaps make diffUpdateV2 write Skip structs; then the complete set until quiescent.
// Oracle: views compared without a sequential specification, pending stores and quiescence checked,
// and the fingerprint of the state reloaded through both encodings compared with the live view.
// A convergence failure is counted only when the complete set was delivered, no pending structs or
// delete sets remain, and views or reloaded fingerprints still differ. Exceptions are findings too.
//
// Usage:
//   node e6-v2-encoding.mjs run <13|14> <count> <start> <encodings,csv> <deliveries,csv> <out.json>
//   node e6-v2-encoding.mjs aggregate <out.json> <shard.json>...
//   node e6-v2-encoding.mjs one <13|14> <family> <gc> <seed> <encoding> <delivery>    (prints one full trial)
import assert from 'node:assert/strict';
import { writeFileSync, readFileSync } from 'node:fs';
import { load, rng, shuffle } from './lib.mjs';

const FAMILIES = ['plain-gap', 'delete-set-gap', 'insert-before-unformat'];
const MIXED_FORMATS = [['v1', 'v2', 'v2'], ['v2', 'v1', 'v2'], ['v2', 'v2', 'v1'], ['v1', 'v1', 'v2'], ['v1', 'v2', 'v1'], ['v2', 'v1', 'v1']];

const [mode, ...rest] = process.argv.slice(2);
if (mode === 'aggregate') aggregate(rest[0], rest.slice(1));
else if (mode === 'run') await run(rest[0] || '14', Number(rest[1] || 1000), Number(rest[2] || 1), (rest[3] || 'v2,mixed').split(','), (rest[4] || 'individual,diff,diff-partial').split(','), rest[5] || `e6-shard-v${rest[0] || '14'}.json`);
else if (mode === 'one') { const L = await load(rest[0]); const { trial } = makeTrial(L); const t = trial(rest[1], rest[2] === 'true', Number(rest[3]), rest[4], rest[5]); console.log(JSON.stringify({ package: L.pkg.name, version: L.pkg.version, ...t }, null, 1)); }
else { console.error('usage: run <13|14> <count> <start> <encodings> <deliveries> <out> | aggregate <out> <shards...> | one <13|14> <family> <gc> <seed> <encoding> <delivery>\n  deliveries: individual, diff, diff-partial'); process.exit(2); }

/** The trial and its oracle controls, over the loaded package L. */
function makeTrial(L) {
  const { Y, text, view, key, equal, pending, sv } = L;
  const F = {
    v1: { event: 'update', apply: Y.applyUpdate, merge: Y.mergeUpdates, encode: Y.encodeStateAsUpdate },
    v2: { event: 'updateV2', apply: Y.applyUpdateV2, merge: Y.mergeUpdatesV2, encode: Y.encodeStateAsUpdateV2 },
  };
  const convert = (u, from, to) => (from === to ? u : from === 'v1' ? Y.convertUpdateFormatV1ToV2(u) : Y.convertUpdateFormatV2ToV1(u));
  const b64 = (u) => Buffer.from(u).toString('base64');
  /** Whether an update carries a Skip struct on the wire (coverage of the gap-encoding path). */
  const carriesSkip = (u, fmt) => (fmt === 'v1' ? Y.decodeUpdate(u) : Y.decodeUpdateV2(u)).structs.some((s) => s instanceof Y.Skip);

  /** withholdFrom (control only): that replica receives nothing in the delivery phase and anti-entropy is skipped. */
  function trial(family, gc, seed, encoding, delivery, localCount = null, withholdFrom = -1) {
    const r = rng(seed), rf = rng((seed ^ 0xa5a5a5a5) >>> 0);
    const formats = encoding === 'v2' ? ['v2', 'v2', 'v2'] : MIXED_FORMATS[Math.floor(rf() * MIXED_FORMATS.length)];
    const docs = [], all = [], seen = new Set(), by = [], trace = [];
    let phase = 'setup';
    const result = { family, gc, seed, encoding, delivery, formats, trace, deliveries: 0, skipDeliveries: 0 };
    try {
      for (let i = 0; i < 3; i++) {
        const d = new Y.Doc({ gc }); d.clientID = 100 + i; const us = []; docs.push(d); by.push(us);
        d.on(F[formats[i]].event, (u) => { const item = { u, fmt: formats[i] }; us.push(item); const k = item.fmt + ':' + b64(u); if (!seen.has(k)) { seen.add(k); all.push(item); } });
        text(d);
      }
      const [a, b, c] = docs;
      let withheld;
      const idxOf = (d) => docs.indexOf(d);
      /** Deliver one update item to a replica in that replica's own format. */
      const apply = (d, item) => { const f = formats[idxOf(d)], u = convert(item.u, item.fmt, f); result.deliveries++; if (carriesSkip(u, f)) result.skipDeliveries++; F[f].apply(d, u); };
      /** Merge a batch in the format of its first element. */
      const mergeBatch = (chunk) => { const fmt = chunk[0].fmt; return { u: F[fmt].merge(chunk.map((x) => convert(x.u, x.fmt, fmt))), fmt }; };
      if (family === 'plain-gap') {
        text(a).insert(0, 'y'); withheld = by[0][0]; text(b).insert(0, 'b'); apply(a, by[1][0]);
        text(a).insert(text(a).toString().indexOf('b') + 1, 'h'); apply(b, by[0].at(-1));
        apply(c, by[1][0]); apply(c, by[0].at(-1));
      } else if (family === 'delete-set-gap') {
        text(a).insert(0, 'a', { bold: true }); const base = by[0].at(-1); text(a).insert(1, 'b'); withheld = by[0].at(-1); text(a).format(0, 2, { bold: null });
        const late = by[0].at(-1); apply(b, base); apply(b, late); apply(c, base);
      } else {
        text(a).insert(0, 'ab', { bold: true }); const base = by[0].at(-1); apply(b, base); apply(c, base); text(b).format(0, 2, { bold: null }); withheld = by[1].at(-1); text(b).insert(1, 'q'); apply(a, by[1].at(-1)); apply(c, by[1].at(-1));
      }
      result.gapViews = docs.map(view); result.gapPending = docs.map(pending);
      // Local mutations made while the predecessor is withheld, including formatting (same draw sequence as search.mjs).
      phase = 'edits';
      const n = localCount ?? (1 + Math.floor(r() * 8));
      result.localCount = n;
      for (let k = 0; k < n; k++) {
        const idx = family === 'insert-before-unformat' ? (r() < 0.5 ? 0 : 2) : 1 + Math.floor(r() * 2), d = docs[idx], t = text(d), len = t.length, choice = Math.floor(r() * 4), pos = Math.floor(r() * (len + 1));
        if (choice < 2 || len === 0) { const value = String.fromCharCode(65 + k % 26), attrs = r() < 0.5 ? {} : { bold: r() < 0.5, italic: r() < 0.5 }; t.insert(pos, value, attrs); trace.push({ op: 'insert', replica: idx, pos, value, attrs }); } else { const from = Math.min(pos, len - 1), length = 1 + Math.floor(r() * (len - from)); if (choice === 2) { t.delete(from, length); trace.push({ op: 'delete', replica: idx, from, length }); } else { const attrs = r() < 0.5 ? { bold: null } : { bold: true, italic: r() < 0.5 ? true : null }; t.format(from, length, attrs); trace.push({ op: 'format', replica: idx, from, length, attrs }); } }
        // Optionally relay the just-produced edit but never the withheld predecessor.
        if (r() < 0.5 && by[idx].length) { const dest = (idx + 1) % 3, item = by[idx].at(-1); if (item !== withheld && Buffer.compare(Buffer.from(item.u), Buffer.from(withheld.u)) !== 0) { apply(docs[dest], item); trace.push({ op: 'relay-last', from: idx, to: dest }); } }
      }
      // Every replica gets the complete set. Newly generated cleanup updates join it.
      phase = 'delivery';
      let deliveryQuiescent = false;
      const partialRounds = delivery === 'diff-partial' ? 8 : 0;
      for (let round = 0; round < 12 + partialRounds; round++) {
        const before = all.length, batch = all.slice(), partial = round < partialRounds;
        if (delivery === 'individual') {
          for (const d of docs) { if (idxOf(d) === withholdFrom) continue; const ordered = shuffle(batch, r); for (let i = 0; i < ordered.length;) { const size = 1 + Math.floor(r() * 3), chunk = ordered.slice(i, i + size); i += size; const item = chunk.length === 1 ? chunk[0] : mergeBatch(chunk); apply(d, item); if (r() < 0.3) apply(d, item); } }
        } else {
          const merged = partial ? null : Y.mergeUpdatesV2(batch.map((x) => convert(x.u, x.fmt, 'v2')));
          for (const d of shuffle(docs, r)) {
            if (idxOf(d) === withholdFrom) continue;
            const source = partial ? Y.mergeUpdatesV2(shuffle(batch, r).slice(0, 1 + Math.floor(r() * batch.length)).map((x) => convert(x.u, x.fmt, 'v2'))) : merged;
            const item = { u: Y.diffUpdateV2(source, Y.encodeStateVector(d)), fmt: 'v2' }; apply(d, item); if (r() < 0.3) apply(d, item);
          }
        }
        if (all.length === before && !partial) { deliveryQuiescent = true; break; }
      }
      result.deliveryQuiescent = deliveryQuiescent; result.delivered = docs.map(view); result.mismatchAfterDelivery = !equal(docs); result.pendingAfterDelivery = docs.map(pending);
      // Explicit anti-entropy: exchange state-vector differences in shuffled order.
      phase = 'anti-entropy';
      let quiescent = false;
      for (let round = 0; round < (withholdFrom < 0 ? 12 : 0); round++) {
        const before = all.length, old = JSON.stringify(docs.map(view));
        for (const i of shuffle([0, 1, 2], r)) for (const j of shuffle([0, 1, 2], r)) if (i !== j) { const fmt = encoding === 'v2' ? 'v2' : (round + i + j) % 2 ? 'v2' : 'v1'; apply(docs[j], { u: F[fmt].encode(docs[i], Y.encodeStateVector(docs[j])), fmt }); }
        if (all.length === before && JSON.stringify(docs.map(view)) === old) { quiescent = true; break; }
      }
      phase = 'verdict';
      const v = L.verdict(docs);
      const freshV2 = docs.map((d) => L.reloadedV2(d, false));
      const reloadDivergenceV2 = !equal(freshV2) || freshV2.some((f, i) => key(f) !== key(docs[i]));
      for (const f of freshV2) f.destroy();
      Object.assign(result, { quiescent, final: docs.map(view), svList: docs.map(sv), updates: all.length, ...v, reloadDivergenceV2 });
      result.failure = !result.unresolved && (result.divergence || result.reloadDivergence || result.reloadDivergenceV2);
    } catch (e) {
      result.exception = { phase, name: e?.name, message: e?.message, stack: e?.stack };
      try { result.partialViews = docs.map(view); result.partialPending = docs.map(pending); } catch (_) { /* a half-built document may not render */ }
    }
    for (const d of docs) d.destroy();
    return result;
  }

  // Oracle controls on the v2 path: differing text must fail, complete shared v2 updates must pass,
  // a v2-only listener fires for local and remote transactions, and conversions round-trip.
  function controls() {
    const a = new Y.Doc(), b = new Y.Doc(); let fired = 0; a.on('updateV2', () => fired++);
    text(a).insert(0, 'x'); assert.equal(fired, 1); assert.equal(equal([a, b]), false);
    Y.applyUpdateV2(b, Y.encodeStateAsUpdateV2(a)); assert.equal(equal([a, b]), true);
    text(a).format(0, 1, { bold: true }); assert.equal(fired, 2); assert.equal(equal([a, b]), false);
    Y.applyUpdate(b, Y.convertUpdateFormatV2ToV1(Y.encodeStateAsUpdateV2(a))); assert.equal(equal([a, b]), true);
    const c = new Y.Doc(); let cfired = 0; c.on('updateV2', () => cfired++);
    Y.applyUpdateV2(c, Y.convertUpdateFormatV1ToV2(Y.encodeStateAsUpdate(a))); assert.equal(cfired, 1); assert.equal(equal([a, c]), true);
    assert.equal(key(L.reloadedV2(a)), key(a));
    a.destroy(); b.destroy(); c.destroy();
    // Negative control through the whole pipeline: a replica that never receives the predecessor
    // and gets no anti-entropy must be reported as divergent or unresolved, never as converged.
    for (const encoding of ['v2', 'mixed']) for (const delivery of ['individual', 'diff', 'diff-partial']) for (const family of FAMILIES) {
      const bearer = family === 'insert-before-unformat' ? 0 : 1;
      const t = trial(family, false, 829, encoding, delivery, 2, bearer);
      assert.equal(t.exception, undefined, t.exception?.stack);
      assert.ok(t.divergence || t.unresolved, `negative control ${family}/${encoding}/${delivery} passed the oracle`);
      assert.ok(t.updates > 0 && t.trace.length === 2);
    }
    // The Skip detector must see a skip in a merged update with a same-client gap, in both formats, and none in a complete update.
    { const a = new Y.Doc(); a.clientID = 5; const us = []; a.on('updateV2', (u) => us.push(u)); text(a).insert(0, 'a'); text(a).insert(1, 'b'); text(a).insert(2, 'c'); assert.equal(carriesSkip(Y.encodeStateAsUpdateV2(a), 'v2'), false); const gap = Y.mergeUpdatesV2([us[0], us[2]]); assert.equal(carriesSkip(gap, 'v2'), true); assert.equal(carriesSkip(Y.convertUpdateFormatV2ToV1(gap), 'v1'), true); a.destroy(); }
  }
  return { trial, controls };
}

async function run(version, count, start, encodings, deliveries, outPath) {
  const L = await load(version);
  const { pkg } = L;
  const { trial, controls } = makeTrial(L);
  controls();

  const summary = { package: pkg.name, version: pkg.version, node: process.version, start, count, encodings, deliveries, started: new Date().toISOString(), trials: 0, failures: 0, divergences: 0, reloadDivergences: 0, reloadDivergencesV2: 0, unresolved: 0, nonquiescent: 0, deliveryMismatches: 0, svMismatches: 0, exceptions: 0, baselineFailures: 0, groups: [], findings: [] };
  const COUNTERS = ['failures', 'divergences', 'reloadDivergences', 'reloadDivergencesV2', 'unresolved', 'nonquiescent', 'deliveryMismatches', 'svMismatches', 'exceptions'];
  console.log(JSON.stringify({ event: 'START', ...summary }));
  for (const encoding of encodings) for (const delivery of deliveries) for (const family of FAMILIES) for (const gc of [false, true]) {
    const group = { encoding, delivery, family, gc, trials: 0, baselineFailures: 0, deliveries: 0, skipDeliveries: 0 };
    for (const c of COUNTERS) group[c] = 0;
    // Zero-local-edit baseline must converge and show the reported partial views for each family.
    const baseline = trial(family, gc, 829, encoding, delivery, 0);
    try {
      assert.equal(baseline.exception, undefined, baseline.exception?.message);
      assert.equal(baseline.divergence, false); assert.equal(baseline.unresolved, false); assert.equal(baseline.reloadDivergence, false); assert.equal(baseline.reloadDivergenceV2, false);
      if (family === 'plain-gap') { assert.equal(baseline.gapViews[1].text, version === '14' ? 'bh' : 'b'); assert.equal(baseline.gapPending[1].structs, version !== '14'); }
      if (family === 'delete-set-gap') { assert.equal(baseline.gapViews[1].text, 'a'); assert.deepEqual(baseline.gapViews[1].delta, [{ attributes: {}, insert: 'a' }]); }
      if (family === 'insert-before-unformat') { assert.equal(baseline.gapViews[0].text, 'aqb'); assert.ok(baseline.gapViews[0].delta.some((x) => x.attributes.bold === true)); }
    } catch (e) {
      group.baselineFailures++; summary.baselineFailures++;
      const finding = { kind: 'baseline', assertion: e.message, ...baseline };
      summary.findings.push(finding); console.log(JSON.stringify({ event: 'FINDING', ...finding }));
    }
    for (let k = 0; k < count; k++) {
      const result = trial(family, gc, Math.imul(start + k, 0x9e3779b1) >>> 0, encoding, delivery);
      group.trials++; summary.trials++; group.deliveries += result.deliveries; group.skipDeliveries += result.skipDeliveries;
      const flags = result.exception
        ? { exceptions: true }
        : { failures: result.failure, divergences: result.divergence, reloadDivergences: result.reloadDivergence, reloadDivergencesV2: result.reloadDivergenceV2, unresolved: result.unresolved, nonquiescent: !result.quiescent || !result.deliveryQuiescent, deliveryMismatches: result.mismatchAfterDelivery, svMismatches: result.svs > 1 };
      const flagged = Object.entries(flags).filter(([, f]) => f).map(([name]) => name);
      for (const name of flagged) { group[name]++; summary[name]++; }
      if (flagged.length) { const finding = { kind: result.exception ? 'exception' : 'oracle', flagged, ...result }; if (summary.findings.length < 40) summary.findings.push(finding); console.log(JSON.stringify({ event: 'FINDING', ...finding })); }
      if (k % 1000 === 999) console.log(JSON.stringify({ event: 'PROGRESS', version: pkg.version, ...group }));
    }
    summary.groups.push(group);
    console.log(JSON.stringify({ event: 'GROUP', version: pkg.version, ...group }));
  }
  summary.finished = new Date().toISOString();
  writeFileSync(outPath, JSON.stringify(summary, null, 2) + '\n');
  console.log(JSON.stringify({ event: 'DONE', ...summary, findings: summary.findings.length }));
}

function aggregate(outPath, shardPaths) {
  const shards = shardPaths.map((p) => JSON.parse(readFileSync(p)));
  const out = { experiment: 'E6 v2 and mixed encodings, issue 829 families', node: shards[0]?.node, versions: [...new Set(shards.map((s) => `${s.package}@${s.version}`))], started: shards.map((s) => s.started).sort()[0], finished: shards.map((s) => s.finished).sort().at(-1), totals: { trials: 0 }, groups: [], findings: [] };
  for (const s of shards) {
    for (const g of s.groups) { out.groups.push({ package: s.package, version: s.version, ...g }); for (const [k, v] of Object.entries(g)) if (typeof v === 'number') out.totals[k] = (out.totals[k] || 0) + v; }
    for (const f of s.findings) out.findings.push({ package: s.package, version: s.version, ...f });
  }
  out.groups.sort((x, y) => `${x.version}|${x.encoding}|${x.delivery}|${x.family}|${x.gc}`.localeCompare(`${y.version}|${y.encoding}|${y.delivery}|${y.family}|${y.gc}`));
  writeFileSync(outPath, JSON.stringify(out, null, 2) + '\n');
  console.log(JSON.stringify({ event: 'AGGREGATED', shards: shards.length, totals: out.totals, findings: out.findings.length }));
}
