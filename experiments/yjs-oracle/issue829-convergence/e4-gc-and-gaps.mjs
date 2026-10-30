// E4: garbage collection and delete sets around a causal gap (issue 829).
// A gap is a same-client clock range the receiver has not seen while it holds
// later structs of that client: v14 fills it with a Skip struct, v13 parks the
// later structs in pendingStructs. Every shape here puts deleted, collected,
// formatted or re-encoded structs next to that gap before the gap is filled,
// then delivers the identical complete update set to every replica, runs
// all-pairs state-vector anti-entropy, and judges convergence.
//
// Usage: node e4-gc-and-gaps.mjs <13|14> [count=5000] [start=1] [gc=true|false|both]
import { writeFileSync } from 'node:fs';
import { load, rng, shuffle } from './lib.mjs';

const version = process.argv[2] || '14';
const count = Number(process.argv[3] || 5000);
const start = Number(process.argv[4] || 1);
const gcModes = (process.argv[5] || 'true') === 'both' ? [true, false] : [(process.argv[5] || 'true') === 'true'];
const L = await load(version);
const { Y } = L;

// Observables: the top-level text 't' (text and formatting runs, from lib.mjs)
// plus the nested node list 'a' (used by the nested shapes).
const arr = (d) => (version === '14' ? d.get('a') : d.getArray('a'));
const node = () => (version === '14' ? new Y.Node() : new Y.Text());
const inner = (d) => (arr(d).length ? arr(d).get(0) : null);
const nestedJSON = (d) => JSON.stringify(arr(d).toJSON());
const fp = (d) => L.key(d) + '|' + nestedJSON(d);
const same = (docs) => docs.every((d) => fp(d) === fp(docs[0]));
const skips = (d) => (d.store.skips ? [...d.store.skips.clients.entries()].map(([c, r]) => [c, r.getIds().map((x) => [x.clock, x.len])]) : []);
const structs = (d, c) => (d.store.clients.get(c) || []).map((s) => `${s.constructor.name}@${s.id.clock}+${s.length}${s.isItem ? ':' + s.content.constructor.name + (s.deleted ? '(del)' : '') : ''}`).join(' ');

/** Oracle verdict on documents that received the same complete update set. */
const judge = (docs) => {
  const fresh = docs.map((d) => L.reloaded(d, false));
  const out = {
    divergence: !same(docs),
    pending: docs.map(L.pending),
    svs: new Set(docs.map(L.sv)).size,
    reloadDivergence: !same(fresh) || fresh.some((f, i) => fp(f) !== fp(docs[i])),
    views: docs.map(fp),
  };
  for (const f of fresh) f.destroy();
  out.unresolved = out.pending.some((p) => p.structs || p.ds);
  out.failure = out.divergence || out.reloadDivergence || out.unresolved;
  return out;
};

const replica = (id, gc) => { const { d, updates } = L.doc(id, { gc }); arr(d); return { id, d, updates, gc }; };
const last = (r) => r.updates.at(-1);
const apply = (r, u) => Y.applyUpdate(r.d, u);

/**
 * Three replicas: A (client 1) authors the structs around the gap, B (client 2)
 * is the gap-bearing replica, C (client 3) is a bystander. B supplies an anchor
 * from its own client so that A's later structs depend only on structs B has.
 *
 * kind 'text':   A clock 0 'x' (after anchor b, withheld), clock 1 'h' (before b, present).
 * kind 'text2':  as 'text' plus clock 2 'y' (before h, withheld), clock 3 'z' (between h and b, present).
 * kind 'nested': anchor is a node holding 'm'; A clock 0 'p' (after m, withheld), clock 1 'q' (before m, present).
 */
function world(gc, kind) {
  const A = replica(1, gc), B = replica(2, gc), C = replica(3, gc);
  const named = {};
  if (kind === 'nested') {
    arr(B.d).insert(0, [node()]);
    inner(B.d).insert(0, 'm');
    for (const u of B.updates) { apply(A, u); apply(C, u); }
    inner(A.d).insert(1, 'p'); named.x = last(A);
    inner(A.d).insert(0, 'q'); named.h = last(A);
  } else {
    L.text(B.d).insert(0, 'b'); apply(A, last(B)); apply(C, last(B));
    L.text(A.d).insert(1, 'x'); named.x = last(A);
    L.text(A.d).insert(0, 'h'); named.h = last(A);
    if (kind === 'text2') {
      L.text(A.d).insert(0, 'y'); named.y = last(A);
      L.text(A.d).insert(2, 'z'); named.z = last(A);
    }
  }
  const present = kind === 'text2' ? [named.h, named.z] : [named.h];
  const withheld = kind === 'text2' ? [named.x, named.y] : [named.x];
  return { A, B, C, replicas: [A, B, C], named, present, withheld, kind, gc };
}

// Actions on the gap-bearing side while the predecessor is withheld.
const openGap = (w, targets = [w.B]) => { for (const r of targets) for (const u of w.present) apply(r, u); };
const deleteChars = (r, chars) => {
  const t = L.text(r.d);
  r.d.transact(() => { for (const ch of chars) { const i = t.toString().indexOf(ch); if (i >= 0) t.delete(i, 1); } });
};
/** Deletes the items behind the gap on replica r ('h' and 'z', or the nested node). */
const deleteBehind = (w, r) => { if (w.kind === 'nested') { if (arr(r.d).length) arr(r.d).delete(0, 1); } else deleteChars(r, ['h', 'z']); };
/** Inserts items whose origin is the item behind the gap. */
const insertAfterBehind = (w, r, chars) => {
  if (w.kind === 'nested') { const t = inner(r.d); if (t) { const i = t.toString().indexOf('q'); if (i >= 0) t.insert(i + 1, chars); } return; }
  const t = L.text(r.d); const i = t.toString().indexOf('h'); if (i >= 0) t.insert(i + 1, chars);
};
const formatAll = (r, formats) => { const t = L.text(r.d); if (t.length) t.format(0, t.length, formats); };
/** The author deletes a subset of its own characters in one transaction; returns that update. */
const authorDeletes = (w, chars) => { deleteChars(w.A, chars); return last(w.A); };
const relay = (from, to) => L.sync(from.d, to.d);
/** Replaces r's document with its re-encoded state loaded into a fresh document, keeping r's update log and client id. */
const reload = (r, v2 = false) => {
  const f = v2 ? L.reloadedV2(r.d) : L.reloaded(r.d);
  f.clientID = r.id; f.on('update', (u) => r.updates.push(u)); L.text(f); arr(f);
  r.d.destroy(); r.d = f;
};

// Ways the withheld predecessor can reach a replica.
const fillAlone = (w, r, order = w.withheld) => { for (const u of order) apply(r, u); };
const fillMerged = (w, r, extra = []) => apply(r, Y.mergeUpdates([...w.withheld, ...extra]));
const fillSync = (w, r, from = w.A) => relay(from, r);

/** Complete delivery of every recorded local update to every replica, then anti-entropy. */
function converge(w, r, { rounds = 12 } = {}) {
  let deliveryQuiescent = false;
  for (let round = 0; round < rounds; round++) {
    const batch = w.replicas.flatMap((x) => x.updates), before = batch.length;
    for (const x of w.replicas) {
      const ordered = shuffle(batch, r);
      for (let i = 0; i < ordered.length;) {
        const size = 1 + Math.floor(r() * 3), chunk = ordered.slice(i, i + size); i += size;
        const u = chunk.length === 1 ? chunk[0] : Y.mergeUpdates(chunk);
        apply(x, u); if (r() < 0.3) apply(x, u);
      }
    }
    if (w.replicas.flatMap((x) => x.updates).length === before) { deliveryQuiescent = true; break; }
  }
  const afterDelivery = w.replicas.map((x) => fp(x.d));
  let quiescent = false;
  for (let round = 0; round < rounds; round++) {
    const before = w.replicas.flatMap((x) => x.updates).length, old = JSON.stringify(w.replicas.map((x) => fp(x.d)));
    for (const i of shuffle([0, 1, 2], r)) for (const j of shuffle([0, 1, 2], r)) if (i !== j) relay(w.replicas[i], w.replicas[j]);
    if (w.replicas.flatMap((x) => x.updates).length === before && JSON.stringify(w.replicas.map((x) => fp(x.d))) === old) { quiescent = true; break; }
  }
  const v = judge(w.replicas.map((x) => x.d));
  return { ...v, deliveryQuiescent, quiescent, mismatchAfterDelivery: new Set(afterDelivery).size > 1 };
}
const destroy = (w) => { for (const x of w.replicas) x.d.destroy(); };

// Hand-built shapes. Each records the gap-bearing replica's structs for client 1
// and its pending stores before the fill (the transient), the text after the
// fill, and the final verdict against a hand-derived expectation.
const plainRuns = (view) => view.delta.every((run) => Object.keys(run.attributes).length === 0);
const boldRuns = (view) => view.delta.every((run) => run.attributes.bold === true);
function shape(name, kind, gc, body, expect) {
  const w = world(gc, kind);
  const r = rng(829);
  const rec = { name, kind, gc, version: L.pkg.version };
  try {
    body(w, rec);
    rec.afterFill = { B: L.view(w.B.d), Bnested: nestedJSON(w.B.d), pendingB: L.pending(w.B.d), structsB: structs(w.B.d, 1), skipsB: skips(w.B.d) };
    rec.final = converge(w, r);
    rec.expect = expect;
    const got = { text: L.view(w.B.d).text, nested: nestedJSON(w.B.d), view: L.view(w.B.d) };
    rec.got = { text: got.text, nested: got.nested, delta: got.view.delta };
    rec.pass = !rec.final.failure && (expect.text === undefined || expect.text === got.text) && (expect.nested === undefined || expect.nested === got.nested) && (expect.plain === undefined || plainRuns(got.view) === expect.plain) && (expect.bold === undefined || boldRuns(got.view) === expect.bold) && (expect.delta === undefined || JSON.stringify(expect.delta) === JSON.stringify(got.view.delta)) && (expect.structsB === undefined || expect.structsB === structs(w.B.d, 1));
  } catch (e) {
    rec.crash = { message: String(e && e.message), stack: String(e && e.stack) };
    rec.pass = false;
  }
  destroy(w);
  return rec;
}
const transient = (w, rec, label) => { (rec.transients ??= []).push({ label, B: L.view(w.B.d).text, Bnested: nestedJSON(w.B.d), pendingB: L.pending(w.B.d), structsB: structs(w.B.d, 1), skipsB: skips(w.B.d) }); };

const emptyNested = version === '14' ? '{}' : '[]';
/** v14 shows the item behind the gap (Skip), v13 hides it (pendingStructs); hand expectations differ accordingly. */
const vv = (v14, v13) => (version === '14' ? v14 : v13);
function handShapes(gc) {
  const S = [];
  // (1) The item behind the gap is deleted and collected beside the Skip, then the predecessor arrives alone, merged, or by sync.
  S.push(shape('deleteBehindGap_fillAlone', 'text', gc, (w, rec) => { openGap(w); deleteBehind(w, w.B); transient(w, rec, 'deleted h beside gap'); fillAlone(w, w.B); }, { text: vv('bx', 'hbx'), plain: true }));
  S.push(shape('deleteBehindGap_fillMergedWithLater', 'text', gc, (w, rec) => { openGap(w); deleteBehind(w, w.B); L.text(w.A.d).insert(3, 'w'); transient(w, rec, 'deleted h beside gap'); fillMerged(w, w.B, [last(w.A)]); }, { text: vv('bxw', 'hbxw'), plain: true }));
  S.push(shape('deleteBehindGap_fillBySync', 'text', gc, (w, rec) => { openGap(w); deleteBehind(w, w.B); transient(w, rec, 'deleted h beside gap'); fillSync(w, w.B); }, { text: vv('bx', 'hbx'), plain: true }));
  S.push(shape('deleteBehindGap_fillBySyncFromBystander', 'text', gc, (w, rec) => { openGap(w); deleteBehind(w, w.B); fillAlone(w, w.C); transient(w, rec, 'deleted h beside gap'); fillSync(w, w.B, w.C); }, { text: vv('bx', 'hbx'), plain: true }));
  S.push(shape('nestedGCBesideSkip_fillAlone', 'nested', gc, (w, rec) => { openGap(w); deleteBehind(w, w.B); transient(w, rec, 'node deleted, q collected beside gap'); fillAlone(w, w.B); }, { nested: emptyNested, structsB: gc ? 'GC@0+2' : undefined }));
  S.push(shape('nestedGCBesideSkip_fillBySync', 'nested', gc, (w, rec) => { openGap(w); deleteBehind(w, w.B); transient(w, rec, 'node deleted, q collected beside gap'); fillSync(w, w.B); }, { nested: emptyNested }));
  S.push(shape('nestedGCBesideSkip_fillMergedWithLater', 'nested', gc, (w, rec) => { openGap(w); deleteBehind(w, w.B); inner(w.A.d).insert(3, 'r'); transient(w, rec, 'node deleted, q collected beside gap'); fillMerged(w, w.B, [last(w.A)]); }, { nested: emptyNested }));
  // (2) The author's delete set covers the gap and the item behind it; it arrives before the predecessor.
  S.push(shape('authorDeleteSetSpansGap_before', 'text', gc, (w, rec) => { openGap(w); const ud = authorDeletes(w, ['h', 'x']); apply(w.B, ud); transient(w, rec, 'author delete set applied across gap'); fillAlone(w, w.B); }, { text: 'b', plain: true }));
  S.push(shape('authorDeleteSetSpansGap_reloadBefore', 'text', gc, (w, rec) => { openGap(w); const ud = authorDeletes(w, ['h', 'x']); apply(w.B, ud); reload(w.B); transient(w, rec, 'reloaded with pending delete set'); fillAlone(w, w.B); }, { text: 'b', plain: true }));
  S.push(shape('authorDeleteSetSpansGap_reloadV2Before', 'text', gc, (w, rec) => { openGap(w); const ud = authorDeletes(w, ['h', 'x']); apply(w.B, ud); reload(w.B, true); transient(w, rec, 'reloaded v2 with pending delete set'); fillAlone(w, w.B); }, { text: 'b', plain: true }));
  S.push(shape('authorDeleteSetSpansGap_mergedWithPredecessor', 'text', gc, (w, rec) => { openGap(w); const ud = authorDeletes(w, ['h', 'x']); transient(w, rec, 'gap open'); apply(w.B, Y.mergeUpdates([ud, ...w.withheld])); }, { text: 'b', plain: true }));
  S.push(shape('authorDeleteSetSpansGap_twoGaps', 'text2', gc, (w, rec) => { openGap(w); const ud = authorDeletes(w, ['h', 'x', 'y', 'z']); apply(w.B, ud); transient(w, rec, 'delete set across two gaps'); fillAlone(w, w.B); }, { text: 'b', plain: true }));
  S.push(shape('authorDeleteSetSpansGap_nested', 'nested', gc, (w, rec) => { openGap(w); const t = inner(w.A.d); w.A.d.transact(() => { t.delete(0, 1); t.delete(t.toString().indexOf('p'), 1); }); apply(w.B, last(w.A)); transient(w, rec, 'author delete set across nested gap'); fillAlone(w, w.B); }, { nested: version === '14' ? '{"children":[{"children":["m"]}]}' : '["m"]' }));
  // (3) Items whose origin is the item behind the gap are inserted on B, deleted and collected before the gap fills.
  S.push(shape('originBehindGapDeleted_fillAlone', 'text', gc, (w, rec) => { openGap(w); insertAfterBehind(w, w.B, 'ij'); deleteChars(w.B, ['h', 'i', 'j']); transient(w, rec, 'h i j deleted'); fillAlone(w, w.B); }, { text: vv('bx', 'hbx'), plain: true }));
  S.push(shape('originBehindGapDeleted_keepH', 'text', gc, (w, rec) => { openGap(w); insertAfterBehind(w, w.B, 'ij'); deleteChars(w.B, ['i', 'j']); transient(w, rec, 'i j deleted'); fillSync(w, w.B); }, { text: 'hbx', plain: true }));
  S.push(shape('originBehindGapDeleted_nested', 'nested', gc, (w, rec) => { openGap(w); insertAfterBehind(w, w.B, 'ij'); inner(w.B.d).delete(1, 2); deleteBehind(w, w.B); transient(w, rec, 'i j deleted then node collected'); fillAlone(w, w.B); }, { nested: emptyNested }));
  // (4) Formats spanning the gap position on B, with and without the unformat that deletes the markers.
  S.push(shape('formatSpanningGap_active', 'text', gc, (w, rec) => { openGap(w); formatAll(w.B, { bold: true }); transient(w, rec, 'bold over h b'); fillAlone(w, w.B); }, vv({ text: 'hbx', bold: true }, { text: 'hbx', delta: [{ attributes: {}, insert: 'h' }, { attributes: { bold: true }, insert: 'bx' }] })));
  S.push(shape('formatSpanningGap_unformatted', 'text', gc, (w, rec) => { openGap(w); formatAll(w.B, { bold: true }); formatAll(w.B, { bold: null }); transient(w, rec, 'bold then unbold over h b'); fillAlone(w, w.B); }, { text: 'hbx', plain: true }));
  S.push(shape('formatSpanningGap_unformatted_deleteBehind', 'text', gc, (w, rec) => { openGap(w); formatAll(w.B, { bold: true }); formatAll(w.B, { bold: null }); deleteBehind(w, w.B); transient(w, rec, 'bold, unbold, h deleted'); fillSync(w, w.B); }, { text: vv('bx', 'hbx'), plain: true }));
  S.push(shape('formatSpanningGap_authorUnformatBefore', 'text', gc, (w, rec) => { openGap(w); formatAll(w.B, { bold: true }); apply(w.A, last(w.B)); formatAll(w.A, { bold: null }); apply(w.B, last(w.A)); transient(w, rec, 'B bold, A unbold arrives before predecessor'); fillAlone(w, w.B); }, { text: 'hbx', plain: true }));
  // (5) Two gaps of the same client at B, with the present items deleted and collected.
  S.push(shape('twoGaps_deleteBoth_fillInOrder', 'text2', gc, (w, rec) => { openGap(w); deleteBehind(w, w.B); transient(w, rec, 'h z deleted beside two gaps'); fillAlone(w, w.B, [w.named.x, w.named.y]); }, { text: vv('ybx', 'yhzbx'), plain: true }));
  S.push(shape('twoGaps_deleteBoth_fillReversed', 'text2', gc, (w, rec) => { openGap(w); deleteBehind(w, w.B); transient(w, rec, 'h z deleted beside two gaps'); fillAlone(w, w.B, [w.named.y, w.named.x]); }, { text: vv('ybx', 'yhzbx'), plain: true }));
  S.push(shape('twoGaps_deleteBoth_fillMerged', 'text2', gc, (w, rec) => { openGap(w); deleteBehind(w, w.B); transient(w, rec, 'h z deleted beside two gaps'); fillMerged(w, w.B); }, { text: vv('ybx', 'yhzbx'), plain: true }));
  S.push(shape('twoGaps_deleteBoth_fillBySync', 'text2', gc, (w, rec) => { openGap(w); deleteBehind(w, w.B); transient(w, rec, 'h z deleted beside two gaps'); fillSync(w, w.B); }, { text: vv('ybx', 'yhzbx'), plain: true }));
  S.push(shape('twoGaps_deleteBoth_fillOneThenReload', 'text2', gc, (w, rec) => { openGap(w); deleteBehind(w, w.B); fillAlone(w, w.B, [w.named.y]); reload(w.B); transient(w, rec, 'one gap filled, reloaded'); fillAlone(w, w.B, [w.named.x]); }, { text: vv('ybx', 'yhzbx'), plain: true }));
  // (6) The gap-bearing state re-encoded and loaded into a fresh document before the predecessor arrives.
  S.push(shape('reloadBeforeFill_deleteBehind', 'text', gc, (w, rec) => { openGap(w); deleteBehind(w, w.B); reload(w.B); transient(w, rec, 'reloaded with deleted h beside gap'); fillAlone(w, w.B); }, { text: vv('bx', 'hbx'), plain: true }));
  S.push(shape('reloadV2BeforeFill_deleteBehind', 'text', gc, (w, rec) => { openGap(w); deleteBehind(w, w.B); reload(w.B, true); transient(w, rec, 'reloaded v2 with deleted h beside gap'); fillAlone(w, w.B); }, { text: vv('bx', 'hbx'), plain: true }));
  S.push(shape('reloadBeforeFill_nestedGC', 'nested', gc, (w, rec) => { openGap(w); deleteBehind(w, w.B); reload(w.B); transient(w, rec, 'reloaded with GC beside gap'); fillAlone(w, w.B); }, { nested: emptyNested }));
  S.push(shape('reloadBeforeFill_formatUnformat', 'text', gc, (w, rec) => { openGap(w); formatAll(w.B, { bold: true }); formatAll(w.B, { bold: null }); reload(w.B); transient(w, rec, 'reloaded after bold and unbold'); fillSync(w, w.B); }, { text: 'hbx', plain: true }));
  S.push(shape('reloadBeforeFill_twoGaps', 'text2', gc, (w, rec) => { openGap(w); deleteBehind(w, w.B); reload(w.B); transient(w, rec, 'reloaded with two gaps'); fillMerged(w, w.B); }, { text: vv('ybx', 'yhzbx'), plain: true }));
  // Relay of the gap-bearing state to the bystander, who deletes behind its own copy of the gap.
  S.push(shape('gapRelayedToBystander_bothDelete', 'text', gc, (w, rec) => { openGap(w); relay(w.B, w.C); deleteBehind(w, w.C); deleteBehind(w, w.B); transient(w, rec, 'B and C both hold the gap and deleted h'); fillSync(w, w.C); fillSync(w, w.B, w.C); }, { text: vv('bx', 'hbx'), plain: true }));
  S.push(shape('gapRelayedToBystander_deleteSetRelayed', 'text', gc, (w, rec) => { openGap(w); const ud = authorDeletes(w, ['h', 'x']); apply(w.B, ud); relay(w.B, w.C); transient(w, rec, 'pending delete set relayed by sync'); fillAlone(w, w.C); fillSync(w, w.B, w.C); }, { text: 'b', plain: true }));
  return S;
}

// Randomised campaign drawing from the same mechanisms.
function trial(seed, gc) {
  const r = rng(seed);
  const pick = (xs) => xs[Math.floor(r() * xs.length)];
  const kind = pick(['text', 'text', 'text2', 'nested']);
  const w = world(gc, kind);
  const trace = [{ kind }];
  const result = { seed, gc, kind, trace };
  try {
    const gapHolders = r() < 0.4 ? [w.B, w.C] : [w.B];
    openGap(w, gapHolders);
    trace.push({ op: 'openGap', targets: gapHolders.map((x) => x.id) });
    const n = 1 + Math.floor(r() * 5);
    const seenPendingDs = { B: false, C: false };
    for (let k = 0; k < n; k++) {
      const target = r() < 0.8 ? w.B : w.C;
      const op = pick(['deleteBehind', 'insertAfterBehind', 'insertAfterBehindThenDelete', 'format', 'unformat', 'authorDeleteSet', 'relayToOther', 'reload', 'reloadV2', 'localEdit', 'authorMore']);
      trace.push({ op, target: target.id });
      if (op === 'deleteBehind') deleteBehind(w, target);
      else if (op === 'insertAfterBehind') insertAfterBehind(w, target, String.fromCharCode(105 + k));
      else if (op === 'insertAfterBehindThenDelete') { const ch = String.fromCharCode(105 + k); insertAfterBehind(w, target, ch); if (kind === 'nested') { const t = inner(target.d); if (t) { const i = t.toString().indexOf(ch); if (i >= 0) t.delete(i, 1); } } else deleteChars(target, [ch, ...(r() < 0.5 ? ['h'] : [])]); }
      else if (op === 'format') formatAll(target, r() < 0.5 ? { bold: true } : { italic: true, bold: r() < 0.5 ? true : null });
      else if (op === 'unformat') formatAll(target, { bold: null, italic: null });
      else if (op === 'authorDeleteSet') { const all = kind === 'nested' ? ['p', 'q'] : kind === 'text2' ? ['h', 'x', 'y', 'z'] : ['h', 'x']; const chars = all.filter(() => r() < 0.6); if (chars.length) { if (kind === 'nested') { const t = inner(w.A.d); w.A.d.transact(() => { for (const ch of chars) { const i = t.toString().indexOf(ch); if (i >= 0) t.delete(i, 1); } }); } else deleteChars(w.A, chars); const ud = last(w.A); trace.at(-1).chars = chars; if (r() < 0.9) apply(target, ud); } }
      else if (op === 'relayToOther') { const other = target === w.B ? w.C : w.B; relay(target, other); trace.at(-1).to = other.id; }
      else if (op === 'reload') reload(target);
      else if (op === 'reloadV2') reload(target, true);
      else if (op === 'localEdit') {
        const t = L.text(target.d), len = t.length, pos = Math.floor(r() * (len + 1)), c = Math.floor(r() * 3);
        if (c === 0 || len === 0) { t.insert(pos, String.fromCharCode(65 + k), r() < 0.5 ? {} : { bold: true }); trace.at(-1).edit = ['insert', pos]; } else if (c === 1) { const from = Math.min(pos, len - 1); t.delete(from, 1 + Math.floor(r() * (len - from))); trace.at(-1).edit = ['delete', from]; } else { const from = Math.min(pos, len - 1); t.format(from, 1 + Math.floor(r() * (len - from)), r() < 0.5 ? { bold: null } : { bold: true }); trace.at(-1).edit = ['format', from]; }
      } else if (op === 'authorMore') {
        if (kind === 'nested') { const t = inner(w.A.d); t.insert(r() < 0.5 ? 0 : t.length, String.fromCharCode(97 + k)); } else { const t = L.text(w.A.d); t.insert(r() < 0.5 ? 0 : t.length, String.fromCharCode(97 + k)); }
        if (r() < 0.6) { apply(target, last(w.A)); trace.at(-1).delivered = true; }
      }
      for (const x of [w.B, w.C]) if (L.pending(x.d).ds) seenPendingDs[x.id === 2 ? 'B' : 'C'] = true;
    }
    result.beforeFill = { B: structs(w.B.d, 1), skipsB: skips(w.B.d), pendingB: L.pending(w.B.d), pendingC: L.pending(w.C.d), seenPendingDs };
    const mode = pick(['alone', 'aloneShuffled', 'merged', 'mergedWithLater', 'sync', 'syncViaC', 'reloadThenAlone']);
    result.fill = mode;
    if (mode === 'alone') fillAlone(w, w.B);
    else if (mode === 'aloneShuffled') fillAlone(w, w.B, shuffle(w.withheld, r));
    else if (mode === 'merged') fillMerged(w, w.B);
    else if (mode === 'mergedWithLater') fillMerged(w, w.B, w.A.updates.filter(() => r() < 0.5));
    else if (mode === 'sync') fillSync(w, w.B);
    else if (mode === 'syncViaC') { fillAlone(w, w.C); fillSync(w, w.B, w.C); }
    else { reload(w.B, r() < 0.5); fillAlone(w, w.B); }
    result.afterFill = { B: structs(w.B.d, 1), skipsB: skips(w.B.d), pendingB: L.pending(w.B.d), textB: L.view(w.B.d).text, textA: L.view(w.A.d).text };
    result.final = converge(w, r);
  } catch (e) {
    result.crash = { message: String(e && e.message), stack: String(e && e.stack) };
  }
  destroy(w);
  return result;
}

// Oracle controls: the fingerprint must see a missing insert, a missing format and a missing nested insert, and stop seeing them once delivered.
{
  const a = replica(7, true), b = replica(8, true);
  L.text(a.d).insert(0, 'x'); if (same([a.d, b.d])) throw new Error('control: missing insert not detected');
  relay(a, b); if (!same([a.d, b.d])) throw new Error('control: delivered insert still differs');
  L.text(a.d).format(0, 1, { bold: true }); if (same([a.d, b.d])) throw new Error('control: missing format not detected');
  relay(a, b); if (!same([a.d, b.d])) throw new Error('control: delivered format still differs');
  arr(a.d).insert(0, [node()]); inner(a.d).insert(0, 'n'); if (same([a.d, b.d])) throw new Error('control: missing nested insert not detected');
  relay(a, b); if (!same([a.d, b.d])) throw new Error('control: delivered nested insert still differs');
  const c = L.reloaded(a.d, false); if (fp(c) !== fp(a.d)) throw new Error('control: reload fingerprint differs'); c.destroy();
  a.d.destroy(); b.d.destroy();
}

const summary = { package: L.pkg.name, version: L.pkg.version, node: process.version, start, count, gcModes, started: new Date().toISOString(), hand: [], trials: 0, failures: 0, divergences: 0, reloadDivergences: 0, unresolved: 0, nonquiescent: 0, crashes: 0, deliveryMismatches: 0, transients: { pendingDsSeen: 0, skipsAtBBeforeFill: 0, pendingStructsAtBBeforeFill: 0, pendingAfterFill: 0, textDiffersAfterFill: 0 }, transientExamples: { pendingAfterFill: [], pendingDsSeen: [] }, groups: [], findings: [] };
console.log(JSON.stringify({ event: 'START', package: summary.package, version: summary.version, node: summary.node, count, start, gcModes }));
for (const gc of gcModes) {
  const hand = handShapes(gc);
  summary.hand.push(...hand);
  for (const h of hand) console.log(JSON.stringify({ event: 'HAND', name: h.name, gc, pass: h.pass, got: h.got, expect: h.expect, transients: h.transients, final: h.final && { divergence: h.final.divergence, reloadDivergence: h.final.reloadDivergence, unresolved: h.final.unresolved, svs: h.final.svs }, crash: h.crash }));
}
summary.handFailures = summary.hand.filter((h) => !h.pass).length;
for (const gc of gcModes) {
  const group = { gc, trials: 0, failures: 0, divergences: 0, reloadDivergences: 0, unresolved: 0, nonquiescent: 0, crashes: 0, deliveryMismatches: 0, kinds: {}, fills: {} };
  for (let k = 0; k < count; k++) {
    const seed = Math.imul(start + k, 0x9e3779b1) >>> 0;
    const t = trial(seed, gc);
    group.trials++; summary.trials++;
    group.kinds[t.kind] = (group.kinds[t.kind] || 0) + 1; if (t.fill) group.fills[t.fill] = (group.fills[t.fill] || 0) + 1;
    if (t.beforeFill) { if (t.beforeFill.seenPendingDs.B || t.beforeFill.seenPendingDs.C) { summary.transients.pendingDsSeen++; if (summary.transientExamples.pendingDsSeen.length < 3) summary.transientExamples.pendingDsSeen.push({ seed: t.seed, gc, kind: t.kind, fill: t.fill, trace: t.trace, beforeFill: t.beforeFill, afterFill: t.afterFill }); } if (t.beforeFill.skipsB.length) summary.transients.skipsAtBBeforeFill++; if (t.beforeFill.pendingB.structs) summary.transients.pendingStructsAtBBeforeFill++; }
    if (t.afterFill) { if (t.afterFill.pendingB.structs || t.afterFill.pendingB.ds) { summary.transients.pendingAfterFill++; if (summary.transientExamples.pendingAfterFill.length < 5) summary.transientExamples.pendingAfterFill.push({ seed: t.seed, gc, kind: t.kind, fill: t.fill, trace: t.trace, beforeFill: t.beforeFill, afterFill: t.afterFill }); } if (t.afterFill.textB !== t.afterFill.textA) summary.transients.textDiffersAfterFill++; }
    const f = t.final || {};
    const flags = [['crashes', !!t.crash], ['divergences', !!f.divergence], ['reloadDivergences', !!f.reloadDivergence], ['unresolved', !!f.unresolved], ['nonquiescent', t.final && (!f.quiescent || !f.deliveryQuiescent)], ['deliveryMismatches', !!f.mismatchAfterDelivery]];
    for (const [name, flag] of flags) if (flag) { group[name]++; summary[name]++; }
    const failure = !!t.crash || !!f.failure || (t.final && (!f.quiescent || !f.deliveryQuiescent));
    if (failure) { group.failures++; summary.failures++; if (summary.findings.length < 20) summary.findings.push(t); console.log(JSON.stringify({ event: 'FINDING', ...t })); }
    if (k % 1000 === 999) console.log(JSON.stringify({ event: 'PROGRESS', version: L.pkg.version, ...group }));
  }
  summary.groups.push(group);
}
summary.finished = new Date().toISOString();
writeFileSync(new URL(`e4-gc-and-gaps-results${version === '14' ? '' : '-v13'}.json`, import.meta.url), JSON.stringify(summary, null, 2) + '\n');
console.log(JSON.stringify({ event: 'DONE', package: summary.package, version: summary.version, trials: summary.trials, failures: summary.failures, divergences: summary.divergences, reloadDivergences: summary.reloadDivergences, unresolved: summary.unresolved, nonquiescent: summary.nonquiescent, crashes: summary.crashes, deliveryMismatches: summary.deliveryMismatches, handFailures: summary.handFailures, transients: summary.transients }));
