/**
 * Measured facts about Y.Text in the pinned Yjs release. Each fact runs a
 * fixed scenario, compares the observation with a hand-derived expected
 * value, and checks a negative companion (a tempting wrong answer that must
 * not be produced). Writes results/facts.json.
 *
 * Notation for displayed text: characters separated by spaces, `*` marks
 * bold, e.g. 'a b* c'. Ids are [client, clock].
 */
import { mkdirSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { isDeepStrictEqual } from 'node:util';
import { verifySources, Replica } from '../../ra-pbt/instances/yjs/index.js';

const here = dirname(fileURLToPath(import.meta.url));

/** 'a b* c' -> [{ch:'a',attrs:{}}, {ch:'b',attrs:{bold:true}}, {ch:'c',attrs:{}}] */
const parse = (s) => (s === '' ? [] : s.split(' ').map((t) => (t.endsWith('*') ? { ch: t.slice(0, -1), attrs: { bold: true } } : { ch: t, attrs: {} })));
/** Inverse of parse for bold-only text; other attributes are shown as {..}. */
const render = (vis) => vis.map((v) => {
  const { bold, ...rest } = v.attrs;
  if (Object.keys(rest).length) return `${v.ch}${JSON.stringify(v.attrs)}`;
  return bold === true ? `${v.ch}*` : v.ch;
}).join(' ');
const shows = (r, s) => isDeepStrictEqual(r.visible(), parse(s));

/** Replica with base content 'abc' written by client 1. */
const abc = (client = 1) => {
  const r = new Replica(client);
  r.insert(0, 'abc', {});
  return r;
};
/** Replica with 'a b* c': 'abc' by client 1, then client 1 bolds b. */
const aBc = (client = 1) => {
  const r = abc(client);
  r.format(1, 1, { bold: true });
  return r;
};
/** Fresh replica with the given client id holding the same state as src. */
const fork = (src, client) => {
  const r = new Replica(client);
  r.syncFrom(src);
  return r;
};
/**
 * Delivers each replica's op to the other, then forwards any updates Yjs
 * emitted while integrating (formatting cleanup) until both are quiet.
 */
const exchange = (x, opX, y, opY) => {
  const log = [];
  let qx = y.deliver(opX).emitted.map((u) => ({ from: y, u }));
  let qy = x.deliver(opY).emitted.map((u) => ({ from: x, u }));
  let queue = [...qx, ...qy];
  log.push({ emittedBy: { [y.clientID]: qx.length, [x.clientID]: qy.length } });
  while (queue.length) {
    const next = [];
    for (const { from, u } of queue) {
      const to = from === x ? y : x;
      for (const e of to.deliver({ update: u }).emitted) next.push({ from: to, u: e });
    }
    queue = next;
  }
  return log;
};

const facts = [];
const record = (f) => {
  facts.push(f);
  const tag = f.observationOnly ? (f.matched ? 'MATCH' : 'DIFFERS') : (f.pass ? 'PASS' : 'FAIL');
  console.log(`${tag.padEnd(7)} ${f.name}`);
};

verifySources();

// a. Identity of characters and format markers.
{
  const r = aBc();
  const items = r.items().map(({ id, kind, str, key, value, deleted }) => (kind === 'string' ? { id, kind, str, deleted } : { id, kind, key, value, deleted }));
  const expected = [
    { id: [1, 0], kind: 'string', str: 'a', deleted: false },
    { id: [1, 3], kind: 'format', key: 'bold', value: true, deleted: false },
    { id: [1, 1], kind: 'string', str: 'b', deleted: false },
    { id: [1, 4], kind: 'format', key: 'bold', value: null, deleted: false },
    { id: [1, 2], kind: 'string', str: 'c', deleted: false },
  ];
  const markersDeleted = items.filter((i) => i.kind === 'format').some((i) => i.deleted);
  const ok = isDeepStrictEqual(items, expected);
  record({
    name: 'a. per-character ids and marker ids',
    setup: "client 1: insert(0,'abc'); format(1,1,{bold:true})",
    observed: items,
    expected,
    negative: { claim: 'the two markers are deleted items', holds: !markersDeleted },
    pass: ok && !markersDeleted,
  });
}

// b. Insertion attribute policy at the edges of a bold run.
{
  const cases = [
    { index: 1, attrs: {}, expected: 'a X b* c' },
    { index: 2, attrs: {}, expected: 'a b* X c' },
    { index: 3, attrs: {}, expected: 'a b* c X' },
    { index: 1, attrs: { bold: true }, expected: 'a X* b* c' },
  ];
  const observed = cases.map(({ index, attrs, expected }) => {
    const r = aBc();
    r.insert(index, 'X', attrs);
    return { index, attrs, expected, observed: render(r.visible()), ok: shows(r, expected) };
  });
  const r2 = aBc();
  r2.insert(2, 'X', {});
  const negHolds = !shows(r2, 'a b* X* c');
  record({
    name: 'b. explicit attributes: no inheritance from neighbours',
    setup: "from 'a b* c' (client 1), insert 'X' with attrs {} at 1, 2, 3 and with {bold:true} at 1",
    observed,
    expected: cases.map((c) => c.expected),
    negative: { claim: "X inserted with {} at 2 shows bold ('a b* X* c')", holds: negHolds },
    pass: observed.every((o) => o.ok) && negHolds,
  });
}
{
  // Attributes omitted: YText.insert copies the attributes in effect just after
  // the left neighbour character (none at index 0).
  const cases = [
    { index: 0, expected: 'X a b* c' },
    { index: 1, expected: 'a X b* c' },
    { index: 2, expected: 'a b* X* c' },
    { index: 3, expected: 'a b* c X' },
  ];
  const observed = cases.map(({ index, expected }) => {
    const r = aBc();
    const op = r.insert(index, 'X');
    return { index, expected, observed: render(r.visible()), newMarkers: op.markers.length, ok: shows(r, expected) };
  });
  const r2 = aBc();
  r2.insert(2, 'X');
  const negHolds = !shows(r2, 'a b* X c');
  record({
    name: 'b. omitted attributes: inherit from the left neighbour',
    setup: "from 'a b* c' (client 1), insert 'X' with attrs omitted at 0, 1, 2, 3",
    observed,
    expected: cases.map((c) => c.expected),
    negative: { claim: "X inserted with attrs omitted at 2 is plain ('a b* X c')", holds: negHolds },
    pass: observed.every((o) => o.ok) && negHolds,
  });
}

// c. Concurrent format versus insert inside the range.
{
  const base = abc();
  const r4 = fork(base, 4);
  const r5 = fork(base, 5);
  const f = r4.format(0, 3, { bold: true });
  const i = r5.insert(1, 'X', {});
  const log = exchange(r4, f, r5, i);
  const expected = 'a* X* b* c*';
  const ok = shows(r4, expected) && shows(r5, expected);
  const neg = !shows(r4, 'a* X b* c*') && !shows(r5, 'a* X b* c*');
  record({
    name: 'c. concurrent bold [0,3) and plain insert at 1',
    setup: "base 'abc' (client 1); client 4 format(0,3,{bold:true}) || client 5 insert(1,'X',{}); exchange",
    observed: { 4: render(r4.visible()), 5: render(r5.visible()), log },
    expected,
    negative: { claim: "X is plain ('a* X b* c*')", holds: neg },
    pass: ok && neg,
  });
}

// d. Concurrent bold [0,2) versus unbold [1,3) from 'a b* c'.
{
  const seq = (first) => {
    const r = aBc(1);
    const s = fork(r, 12);
    if (first === 'bold') {
      s.format(0, 2, { bold: true });
      s.format(1, 2, { bold: null });
    } else {
      s.format(1, 2, { bold: null });
      s.format(0, 2, { bold: true });
    }
    return s;
  };
  const sBU = seq('bold');
  const sUB = seq('unbold');
  const seqBoldThenUnbold = 'a* b c';
  const seqUnboldThenBold = 'a* b* c';
  const seqOk = shows(sBU, seqBoldThenUnbold) && shows(sUB, seqUnboldThenBold);

  const base = aBc(1);
  const r10 = fork(base, 10);
  const r11 = fork(base, 11);
  const bold = r10.format(0, 2, { bold: true });
  const unbold = r11.format(1, 2, { bold: null });
  const itemsBefore = { 10: r10.items(), 11: r11.items() };
  const log = exchange(r10, bold, r11, unbold);
  const expected = 'a* b* c*';
  const ok = shows(r10, expected) && shows(r11, expected);
  const neg = !shows(r10, seqBoldThenUnbold) && !shows(r10, seqUnboldThenBold)
    && !shows(r11, seqBoldThenUnbold) && !shows(r11, seqUnboldThenBold);
  record({
    name: 'd. concurrent bold [0,2) and unbold [1,3)',
    setup: "base 'a b* c' (client 1); client 10 format(0,2,{bold:true}) || client 11 format(1,2,{bold:null}); exchange",
    observed: {
      10: render(r10.visible()),
      11: render(r11.visible()),
      ops: { bold: { markers: bold.markers, range: bold.range }, unbold: { markers: unbold.markers, range: unbold.range } },
      itemsBeforeExchange: itemsBefore,
      itemsAfter: { 10: r10.items(), 11: r11.items() },
      log,
      sequential: { boldThenUnbold: render(sBU.visible()), unboldThenBold: render(sUB.visible()) },
    },
    expected: { concurrent: expected, boldThenUnbold: seqBoldThenUnbold, unboldThenBold: seqUnboldThenBold },
    negative: { claim: 'the converged state equals one of the two sequential outcomes', holds: neg },
    pass: ok && seqOk && neg,
  });
}

// e. Pending structs when a causal predecessor is missing.
{
  const w = new Replica(1);
  const first = w.insert(0, 'ab', {});
  const second = w.insert(2, 'c', {});
  const r = new Replica(13);
  const d2 = r.deliver(second);
  const whilePending = { pending: d2.pending, text: r.string() };
  const d1 = r.deliver(first);
  const after = { pending: d1.pending, text: r.string() };
  const ok = whilePending.pending === true && whilePending.text === '' && after.pending === false && after.text === 'abc';
  const neg = whilePending.text !== 'abc' && whilePending.text !== 'c';
  record({
    name: 'e. pending structs',
    setup: "client 1 insert(0,'ab'), insert(2,'c'); fresh doc receives the second update, then the first",
    observed: { whilePending, after },
    expected: { whilePending: { pending: true, text: '' }, after: { pending: false, text: 'abc' } },
    negative: { claim: "text is 'abc' or 'c' while the predecessor is missing", holds: neg },
    pass: ok && neg,
  });
}

// f. Deleting across markers.
{
  const r = aBc();
  r.delete(0, 2);
  const markers = r.items().filter((i) => i.kind === 'format').map(({ id, key, value, deleted }) => ({ id, key, value, deleted }));
  const expectedMarkers = [
    { id: [1, 3], key: 'bold', value: true, deleted: true },
    { id: [1, 4], key: 'bold', value: null, deleted: true },
  ];
  const ok = shows(r, 'c') && isDeepStrictEqual(markers, expectedMarkers);
  const neg = !shows(r, 'c*');
  record({
    name: 'f. delete(0,2) across both markers',
    setup: "from 'a b* c' (client 1), delete(0,2)",
    observed: { text: render(r.visible()), markers },
    expected: { text: 'c', markers: expectedMarkers },
    negative: { claim: "c becomes bold ('c*')", holds: neg },
    pass: ok && neg,
  });
}

// g. Concurrent delete and format over the deleted character.
{
  const base = abc();
  const r6 = fork(base, 6);
  const r7 = fork(base, 7);
  const del = r6.delete(1, 1);
  const fmt = r7.format(0, 3, { bold: true });
  const log = exchange(r6, del, r7, fmt);
  const expected = 'a* c*';
  const ok = shows(r6, expected) && shows(r7, expected);
  const neg = ['a* c', 'a c*', 'a* b* c*'].every((s) => !shows(r6, s) && !shows(r7, s));
  record({
    name: 'g. delete b || bold [0,3)',
    setup: "base 'abc' (client 1); client 6 delete(1,1) || client 7 format(0,3,{bold:true}); exchange",
    observed: { 6: render(r6.visible()), 7: render(r7.visible()), log },
    expected,
    negative: { claim: "result is 'a* c', 'a c*' or resurrects b", holds: neg },
    pass: ok && neg,
  });
}

// h. Format across a tombstone || insert at the tombstone.
{
  const base = abc();
  base.delete(1, 1);
  const r8 = fork(base, 8);
  const r9 = fork(base, 9);
  const fmt = r8.format(0, 2, { bold: true });
  const ins = r9.insert(1, 'X', {});
  const log = exchange(r8, fmt, r9, ins);
  // Interval meaning: the format covers the interval from a to c; X lands between a and c.
  const expected = 'a* X* c*';
  const matched = shows(r8, expected) && shows(r9, expected);
  record({
    name: 'h. bold over a..c across tombstone b || insert X between a and c',
    setup: "base 'abc' with b deleted (client 1); client 8 format(0,2,{bold:true}) || client 9 insert(1,'X',{}); exchange",
    observed: { 8: render(r8.visible()), 9: render(r9.visible()), items: r8.items(), formatRange: fmt.range, insertChar: ins.chars[0], log },
    expected,
    negative: { claim: "X is plain ('a* X c*')", holds: !shows(r8, 'a* X c*') && !shows(r9, 'a* X c*') },
    observationOnly: true,
    matched,
  });
}

// i. The same request on the same displayed text gives different results on
// a replica that opened the document after its formatting existed.
{
  const src = aBc();
  const created = fork(src, 12);
  const opened = new Replica(13, { loaded: true });
  opened.loadFrom(src);
  const sameDisplay = isDeepStrictEqual(created.visible(), opened.visible());
  created.insert(2, 'X');
  opened.insert(2, 'X');
  const expected = { created: 'a b* X* c', opened: 'a b* X c' };
  const ok = sameDisplay && shows(created, expected.created) && shows(opened, expected.opened);
  const neg = !isDeepStrictEqual(created.visible(), opened.visible());
  record({
    name: 'i. omitted attributes on a created versus an opened replica',
    setup: "from 'a b* c' (client 1): client 12 holds the text type before receiving the state, client 13 applies the state first and takes the text type afterwards; both insert 'X' at 2 with attrs omitted",
    observed: { sameDisplayBefore: sameDisplay, created: render(created.visible()), opened: render(opened.visible()) },
    expected,
    negative: { claim: 'the two replicas agree', holds: neg },
    pass: ok && neg,
  });
}

// j. Delete on an opened replica deletes a closing marker and spreads the run.
{
  const src = abc();
  src.format(0, 2, { bold: true });
  const created = fork(src, 14);
  const opened = new Replica(15, { loaded: true });
  opened.loadFrom(src);
  const sameDisplay = shows(created, 'a* b* c') && shows(opened, 'a* b* c');
  const dc = created.delete(1, 1);
  const dop = opened.delete(1, 1);
  const expected = { created: 'a* c', opened: 'a* c*' };
  const removed = (op) => op.deletedMarkers.map(({ id, key, value }) => ({ id, key, value }));
  const expectedRemoved = { created: [], opened: [{ id: [1, 4], key: 'bold', value: null }] };
  const ok = sameDisplay && shows(created, expected.created) && shows(opened, expected.opened)
    && isDeepStrictEqual(removed(dc), expectedRemoved.created) && isDeepStrictEqual(removed(dop), expectedRemoved.opened);
  const neg = !shows(created, 'a* c*') && !shows(opened, 'a* c');
  record({
    name: 'j. delete on an opened replica spreads formatting to the right neighbour',
    setup: "client 1: insert(0,'abc',{}); format(0,2,{bold:true}) giving 'a* b* c'; client 14 holds the text type before receiving the state, client 15 applies the state first; both delete(1,1)",
    observed: { sameDisplayBefore: sameDisplay, created: render(created.visible()), opened: render(opened.visible()), deletedMarkers: { created: removed(dc), opened: removed(dop) } },
    expected: { ...expected, deletedMarkers: expectedRemoved },
    negative: { claim: "the created replica spreads bold ('a* c*') or the opened one gives the list edit ('a* c')", holds: neg },
    pass: ok && neg,
  });
}

// k. Opened replicas skip the formatting cleanup after a remote transaction.
{
  const base = abc();
  const r16 = fork(base, 16);
  const r17 = fork(base, 17);
  r16.format(1, 1, { bold: true });
  r17.format(1, 1, { bold: true });
  // Merging two identical concurrent bolds leaves two bold:true and two bold:null markers around b.
  const merged = new Replica(18);
  merged.syncFrom(r16);
  merged.syncFrom(r17);
  const sender = fork(base, 19);
  const del = sender.delete(1, 1);
  const created = fork(merged, 20);
  const opened = new Replica(21, { loaded: true });
  opened.loadFrom(merged);
  const liveMarkers = (r) => r.items().filter((it) => it.kind === 'format' && !it.deleted).length;
  const before = { merged: render(merged.visible()), liveMarkers: liveMarkers(merged) };
  const ec = created.deliver(del).emitted.length;
  const eo = opened.deliver(del).emitted.length;
  const observed = {
    before,
    created: { text: render(created.visible()), cleanupUpdates: ec, liveMarkers: liveMarkers(created) },
    opened: { text: render(opened.visible()), cleanupUpdates: eo, liveMarkers: liveMarkers(opened) },
  };
  const expected = {
    before: { merged: 'a b* c', liveMarkers: 4 },
    created: { text: 'a c', cleanupUpdates: 1, liveMarkers: 1 },
    opened: { text: 'a c', cleanupUpdates: 0, liveMarkers: 4 },
  };
  const ok = isDeepStrictEqual(observed, expected);
  const neg = observed.created.cleanupUpdates !== observed.opened.cleanupUpdates && observed.created.liveMarkers !== observed.opened.liveMarkers;
  record({
    name: 'k. opened replicas skip the post-transaction formatting cleanup',
    setup: "base 'abc' (client 1); clients 16 and 17 each format(1,1,{bold:true}); client 18 merges both; client 19 (from the plain base) delete(1,1); the delete is delivered to client 20 (created from 18's state) and client 21 (opened from 18's state)",
    observed,
    expected,
    negative: { claim: 'the opened receiver also emits a cleanup update and keeps one live marker', holds: neg },
    pass: ok && neg,
  });
}

verifySources();

const out = {
  yjs: verifySources(),
  node: process.version,
  sourcesVerified: true,
  status: 'measured on the pinned version; not proved',
  facts,
};
mkdirSync(join(here, 'results'), { recursive: true });
writeFileSync(join(here, 'results', 'facts.json'), JSON.stringify(out, null, 2) + '\n');
const asserted = facts.filter((f) => !f.observationOnly);
const failed = asserted.filter((f) => !f.pass);
const observed = facts.filter((f) => f.observationOnly);
console.log(`${asserted.length - failed.length}/${asserted.length} asserted facts pass; ${observed.filter((f) => f.matched).length}/${observed.length} observations match the interval reading; wrote results/facts.json`);
if (failed.length) process.exitCode = 1;
