/**
 * Y.Text edits on an opened replica versus a created replica.
 *
 * A created replica takes its text type (`doc.getText('t')`) before any state
 * arrives; an opened replica applies a stored or served state first and takes
 * the text type afterwards. Every scenario below builds a source state on
 * client 1, encodes it once with `Y.encodeStateAsUpdate`, applies the same
 * bytes to one replica of each kind (both client 2), issues the same index
 * requests on both, and compares each displayed text with a hand-derived
 * expected value. The oracle for each step is the index-level list edit
 * `spec.localEdit`; for an insert with attributes omitted, the request is
 * read with the attributes of the left neighbour (none at index 0), which is
 * Yjs's documented policy and what a created replica does (fact b). Each
 * expected value is also checked to be `localEdit` of the previous expected
 * view, so a mistake in a hand derivation fails the run.
 *
 * For each step the module also states the opened replica's outcome as
 * predicted from the mechanism below, and asserts both the created outcome
 * (equal to the oracle) and the opened outcome (equal to the prediction).
 * Every scenario carries a negative companion. Writes
 * results/opened-document.json and exits non-zero on a failed assertion.
 *
 * Mechanism, in node_modules/yjs/dist/yjs.mjs of yjs@13.6.31:
 *
 * Where the flags are lost. Decoding an update resolves a root parent name
 * with `doc.get(name)` (lines 1430, 1454), which creates a placeholder
 * `AbstractType` when the name is not yet defined. `ContentFormat.integrate`
 * (lines 8991-8996) sets `_searchMarker = null` and `_hasFormatting = true`
 * on that placeholder. A later `getText` (line 628) reaches `Doc.get`
 * (lines 577-608), which builds a fresh `YText` (constructor lines 7053-7069:
 * `_searchMarker = []`, `_hasFormatting = false`) and copies only `_map`,
 * `_start` and `_length` from the placeholder (lines 588-599). The two flags
 * stay on the discarded placeholder. Root-level text only: a Y.Text nested
 * in a map or a Y.XmlText in a fragment is decoded with its own constructor
 * and keeps both flags.
 *
 * Which operations read search markers. `findPosition` (line 6327) consults
 * `findMarker` (line 4849) when its last argument is true. `YText.insert`
 * passes `!attributes` (line 7329), so inserts with attributes omitted use
 * markers; `insertEmbed` likewise (7356); `YText.delete` always passes true
 * (7379); `YText.format` passes false (7403). `findMarker` returns null at
 * index 0 and when `_searchMarker` is null (4850), which is why a created
 * replica, whose formatted text has `_searchMarker = null`, never uses one.
 * With a marker, `findPosition` starts at `marker.p.left` with an empty
 * attribute map (6330-6332), so format items to the left of `marker.p` are
 * not counted. `findMarker` stops on the first item at or past the index and
 * then backs over items that are clock-contiguous with their left neighbour
 * (4878-4883), so `marker.p` is a format item, or a string item whose left
 * neighbour is a format item; in both cases the attributes in force there
 * are missed. `deleteText` (line 6737) copies those wrong attributes as
 * `startAttrs` (6739) and calls `cleanupFormattingGap` (6564), which deletes
 * a format item whose value equals the start value (6592): a closing marker
 * (value null) is then judged redundant and deleted, and the run's
 * formatting spreads to the right neighbour. An insert with attributes
 * omitted copies the empty map and so does not inherit. Markers persist
 * across edits (`updateMarkerChanges`, line 4931, called from 6465 and 6761),
 * so later edits on the same replica use them too.
 *
 * Which cleanup is skipped. After a remote transaction `YText._callObserver`
 * sets `_needFormattingCleanup` only when `_hasFormatting` is true (7123);
 * the transaction then calls `cleanupYTextAfterTransaction` (3300-3301,
 * 6684), whose per-item gate also checks `_hasFormatting` (6707). An opened
 * replica therefore never runs the post-transaction cleanup. Local
 * transactions never run it on either kind.
 *
 * Healing. Any format item integrated into the text later, by a local
 * `format` or an insert with attributes that creates a marker, or by a
 * remote update carrying one, runs `ContentFormat.integrate` on the real
 * `YText` and sets both flags; from then on the replica behaves as created.
 *
 * Notation: characters separated by spaces; suffix `*` bold, `_` italic,
 * `*_` both.
 */
import { mkdirSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { isDeepStrictEqual } from 'node:util';
import { Y, verifySources, Replica, localEdit, viewsEqual, normaliseAttrs } from '../../ra-pbt/instances/yjs/index.js';

const here = dirname(fileURLToPath(import.meta.url));

/** 'a* b c_' -> [{ch:'a',attrs:{bold:true}}, {ch:'b',attrs:{}}, {ch:'c',attrs:{italic:true}}] */
const parse = (s) => (s === '' ? [] : s.split(' ').map((t) => {
  const attrs = {};
  if (t.slice(1).includes('*')) attrs.bold = true;
  if (t.slice(1).includes('_')) attrs.italic = true;
  return { ch: t[0], attrs };
}));
const render = (vis) => vis.map((v) => {
  const { bold, italic, ...rest } = normaliseAttrs(v.attrs);
  if (Object.keys(rest).length) return `${v.ch}${JSON.stringify(v.attrs)}`;
  return v.ch + (bold === true ? '*' : '') + (italic === true ? '_' : '');
}).join(' ');
const shows = (vis, s) => viewsEqual(vis, parse(s));

const describe = (q) => {
  if (q.kind === 'insert') return `insert ${q.index} "${q.text}"${q.attrs === undefined ? ' (attrs omitted)' : ' ' + JSON.stringify(q.attrs)}`;
  if (q.kind === 'delete') return `delete [${q.index},${q.index + q.len})`;
  return `format [${q.index},${q.index + q.len}) ${JSON.stringify(q.attrs)}`;
};

/** Issues an index request on a replica; attrs undefined means omitted. */
const issue = (r, q) => {
  if (q.kind === 'insert') return q.attrs === undefined ? r.insert(q.index, q.text) : r.insert(q.index, q.text, q.attrs);
  if (q.kind === 'delete') return r.delete(q.index, q.len);
  // A format that changes nothing emits no update, which the op record refuses.
  if (q.unchanged) {
    r.text.format(q.index, q.len, { ...q.attrs });
    return { deletedMarkers: [] };
  }
  return r.format(q.index, q.len, q.attrs);
};

/** The oracle request: omitted insert attributes read as the left neighbour's. */
const oracleRequest = (view, q) => {
  if (q.kind !== 'insert' || q.attrs !== undefined) return q;
  return { ...q, attrs: q.index > 0 ? { ...view[q.index - 1].attrs } : {} };
};

const sourceOf = (build) => {
  const s = new Replica(1);
  for (const q of build) issue(s, q);
  return s;
};

/** One created and one opened replica (both client 2) from identical bytes. */
const forksOf = (src) => {
  const bytes = Y.encodeStateAsUpdate(src.doc);
  const created = new Replica(2);
  Y.applyUpdate(created.doc, bytes);
  const opened = new Replica(2, { loaded: true });
  Y.applyUpdate(opened.doc, bytes);
  return { bytes, created, opened };
};

const flags = (r) => ({ searchMarker: r.text._searchMarker === null ? null : r.text._searchMarker.map((m) => m.index), hasFormatting: r.text._hasFormatting });

const derivationErrors = [];

/**
 * Runs `steps` on both kinds. Each step: { request, expected, opened }
 * where `opened` is the predicted opened outcome (defaults to expected).
 */
const runSteps = (base, build, steps) => {
  const src = sourceOf(build);
  if (!shows(src.visible(), base)) derivationErrors.push(`base ${base}: source shows ${render(src.visible())}`);
  const { created, opened } = forksOf(src);
  const flagsBefore = { created: flags(created), opened: flags(opened) };
  let prevExpected = parse(base);
  let prevOpened = opened.visible();
  const out = [];
  for (const st of steps) {
    const q = st.request;
    const oracle = localEdit(prevExpected, { kind: q.kind, ...oracleRequest(prevExpected, q) });
    if (!viewsEqual(oracle, parse(st.expected))) derivationErrors.push(`${describe(q)} from ${render(prevExpected)}: localEdit gives ${render(oracle)}, hand value ${st.expected}`);
    const ownOracle = localEdit(prevOpened, { kind: q.kind, ...oracleRequest(prevOpened, q) });
    const oc = issue(created, q);
    const oo = issue(opened, q);
    const predicted = st.opened ?? st.expected;
    const vc = created.visible();
    const vo = opened.visible();
    out.push({
      request: describe(q),
      expected: st.expected,
      predictedOpened: predicted,
      observed: { created: render(vc), opened: render(vo) },
      oracle: { created: shows(vc, st.expected), opened: shows(vo, st.expected) },
      openedLocalMeaning: viewsEqual(vo, ownOracle),
      deletedMarkers: { created: oc.deletedMarkers, opened: oo.deletedMarkers },
      asserted: shows(vc, st.expected) && shows(vo, predicted),
    });
    prevExpected = parse(st.expected);
    prevOpened = vo;
  }
  return { src, created, opened, steps: out, flagsBefore, flagsAfter: { created: flags(created), opened: flags(opened) } };
};

const scenarios = [];
const record = (s) => {
  scenarios.push(s);
  console.log(`${s.pass ? 'PASS' : 'FAIL'} ${s.id}. ${s.title}`);
};
const stepsPass = (steps) => steps.every((s) => s.asserted);

verifySources();

const ABC = (fmts) => [{ kind: 'insert', index: 0, text: 'abc', attrs: {} }, ...fmts];
const del = (index, len = 1) => ({ kind: 'delete', index, len });
const ins = (index, text, attrs) => ({ kind: 'insert', index, text, attrs });
const fmt = (index, len, attrs) => ({ kind: 'format', index, len, attrs });

// a. The shrunk case: a plain character between an italic run and a bold run.
{
  const build = [ins(0, 'i', { bold: true }), ins(0, 'lz', {}), fmt(0, 1, { italic: true })];
  const r = runSteps('l_ z i*', build, [{ request: del(1), expected: 'l_ i*', opened: 'l_ i*_' }]);
  const neg = !shows(r.created.visible(), 'l_ i*_') && !shows(r.opened.visible(), 'l_ i*');
  record({
    id: 'a',
    title: 'shrunk case: delete z between l_ and i*',
    setup: "client 1: insert(0,'i',{bold:true}); insert(0,'lz',{}); format(0,1,{italic:true})",
    base: 'l_ z i*',
    steps: r.steps,
    flagsBefore: r.flagsBefore,
    negative: { claim: "the created replica spreads italic to i, or the opened replica gives the list edit 'l_ i*'", holds: neg },
    pass: stepsPass(r.steps) && neg,
  });
}

// b. Smallest single-user cases: three characters, one or two formats.
{
  const cases = [
    { name: 'last character of a run', base: 'a* b* c', build: ABC([fmt(0, 2, { bold: true })]), step: { request: del(1), expected: 'a* c', opened: 'a* c*' } },
    { name: 'plain character between runs of different keys', base: 'a* b c_', build: ABC([fmt(0, 1, { bold: true }), fmt(2, 1, { italic: true })]), step: { request: del(1), expected: 'a* c_', opened: 'a* c*_' } },
    { name: 'plain character between runs of the same key', base: 'a* b c*', build: ABC([fmt(0, 1, { bold: true }), fmt(2, 1, { bold: true })]), step: { request: del(1), expected: 'a* c*' } },
    { name: 'only character of a run, run begins after a plain character', base: 'a b* c', build: ABC([fmt(1, 1, { bold: true })]), step: { request: del(1), expected: 'a c' } },
    { name: 'two characters, nothing to the right', base: 'a* b', build: [ins(0, 'a', { bold: true }), ins(1, 'b', {})], step: { request: del(1), expected: 'a*' } },
  ];
  const observed = cases.map((c) => {
    const r = runSteps(c.base, c.build, [c.step]);
    return { name: c.name, base: c.base, items: r.src.items().map(({ id, kind, str, key, value }) => (kind === 'string' ? `${str}[${id}]` : `${key}:${value}[${id}]`)).join(' '), ...r.steps[0], flagsBefore: r.flagsBefore };
  });
  // Negative companion: the single-format case must not leave the created
  // replica's closing marker deleted, and must delete it on the opened one.
  const first = observed[0];
  const neg = first.deletedMarkers.created.length === 0
    && isDeepStrictEqual(first.deletedMarkers.opened.map((m) => [m.key, m.value]), [['bold', null]])
    && !shows(parse(first.observed.created), 'a* c*');
  record({
    id: 'b',
    title: 'smallest single-user delete that spreads formatting (three characters)',
    cases: observed,
    negative: { claim: "on 'a* b* c' the created replica deletes a marker or shows 'a* c*', or the opened replica keeps the closing bold:null", holds: neg },
    pass: observed.every((o) => o.asserted) && neg,
  });
}

// c. Insert with attributes omitted at each boundary.
{
  const base = 'a* b c_';
  const build = ABC([fmt(0, 1, { bold: true }), fmt(2, 1, { italic: true })]);
  const cases = [
    { request: ins(0, 'X'), expected: 'X a* b c_' },
    { request: ins(1, 'X'), expected: 'a* X* b c_', opened: 'a* X b c_' },
    { request: ins(2, 'X'), expected: 'a* b X c_' },
    { request: ins(3, 'X'), expected: 'a* b c_ X_', opened: 'a* b c_ X' },
  ];
  const observed = cases.map((c) => runSteps(base, build, [c]).steps[0]);
  const neg = shows(parse(observed[0].observed.opened), 'X a* b c_') && shows(parse(observed[2].observed.opened), 'a* b X c_');
  record({
    id: 'c',
    title: 'insert with attributes omitted at each boundary of a* b c_',
    base,
    cases: observed,
    negative: { claim: 'the opened replica also differs at index 0 and at index 2 (where the attributes in force are empty)', holds: neg },
    pass: observed.every((o) => o.asserted) && neg,
  });
}

// d. format on an opened replica, and what it does to the flags.
{
  const build = ABC([fmt(0, 2, { bold: true })]);
  const r1 = runSteps('a* b* c', build, [
    { request: fmt(1, 1, { italic: true }), expected: 'a* b*_ c' },
    { request: del(1), expected: 'a* c' },
  ]);
  // A format that changes nothing creates no format item, so the flags stay lost.
  const r2 = runSteps('a* b* c', build, [
    { request: { ...fmt(0, 1, { bold: true }), unchanged: true }, expected: 'a* b* c' },
    { request: del(1), expected: 'a* c', opened: 'a* c*' },
  ]);
  const flagsAfterNoop = r2.flagsAfter.opened.hasFormatting;
  const neg = !shows(r1.opened.visible(), 'a* c*') && r1.flagsAfter.opened.searchMarker === null && r1.flagsAfter.opened.hasFormatting === true && flagsAfterNoop === false;
  record({
    id: 'd',
    title: 'format on an opened replica is unaffected and restores the flags when it creates a marker',
    base: 'a* b* c',
    effective: { steps: r1.steps, flagsBefore: r1.flagsBefore.opened, flagsAfter: r1.flagsAfter.opened },
    noOpFormat: { steps: r2.steps, flagsAfter: r2.flagsAfter.opened },
    negative: { claim: "after an effective format the opened replica still spreads bold on delete ('a* c*'), or a format that changes nothing restores the flags", holds: neg },
    pass: stepsPass(r1.steps) && stepsPass(r2.steps) && neg,
  });
}

// e. Several edits on one opened replica.
{
  const build = [ins(0, 'abcdef', {}), fmt(0, 2, { bold: true }), fmt(3, 2, { bold: true })];
  const r = runSteps('a* b* c d* e* f', build, [
    { request: del(1), expected: 'a* c d* e* f', opened: 'a* c* d* e* f' },
    { request: del(3), expected: 'a* c d* f', opened: 'a* c* d* f*' },
    { request: del(1), expected: 'a* d* f', opened: 'a* d* f*' },
  ]);
  const wrongPerStep = r.steps.map((s) => !s.openedLocalMeaning);
  const neg = isDeepStrictEqual(wrongPerStep, [true, true, false]);
  record({
    id: 'e',
    title: 'errors recur and accumulate over a sequence of deletes',
    base: 'a* b* c d* e* f',
    steps: r.steps,
    openedSearchMarkersAfter: r.flagsAfter.opened.searchMarker,
    openedWrongAgainstOwnPreviousView: wrongPerStep,
    negative: { claim: 'only the first edit on the opened replica is wrong (the second delete, at the end of the other run, is correct)', holds: neg },
    pass: stepsPass(r.steps) && neg,
  });
}

// f. Reading the text before the edit.
{
  const src = sourceOf(ABC([fmt(0, 2, { bold: true })]));
  const bytes = Y.encodeStateAsUpdate(src.doc);
  const reads = {
    none: () => {},
    toString: (t) => t.toString(),
    toDelta: (t) => t.toDelta(),
    length: (t) => t.length,
    toJSON: (t) => t.toJSON(),
  };
  const observed = Object.entries(reads).map(([name, read]) => {
    const d = new Y.Doc({ gc: false });
    d.clientID = 2;
    Y.applyUpdate(d, bytes);
    const t = d.getText('t');
    read(t);
    t.delete(1, 1);
    const vis = t.toDelta().flatMap((x) => [...x.insert].map((ch) => ({ ch, attrs: x.attributes ?? {} })));
    return { read: name, observed: render(vis), asserted: shows(vis, 'a* c*') };
  });
  const neg = observed.every((o) => !shows(parse(o.observed), 'a* c'));
  record({
    id: 'f',
    title: 'reading before the edit (raw Y.Doc, opened order) changes nothing',
    base: 'a* b* c',
    request: 'delete [1,2)',
    expected: 'a* c',
    predictedOpened: 'a* c*',
    cases: observed,
    negative: { claim: 'some read before the delete yields the list edit', holds: neg },
    pass: observed.every((o) => o.asserted) && neg,
  });
}

// g. getText before applyUpdate with the same bytes.
{
  const all = scenarios.flatMap((s) => [...(s.steps ?? []), ...(s.cases ?? []), ...(s.effective?.steps ?? []), ...(s.noOpFormat?.steps ?? [])]).filter((s) => s.oracle);
  const createdAll = all.every((s) => s.oracle.created);
  const openedFailures = all.filter((s) => !s.oracle.opened).length;
  const src = sourceOf(ABC([fmt(0, 2, { bold: true })]));
  const viaLoad = new Replica(3, { loaded: true });
  viaLoad.loadFrom(src);
  const viaSync = new Replica(3);
  viaSync.syncFrom(src);
  const sameBytes = isDeepStrictEqual(Y.encodeStateAsUpdate(src.doc), Y.encodeStateAsUpdate(src.doc, Y.encodeStateVector(new Y.Doc())));
  const neg = openedFailures > 0;
  record({
    id: 'g',
    title: 'getText before applyUpdate with the same bytes meets the oracle in every step above',
    stepsChecked: all.length,
    createdMeetsOracle: createdAll,
    openedStepsFailingOracle: openedFailures,
    bytesOfLoadAndSyncIdentical: sameBytes,
    negative: { claim: 'the opened order also meets the oracle everywhere (so the byte source, not the order, would matter)', holds: neg },
    pass: createdAll && sameBytes && neg,
  });
}

// h. Round trip: is the opened replica's result permanent, and do replicas converge?
{
  const build = ABC([fmt(0, 2, { bold: true })]);
  const src = sourceOf(build);
  const { opened } = forksOf(src);
  const op = opened.delete(1, 1);
  const third = new Replica(3);
  const viaState = third.syncFrom(opened);
  const reopened = new Replica(4, { loaded: true });
  reopened.loadFrom(opened);
  const atSource = src.deliver(op);
  const views = { opened: render(opened.visible()), createdReceiver: render(third.visible()), openedReceiver: render(reopened.visible()), source: render(src.visible()) };
  const emitted = { createdReceiver: viaState.emitted.length, source: atSource.emitted.length };
  const converge = Object.values(views).every((v) => v === 'a* c*');
  // Reverse direction: a created replica's correct delete reaches an opened receiver.
  const src2 = sourceOf(build);
  const { created } = forksOf(src2);
  const op2 = created.delete(1, 1);
  const openedReceiver = new Replica(5, { loaded: true });
  openedReceiver.loadFrom(src2);
  openedReceiver.deliver(op2);
  const reverse = { sender: render(created.visible()), openedReceiver: render(openedReceiver.visible()) };
  const reverseOk = reverse.sender === 'a* c' && reverse.openedReceiver === 'a* c';
  const neg = !Object.values(views).some((v) => v === 'a* c') && emitted.createdReceiver === 0 && emitted.source === 0;
  record({
    id: 'h',
    title: 'the spread is part of the update: every receiver converges on it',
    base: 'a* b* c',
    request: 'delete [1,2) on the opened replica',
    expected: 'a* c',
    predicted: { allReplicas: 'a* c*' },
    observed: views,
    deletedMarkersInUpdate: op.deletedMarkers,
    cleanupUpdatesEmitted: emitted,
    reverseDirection: { expected: 'a* c', observed: reverse, pass: reverseOk },
    negative: { claim: "some receiver repairs the state to 'a* c', or emits a cleanup", holds: neg },
    pass: converge && reverseOk && neg,
  });
}

verifySources();

const rootCause = [
  'Where the flags are lost: decoding resolves a root parent name with doc.get(name) (yjs.mjs 1430, 1454), creating a placeholder AbstractType; ContentFormat.integrate (8991-8996) sets _searchMarker = null and _hasFormatting = true on it. getText (628) then reaches Doc.get (577-608), which builds a new YText (constructor 7053-7069: _searchMarker = [], _hasFormatting = false) and copies only _map, _start and _length (588-599). Root-level text only; nested Y.Text and Y.XmlText are decoded with their own constructor and keep the flags.',
  'Which operations read search markers: findPosition (6327) calls findMarker (4849) when asked; insert with attributes omitted (7329), insertEmbed with attributes omitted (7356) and every delete (7379) ask; format does not (7403). findMarker returns null at index 0 or when _searchMarker is null (4850), so created replicas with formatted text never use markers. With a marker, the position starts at marker.p.left with an empty attribute map (6330-6332), missing format items left of marker.p; findMarker leaves marker.p on a format item, or on a string item whose left neighbour is a format item (4859-4883). deleteText (6737) copies these attributes (6739) into cleanupFormattingGap (6564), which deletes a format item whose value equals the start value (6592): a closing marker with value null is deleted and the run spreads right. An omitted-attribute insert copies the empty map and does not inherit. Markers persist across edits (updateMarkerChanges 4931, called at 6465 and 6761).',
  'Which cleanup is skipped: after a remote transaction YText._callObserver requests cleanup only when _hasFormatting is true (7123); the transaction runs cleanupYTextAfterTransaction (3300-3301, 6684), whose per-item gate also checks _hasFormatting (6707). Opened replicas never run it.',
  'Healing: any format item later integrated into the text (local format or attributed insert that creates a marker, or a remote update carrying one) runs ContentFormat.integrate on the real YText and restores both flags.',
];

const out = {
  yjs: verifySources(),
  node: process.version,
  sourcesVerified: true,
  status: 'measured on the pinned version; not proved',
  notation: "characters separated by spaces; suffix '*' bold, '_' italic",
  rootCause,
  affected: {
    delete: 'yes, at index > 0: may delete a closing marker and spread formatting to the right neighbour',
    insertAttributesOmitted: 'yes, at index > 0: may fail to inherit the left neighbour\'s attributes',
    insertEmbedAttributesOmitted: 'same path as insert (7356); not exercised here',
    insertExplicitAttributes: 'no (findPosition without markers)',
    format: 'no (findPosition without markers); a format that creates a marker restores the flags',
    reads: 'no (toString, toDelta, length, toJSON neither read nor repair markers)',
    remoteUpdates: 'applied by id, so not affected; the opened receiver skips the post-transaction cleanup',
  },
  derivationErrors,
  scenarios,
};
mkdirSync(join(here, 'results'), { recursive: true });
writeFileSync(join(here, 'results', 'opened-document.json'), JSON.stringify(out, null, 2) + '\n');
const failed = scenarios.filter((s) => !s.pass);
for (const e of derivationErrors) console.log(`DERIVATION ${e}`);
console.log(`${scenarios.length - failed.length}/${scenarios.length} scenarios pass; wrote results/opened-document.json`);
if (failed.length || derivationErrors.length) process.exitCode = 1;
