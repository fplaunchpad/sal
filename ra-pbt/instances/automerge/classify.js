/**
 * Mechanism classification of check failures in executed schedules.
 *
 * Classes (stable ids). A mark's boundary gap, on either side, is the stretch
 * of the element list between its boundary element and the character its
 * Peritext anchor names (or the end of the text when the anchor is the end):
 * the anchor reading and the boundary reading disagree exactly on whether
 * the mark covers the characters there.
 *   A-001 boundary placed by operation order   Automerge inserts a boundary as
 *         a list element and orders it against an element inserted
 *         concurrently into the same gap by operation id, whatever the
 *         expand policy. For a raLinearizability failure: every attribute
 *         in which the displayed view differs from the nearest admitted view
 *         belongs to a character in the boundary gap of a mark of that name
 *         whose gap holds a character concurrent with the mark (the
 *         character itself, or the one it was later inserted after), or
 *         whose run was inserted after a boundary, inside that gap, of a
 *         mark concurrent with it (two boundaries ordered by id). For a
 *         localMeaning failure: the anchor reading at the insertion point
 *         Automerge chose gives the expected value, so the deviation comes
 *         from where boundaries stand, not from where the character went.
 *   A-002 shared insertion point                 a local insert lands after the
 *         last sticky boundary between its displayed neighbours (a begin
 *         that expands before, an end that does not expand after), taking
 *         every mark name with it; a sticky boundary of one name thereby
 *         carries the character across a boundary of another name. For a
 *         localMeaning failure: for every differing attribute, the
 *         insertion point that considers only boundaries of that name gives
 *         the expected value. For a raLinearizability failure: the differing
 *         character (or the character of its run it was inserted after)
 *         was inserted after a boundary of another name and lies in the
 *         boundary gap of a mark of the differing name.
 *   A-003 emptied mark                           a character inserted causally
 *         after a mark, into its boundary gap, when no character concurrent
 *         with the mark is in that gap and every character the mark covered
 *         when it was issued is deleted: the anchors of the emptied mark
 *         still enclose the insertion point, Automerge's insertion rule
 *         places the character outside the boundary pair.
 *   other                                         none of the above.
 *
 * A localMeaning failure that is neither A-001 nor A-002 and in which the
 * anchor reading at Automerge's insertion point gives the value Automerge
 * shows is classed
 * `view-artefact`: a mark of the name covers the new character's position
 * but loses to a later mark on both displayed neighbours, which the
 * index-level edit cannot see, so the expectation, not Automerge, is wrong.
 *
 * A failure whose differing attributes have different explanations is
 * classed by the joined ids (for instance A-001+A-002).
 *
 * A raLinearizability failure for which the confirmation search finds a
 * witness is classed `layout-artefact`. The end-to-end check and the
 * confirmation search are now the same full search, so the class is kept
 * for records of earlier runs and cannot arise.
 *
 * Method. The schedule is re-executed without checks up to the failing step.
 * The replica's element walk, the records' marks (boundary ids and anchors)
 * and the records' causal pasts give, for each mark, the characters in its
 * boundary gaps and whether their inserts are concurrent with it. For a
 * raLinearizability failure the displayed view is compared with the nearest
 * admitted view (same characters, fewest differing attributes); each
 * failure is also repeated by the confirmation search under an application
 * budget and a state cap, which marks it undecided when either runs out.
 */
import { readFileSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { findWitness, allFinalViews } from '../../src/witness.js';
import { DEFAULT_WITNESS_STATE_LIMIT } from '../../src/checks.js';
import { Execution, eventsAt, execute, instanceFor, finalSyncSteps, CHECKS } from './index.js';
import { normaliseAttrs, insertedAttrs } from './spec.js';
import { walk } from './adapter.js';
import { confirmWitness } from './confirm-witness.js';

export { confirmWitness } from './confirm-witness.js';

export const CLASSES = { 'A-001': 'boundary placed by operation order', 'A-002': 'shared insertion point', 'A-003': 'emptied mark', 'layout-artefact': 'witness found under the visible-character direction', 'view-artefact': 'index-level expectation blind to a covered position', other: 'other' };

/** Compact rendering of a view: characters, with attributes in brackets. */
export function renderView(v) {
  return v
    .map((e) => {
      const a = normaliseAttrs(e.attrs);
      const ks = Object.keys(a).sort();
      return ks.length ? `${e.ch}(${ks.map((k) => (a[k] === true ? k : `${k}=${a[k]}`)).join(',')})` : e.ch;
    })
    .join(' ');
}

/** Element walk on one line: <name@id and >@id for boundaries (+ when sticky-relevant expand is set), x for deleted characters. */
export function renderWalk(list) {
  return list
    .map((e) => {
      if (e.kind === 'char') return `${e.ch}${e.deleted ? 'x' : ''}@${e.id}`;
      if (e.kind === 'begin') return `<${e.name}${e.value === null ? '=null' : e.value === true ? '' : '=' + e.value}${e.expand ? '+' : ''}@${e.id}`;
      return `${e.expand ? '+' : ''}>@${e.id}`;
    })
    .join(' ');
}

const precedes = (a, b) => b.deps.includes(a.key);
const concurrent = (a, b) => a !== b && !precedes(a, b) && !precedes(b, a);

/**
 * Executes the first `upto + 1` steps of a schedule followed by its final
 * synchronisation round (Automerge emits no cleanup changes, so the final
 * sync is one round), without checks.
 */
function replay(schedule, upto, semantics) {
  const ex = new Execution(schedule.replicas, { checks: [], semantics });
  [...schedule.steps, ...finalSyncSteps(schedule.replicas)].slice(0, upto + 1).forEach((s) => ex.apply(s));
  return ex;
}

/** Marks integrated at replica r: { record, mark }. */
function marksAt(ex, r) {
  const out = [];
  for (const o of ex.ops) if (ex.integrated[r].has(o.key)) for (const m of o.marks ?? []) out.push({ record: o, mark: m });
  return out;
}

/** The record that inserted each character id. */
function inserters(ex) {
  const by = new Map();
  for (const o of ex.ops) for (const c of o.chars ?? []) by.set(c.id, o);
  return by;
}

/**
 * Characters in the boundary gaps of mark m in `list`: for each side, the
 * characters strictly between the boundary element and the anchor's
 * character, or between the boundary and the end of the text when the anchor
 * is the end. Returns [{ id, side, coveredBy: 'boundary' | 'anchor' }].
 */
export function boundaryGapChars(list, m) {
  const pos = new Map(list.map((e, i) => [e.id, i]));
  const out = [];
  const scan = (from, to, side, coveredBy) => {
    for (let i = Math.min(from, to) + 1; i < Math.max(from, to); i++) if (list[i].kind === 'char') out.push({ id: list[i].id, side, coveredBy });
  };
  const b = pos.get(m.begin.id);
  const e = pos.get(m.end.id);
  if (m.anchorStart === null) scan(-1, b, 'start', 'anchor');
  else {
    const x = pos.get(m.anchorStart.id);
    if (m.anchorStart.side === 'after') x < b ? scan(x, b, 'start', 'anchor') : scan(b, x + 1, 'start', 'boundary');
    else x > b ? scan(b, x, 'start', 'boundary') : scan(x - 1, b, 'start', 'anchor');
  }
  if (m.anchorEnd === null) scan(e, list.length, 'end', 'anchor');
  else {
    const x = pos.get(m.anchorEnd.id);
    if (m.anchorEnd.side === 'before') x > e ? scan(e, x, 'end', 'anchor') : scan(x - 1, e, 'end', 'boundary');
    else x < e ? scan(x, e, 'end', 'boundary') : scan(e, x + 1, 'end', 'anchor');
  }
  return out;
}

/** Whether list position i lies strictly between mark m's boundary on `side` and the character its anchor names (or the end of the text). */
function withinGap(list, m, side, i) {
  const pos = (id) => list.findIndex((e) => e.id === id);
  const b = pos(side === 'start' ? m.begin.id : m.end.id);
  const a = side === 'start' ? m.anchorStart : m.anchorEnd;
  const x = a === null ? (side === 'start' ? -1 : list.length) : pos(a.id);
  return i > Math.min(b, x) && i < Math.max(b, x);
}

/** Whether the anchors of mark m cover list position i (a character's position). */
function anchorCovers(list, m, i) {
  const pos = (id) => list.findIndex((e) => e.id === id);
  if (m.anchorStart) {
    const p = pos(m.anchorStart.id);
    if (m.anchorStart.side === 'after' ? !(i > p) : !(i >= p)) return false;
  }
  if (m.anchorEnd) {
    const p = pos(m.anchorEnd.id);
    if (m.anchorEnd.side === 'before' ? !(i < p) : !(i <= p)) return false;
  }
  return true;
}

/**
 * Value of `key` under the anchor reading for a character inserted at list
 * position `at` (between at-1 and at): among the marks of that name whose
 * start anchor stands before the point and whose end anchor after it, the
 * one with the greatest id.
 */
function anchorValueAt(list, at, key, marks) {
  const pos = (id) => list.findIndex((e) => e.id === id);
  let best = null;
  for (const { mark } of marks) {
    if (mark.name !== key) continue;
    if (mark.anchorStart && !(pos(mark.anchorStart.id) < at)) continue;
    if (mark.anchorEnd && !(pos(mark.anchorEnd.id) >= at)) continue;
    if (!best || cmp(mark.id, best.id) > 0) best = mark;
  }
  return best?.value ?? null;
}

/** Misplaced characters of every mark at replica r, with concurrency of their inserts and the mark. */
function misplacements(ex, r, list) {
  const ins = inserters(ex);
  const out = [];
  for (const { record, mark } of marksAt(ex, r))
    for (const g of boundaryGapChars(list, mark)) {
      const by = ins.get(g.id);
      out.push({ mark: mark.id, name: mark.name, value: mark.value, char: g.id, side: g.side, coveredBy: g.coveredBy, concurrent: by ? concurrent(by, record) : null, charOp: by?.key, markOp: record.key });
    }
  return out;
}

/** Differences between two views of the same characters: [{ index, ch, key, actual, reference }]. */
function differences(actual, reference) {
  const out = [];
  actual.forEach((e, i) => {
    const a = normaliseAttrs(e.attrs);
    const b = normaliseAttrs(reference[i].attrs);
    for (const k of new Set([...Object.keys(a), ...Object.keys(b)])) if (a[k] !== b[k]) out.push({ index: i, ch: e.ch, key: k, actual: a[k] ?? null, reference: b[k] ?? null });
  });
  return out;
}

/** The admitted view with the same characters and fewest differing attributes, or null. */
function nearest(actual, admitted) {
  let best = null;
  for (const v of admitted) {
    if (v.length !== actual.length || v.some((e, i) => e.ch !== actual[i].ch)) continue;
    const d = differences(actual, v).length;
    if (!best || d < best.d) best = { v, d };
  }
  return best?.v ?? null;
}

/** raLinearizability failure at replica r after step `step`. */
function classifyRA(schedule, r, step, semantics) {
  const ex = replay(schedule, step, semantics);
  const rep = ex.replica(r);
  const list = walk(rep.doc);
  const target = rep.visibleWithIds();
  const { events } = eventsAt(ex, r);
  const charsOnly = confirmWitness(semantics, events, target);
  const markerSearch = findWitness(instanceFor('marker', 'layout').spec, events.map((e) => ({ ...e, specOps: ex.byKey.get(e.key).specOpsBySemantics.marker })), Object.assign(target.map((c) => ({ ...c })), { layout: target.boundaries }), { limit: DEFAULT_WITNESS_STATE_LIMIT });
  const markerWitness = markerSearch.truncated ? 'undecided' : markerSearch.found;
  if (charsOnly === true) return { check: 'raLinearizability', replica: r, step, class: 'layout-artefact', witnessCharsOnly: true };
  const admitted = allFinalViews(instanceFor(semantics, 'layout').spec, events, { target, limit: DEFAULT_WITNESS_STATE_LIMIT });
  const reference = nearest(target, admitted);
  const mis = misplacements(ex, r, list);
  const out = { check: 'raLinearizability', replica: r, step, witnessCharsOnly: charsOnly, witnessMarker: markerWitness, walk: renderWalk(list), misplaced: mis };
  if (!reference) return { ...out, class: 'other', pattern: 'character order outside the admitted orders' };
  const diffs = differences(target, reference);
  const ins = inserters(ex);
  const originOf = new Map(ex.ops.flatMap((o) => (o.chars ?? []).map((c) => [c.id, c.origin])));
  const byId = new Map(list.map((e) => [e.id, e]));
  const nameOf = new Map(list.filter((e) => e.kind === 'begin').map((e) => [e.id, e.name]));
  const boundaryName = (e) => (e.kind === 'begin' ? e.name : nameOf.get(`${Number(e.id.split('@')[0]) - 1}@${e.id.split('@')[1]}`));
  const emptied = (mark, record) =>
    ex.ops.filter((o) => record.deps.includes(o.key)).flatMap((o) => o.chars ?? []).every((c) => {
      const e = list.find((x) => x.id === c.id);
      return !e || e.deleted || !anchorCovers(list, mark, list.indexOf(e));
    });
  const explained = diffs.map((d) => {
    const id = target[d.index].id;
    const gaps = mis.filter((x) => x.char === id && x.name === d.key);
    for (const g of gaps) {
      const rootCause = mis.find((x) => x.mark === g.mark && x.side === g.side && x.concurrent);
      if (rootCause) return { ...d, id, by: 'A-001', mark: g.mark, side: g.side, coveredBy: g.coveredBy, concurrentChar: rootCause.char, charOp: rootCause.charOp, markOp: g.markOp };
    }
    for (const g of gaps) {
      const inGap = new Set(mis.filter((x) => x.mark === g.mark && x.side === g.side).map((x) => x.char));
      let root = id;
      for (let o = originOf.get(root); o && inGap.has(o); o = originOf.get(root)) root = o;
      const ref = byId.get(originOf.get(root));
      const refMark = ref && ref.kind !== 'char' ? marksAt(ex, r).find((x) => x.mark.begin.id === ref.id || x.mark.end.id === ref.id) : null;
      const gm = marksAt(ex, r).find((x) => x.mark.id === g.mark);
      if (refMark && concurrent(refMark.record, gm.record) && withinGap(list, gm.mark, g.side, list.indexOf(ref)))
        return { ...d, id, by: 'A-001', mark: g.mark, side: g.side, coveredBy: g.coveredBy, insertedAfter: ref.id, concurrentBoundaryOf: refMark.mark.id, charOp: ins.get(root)?.key, markOp: g.markOp };
      if (ref && ref.kind !== 'char' && boundaryName(ref) !== d.key)
        return { ...d, id, by: 'A-002', mark: g.mark, side: g.side, coveredBy: g.coveredBy, insertedAfter: ref.id, charOp: ins.get(root)?.key, markOp: g.markOp };
    }
    for (const g of gaps) {
      const { record, mark } = marksAt(ex, r).find((x) => x.mark.id === g.mark);
      if (!g.concurrent && emptied(mark, record)) return { ...d, id, by: 'A-003', mark: g.mark, side: g.side, coveredBy: g.coveredBy, charOp: ins.get(id)?.key, markOp: g.markOp };
    }
    return { ...d, id, by: null };
  });
  const kinds = [...new Set(explained.map((d) => d.by))];
  const cls = diffs.length > 0 && !kinds.includes(null) ? kinds.sort().join('+') : 'other';
  return { ...out, class: cls, reference: renderView(reference), differences: explained };
}

/** Value of `key` at list position `at` (an insertion point: between at-1 and at) under Automerge's rule. */
function valueAt(list, at, key) {
  let best = null;
  const active = new Map();
  for (let i = 0; i < at; i++) {
    const e = list[i];
    if (e.kind === 'begin') active.set(e.id, e);
    else if (e.kind === 'end') {
      const [c, a] = e.id.split('@');
      active.delete(`${Number(c) - 1}@${a}`);
    }
  }
  for (const m of active.values()) if (m.name === key && (!best || cmp(m.id, best.id) > 0)) best = m;
  return best?.value ?? null;
}

function cmp(a, b) {
  const [ca, xa] = a.split('@');
  const [cb, xb] = b.split('@');
  if (Number(ca) !== Number(cb)) return Number(ca) - Number(cb);
  return xa < xb ? -1 : xa > xb ? 1 : 0;
}

/**
 * The insertion point Automerge's sticky scan chooses in the run after list
 * position `from` up to the next visible character, considering only the
 * boundaries `relevant` accepts: after the last sticky boundary (a begin
 * expanding before, an end not expanding after) whose pair is not complete
 * inside the run, else immediately after `from`.
 */
function stickyPoint(list, from, relevant) {
  const found = [];
  for (let i = from + 1; i < list.length; i++) {
    const e = list[i];
    if (e.kind === 'char' && !e.deleted) break;
    if (e.kind === 'char' || !relevant(e, list)) continue;
    if (e.kind === 'end') {
      const [c, a] = e.id.split('@');
      const j = found.findIndex((f) => f.id === `${Number(c) - 1}@${a}`);
      if (j !== -1) {
        found.length = j;
        continue;
      }
    }
    if ((e.kind === 'begin' && e.expand) || (e.kind === 'end' && !e.expand)) found.push({ id: e.id, at: i + 1 });
  }
  return found.length ? found[found.length - 1].at : from + 1;
}

/** localMeaning failure of an insert at replica r issued at step `step`. */
function classifyLocal(schedule, r, step, failure) {
  const ex = replay(schedule, step - 1, 'marker');
  const rep = ex.replica(r);
  const before = walk(rep.doc);
  const vis = before.map((e, i) => ({ e, i })).filter((x) => x.e.kind === 'char' && !x.e.deleted);
  const req = failure.request;
  const from = req.index === 0 ? -1 : vis[req.index - 1].i;
  const nameOf = new Map(before.filter((e) => e.kind === 'begin').map((e) => [e.id, e.name]));
  const boundaryName = (e) => (e.kind === 'begin' ? e.name : nameOf.get(`${Number(e.id.split('@')[0]) - 1}@${e.id.split('@')[1]}`));
  const actualAt = stickyPoint(before, from, () => true);
  const diffs = differences(failure.actual, failure.expected).filter((d) => d.index >= req.index && d.index < req.index + req.text.length);
  const marks = marksAt(ex, r);
  const explained = diffs.map((d) => {
    if (anchorValueAt(before, actualAt, d.key, marks) === (d.reference ?? null)) {
      return { ...d, by: 'A-001', point: actualAt };
    }
    const ownAt = stickyPoint(before, from, (e) => boundaryName(e) === d.key);
    if (ownAt !== actualAt && valueAt(before, ownAt, d.key) === (d.reference ?? null)) return { ...d, by: 'A-002', actualPoint: actualAt, ownPoint: ownAt };
    if (anchorValueAt(before, actualAt, d.key, marks) === (d.actual ?? null)) return { ...d, by: 'view-artefact', point: actualAt };
    return { ...d, by: null };
  });
  const classes = [...new Set(explained.map((d) => d.by))];
  const cls = diffs.length && !classes.includes(null) ? classes.sort().join('+') : 'other';
  return { check: 'localMeaning', replica: r, step, class: cls, walk: renderWalk(before), differences: explained, expectedView: renderView(failure.expected), actualView: renderView(failure.actual) };
}

/** Classifies one failure record of a trace of `schedule` under a mark semantics. */
export function classifyFailure(schedule, f, semantics = 'anchor') {
  if (f.check === 'raLinearizability') return classifyRA(schedule, f.replica, f.step, semantics);
  if (f.check === 'localMeaning' && f.request?.kind === 'insert') return classifyLocal(schedule, f.replica, f.step, f);
  return { check: f.check, replica: f.replica, step: f.step, class: 'other' };
}

/** Classifies every failure of a trace; returns the records in check order. */
export function classifyTrace(schedule, checks, semantics = 'anchor') {
  return CHECKS.flatMap((c) => checks[c]?.details.failures ?? []).map((f) => classifyFailure(schedule, f, semantics));
}

/** The class of the earliest failure at replica r of a schedule, or null when nothing fails there. */
export function classifyAt(schedule, r, semantics = 'anchor') {
  const trace = execute(schedule, { semantics });
  const fs = CHECKS.flatMap((c) => trace.checks[c]?.details.failures ?? []).filter((f) => f.replica === r).sort((a, b) => a.step - b.step);
  return fs.length ? classifyFailure(schedule, fs[0], semantics) : { class: null };
}

/** Classifies a search output { summary, failing }: per trial, the classes and the onset class. */
export function classifySearch(data, semantics = data.summary?.options?.semantics ?? 'anchor') {
  return data.failing.map((t) => {
    const fs = CHECKS.flatMap((c) => t.checks[c]?.details.failures ?? []);
    const records = fs.map((f) => classifyFailure(t.schedule, f, semantics));
    const first = records.map((x, i) => ({ x, step: fs[i].step })).sort((a, b) => a.step - b.step)[0];
    return { trial: t.trial, seed: t.seed, campaignSeed: t.campaignSeed, classes: [...new Set(records.map((x) => x.class))].sort(), onset: first?.x.class, records };
  });
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  const [input, output, semantics] = process.argv.slice(2);
  const data = JSON.parse(readFileSync(input, 'utf8'));
  const out = classifySearch(data, semantics);
  const hist = {};
  for (const t of out) for (const c of t.classes) hist[c] = (hist[c] ?? 0) + 1;
  console.log(JSON.stringify(hist));
  if (output) writeFileSync(output, JSON.stringify(out, null, 1) + '\n');
}
