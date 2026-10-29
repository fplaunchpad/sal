/**
 * Mechanism classification of check failures in executed Loro schedules.
 *
 * Classes (stable ids):
 *   L-001 boundary inheritance   raLinearizability: a character inserted
 *                                concurrently with a mark or unmark of key k
 *                                lies just outside the mark's identity
 *                                interval (every displayed character between
 *                                it and the interval is unknown to the mark's
 *                                issuer) and shows the mark's value of k. The
 *                                record says on which side, and whether the
 *                                key's expand type (reversed for an unmark)
 *                                extends the mark to that side
 *                                (`expandConsistent`)
 *   L-002 style from no neighbour  localMeaning on insert: the new text
 *                                carries a key that neither displayed
 *                                neighbour carries
 *   L-003 expand ignored toward  localMeaning on insert: the new text
 *         a neighbour            carries a neighbour's key that the expand
 *                                type does not extend to that side
 *   L-004 adjacent spans         localMeaning on insert: both displayed
 *                                neighbours carry the same value of a key and
 *                                the new text does not
 *   L-005 expand overridden      localMeaning on insert: the expand type of
 *                                a key extends a neighbour's value to the new
 *                                text, and the new text does not carry it
 *   plain-order                  raLinearizability on a version without
 *                                styles (a result about the insertion rule)
 *   other                        none of the above; the record carries the
 *                                differences found
 *
 * A raLinearizability difference on a character whose insert request failed
 * localMeaning on the same key takes that failure's class (`via:
 * 'localMeaning'`): under the inherit reading the specification recomputes
 * the attributes the request was given, so the local failure reappears as a
 * view without a witness.
 *
 * Method. A failure record already holds what is needed: for
 * raLinearizability, the replica's view with identities and the admitted
 * views with the same character order (the directed search); for
 * localMeaning, the request, the view before it, the expected and the
 * actual view. The trial's records give each character's insert record and
 * each mark's interval, key, value and causal past. Deleted characters are
 * located in full orders (tombstones included) consistent with the gap rule
 * and the displayed character order: the witness search with attributes
 * ignored gives a linear extension, folded with every placement directed by
 * the display (at most 64 orders); an explanation holding in one of them is
 * accepted. The nearest admitted
 * view is the one with the fewest differing (character, key) pairs; each
 * difference is explained separately, and a failure takes the class of its
 * first unexplained difference, or L-001 when all are explained.
 */
import { EXPAND, unmarkExpand, idKey, normaliseAttrs, interpret, initial, applyPlaced, placementOf, textSpec } from './spec.js';
import { findWitness } from '../../src/witness.js';

export const CLASSES = {
  'L-001': 'boundary inheritance under concurrency',
  'L-002': 'style from no displayed neighbour',
  'L-003': 'expand ignored toward a neighbour',
  'L-004': 'adjacent spans of one value',
  'L-005': 'expand of a key overridden',
  'plain-order': 'insertion order outside the rule (plain text)',
  other: 'other',
};

const expandsAfter = (e) => e === 'after' || e === 'both';
const expandsBefore = (e) => e === 'before' || e === 'both';
const val = (attrs, k) => normaliseAttrs(attrs)[k];
const same = (a, b) => JSON.stringify(a ?? null) === JSON.stringify(b ?? null);

/** Differing (index, key, actual, expected) pairs of two views of equal length. */
function differences(actual, expected) {
  const out = [];
  for (let i = 0; i < actual.length; i++) {
    const a = normaliseAttrs(actual[i].attrs);
    const e = normaliseAttrs(expected[i].attrs);
    for (const k of new Set([...Object.keys(a), ...Object.keys(e)])) if (!same(a[k], e[k])) out.push({ index: i, key: k, actual: a[k] ?? null, expected: e[k] ?? null });
  }
  return out;
}

/** The trial's records indexed for classification. */
function indexOps(ops) {
  const insertOf = new Map();
  const marks = [];
  for (const o of ops) {
    if (o.kind === 'insert') for (const c of o.chars) insertOf.set(idKey(c.id), o);
    if ((o.kind === 'mark' || o.kind === 'unmark') && o.range) marks.push(o);
  }
  return { insertOf, marks, byKey: new Map(ops.map((o) => [o.key, o])) };
}

const ORDER_SPEC = { ...textSpec('gap'), viewKey: (v) => JSON.stringify(v.map((e) => e.ch)) };

/**
 * Full character orders (deleted characters included) at the version
 * `opKeys`, each consistent with the gap rule and the displayed order
 * `actual`, as { pos: Map from id key to index, state }: at most `limit` of
 * them, along one linear extension the witness search finds with attributes
 * ignored. Empty when none exists.
 */
function fullOrders(idx, opKeys, actual, limit = 64) {
  const keys = new Set(opKeys);
  const events = opKeys.map((k) => idx.byKey.get(k)).filter(Boolean).map((o) => ({ key: o.key, deps: o.deps.filter((d) => keys.has(d)), specOps: interpret(o) }));
  const w = findWitness(ORDER_SPEC, events, actual);
  if (!w.found) return [];
  const placed = placementOf(actual);
  const ops = w.order.flatMap((k) => events.find((e) => e.key === k).specOps);
  const out = [];
  const descend = (st, i) => {
    if (out.length >= limit) return;
    if (i === ops.length) {
      out.push({ pos: new Map(st.map((c, j) => [idKey(c.id), j])), state: st });
      return;
    }
    for (const next of applyPlaced(st, ops[i], placed)) descend(next, i + 1);
  };
  descend(initial(), 0);
  return out;
}

/** Whether record a is in the causal past of record b (deps are the integrated records at issue, so closed). */
const before = (a, b) => b.deps.includes(a.key);
const concurrentOps = (a, b) => a.key !== b.key && !before(a, b) && !before(b, a);

/**
 * Explains a raLinearizability difference at displayed position `index` by a
 * concurrent mark whose interval the character lies just outside of, in one
 * of the full orders `orders`. A displayed character between the two blocks the
 * explanation when the mark's issuer saw it and it was not deleted in the
 * mark's past; deleted characters do not block, since where they sit
 * between displayed ones is not observable and the full order is only one of
 * those the gap rule allows.
 */
function explainBoundary(diff, actual, idx, orders) {
  for (const order of orders) {
    const e = explainIn(diff, actual, idx, order);
    if (e) return e;
  }
  return null;
}

function explainIn(diff, actual, idx, order) {
  const ch = actual[diff.index];
  if (!ch?.id) return null;
  const ins = idx.insertOf.get(idKey(ch.id));
  if (!ins) return null;
  const at = order.pos.get(idKey(ch.id));
  for (const m of idx.marks) {
    if (m.styleKey !== diff.key || !concurrentOps(m, ins)) continue;
    const shownValue = m.kind === 'unmark' ? null : m.value;
    if (!same(shownValue, diff.actual)) continue;
    const l = order.pos.get(idKey(m.range.left));
    const r = order.pos.get(idKey(m.range.right));
    if (l === undefined || r === undefined || (at >= l && at <= r)) continue;
    const [from, to, side] = at < l ? [at + 1, l, 'start'] : [r + 1, at, 'end'];
    const deletedInPast = new Set(m.deps.map((k) => idx.byKey.get(k)).filter((o) => o?.kind === 'delete').flatMap((o) => o.deleted.map(idKey)));
    const shown = new Set(actual.map((e) => idKey(e.id)));
    let adjacent = true;
    for (let i = from; i < to; i++) {
      const c = order.state[i];
      if (!shown.has(idKey(c.id))) continue;
      const o = idx.insertOf.get(idKey(c.id));
      if (!o || (before(o, m) && !deletedInPast.has(idKey(c.id)))) adjacent = false;
    }
    if (!adjacent) continue;
    const expand = m.kind === 'unmark' ? unmarkExpand(EXPAND[m.styleKey] ?? 'none') : EXPAND[m.styleKey] ?? 'none';
    const consistent = side === 'end' ? expandsAfter(expand) : expandsBefore(expand);
    return { mark: m, insert: ins, side, expand, consistent, endpointsVisible: actual.some((e) => idKey(e.id) === idKey(m.range.left)) && actual.some((e) => idKey(e.id) === idKey(m.range.right)) };
  }
  return null;
}

/** Classifies one raLinearizability failure record; `lmByStep` maps a step to its classified localMeaning failure. */
function classifyRaLin(f, idx, lmByStep = new Map()) {
  const kinds = new Set(f.opKeys.map((k) => idx.byKey.get(k)?.kind));
  if (!kinds.has('mark') && !kinds.has('unmark')) return { class: 'plain-order' };
  const admitted = f.expected?.admittedViews ?? [];
  const actual = f.actual;
  const candidates = admitted.filter((w) => w.length === actual.length && w.every((e, i) => e.ch === actual[i].ch));
  if (candidates.length === 0) return { class: 'other', pattern: 'no admitted view with the displayed character order' };
  let best = null;
  for (const w of candidates) {
    const d = differences(actual, w);
    if (!best || d.length < best.d.length) best = { w, d };
  }
  const explained = [];
  const orders = fullOrders(idx, f.opKeys, actual);
  let inherited = null;
  for (const d of best.d) {
    const e = explainBoundary(d, actual, idx, orders);
    if (!e) {
      const ins = actual[d.index]?.id && idx.insertOf.get(idKey(actual[d.index].id));
      const lm = ins && lmByStep.get(ins.step);
      if (lm && lm.key === d.key) {
        inherited ??= { class: lm.class, via: 'localMeaning', localMeaningStep: ins.step, char: actual[d.index].ch, key: d.key };
        continue;
      }
      return { class: 'other', reference: best.w, differences: best.d, unexplained: d };
    }
    explained.push({ char: actual[d.index].ch, key: d.key, actual: d.actual, expected: d.expected, side: e.side, markKind: e.mark.kind, markRecord: e.mark.key, insertRecord: e.insert.key, expand: e.expand, expandConsistent: e.consistent, endpointsVisible: e.endpointsVisible });
  }
  if (inherited) return { ...inherited, reference: best.w, differences: explained };
  return { class: 'L-001', reference: best.w, differences: explained, expandConsistent: explained.every((x) => x.expandConsistent) };
}

/** Classifies one localMeaning failure record on an insert. */
function classifyInsert(f) {
  const { index, text } = f.request;
  const left = f.before[index - 1] ?? null;
  const right = f.before[index] ?? null;
  const diffs = [];
  for (let i = index; i < index + text.length; i++) diffs.push(...differences([f.actual[i]], [f.expected[i]]));
  for (const d of diffs) {
    const lv = left ? val(left.attrs, d.key) : undefined;
    const rv = right ? val(right.attrs, d.key) : undefined;
    const e = EXPAND[d.key] ?? 'none';
    const detail = { key: d.key, actual: d.actual, expected: d.expected, left: lv ?? null, right: rv ?? null, expand: e };
    if (d.actual !== null && d.expected === null) {
      if (!same(lv, d.actual) && !same(rv, d.actual)) return { class: 'L-002', ...detail };
      return { class: 'L-003', ...detail };
    }
    if (d.actual === null && d.expected !== null) {
      if (lv !== undefined && same(lv, rv)) return { class: 'L-004', ...detail };
      return { class: 'L-005', ...detail };
    }
    return { class: 'other', ...detail };
  }
  return { class: 'other', pattern: 'no attribute difference on the inserted text' };
}

/** Classifies one failure record of a trial with records `ops`. */
export function classifyFailure(f, ops, lmByStep) {
  const idx = indexOps(ops);
  if (f.check === 'raLinearizability') return { check: f.check, replica: f.replica, step: f.step, ...classifyRaLin(f, idx, lmByStep) };
  if (f.check === 'localMeaning' && f.request?.kind === 'insert') return { check: f.check, replica: f.replica, step: f.step, ...classifyInsert(f) };
  return { check: f.check, replica: f.replica, step: f.step, class: 'other' };
}

/** Classifies every failure of a trial; `onset` is the class of the earliest failing step. */
export function classifyTrial(checks, ops) {
  const lmByStep = new Map();
  for (const f of checks.localMeaning?.details.failures ?? []) lmByStep.set(f.step, classifyFailure({ check: 'localMeaning', ...f }, ops));
  const records = [];
  for (const c of Object.values(checks)) for (const f of c.details.failures) records.push(c.name === 'localMeaning' ? lmByStep.get(f.step) : classifyFailure({ check: c.name, ...f }, ops, lmByStep));
  records.sort((a, b) => (a.step ?? 0) - (b.step ?? 0));
  return { onset: records[0]?.class ?? null, classes: [...new Set(records.map((r) => r.class))].sort(), records };
}
