/**
 * Sequential specification of styled text with character identities, for
 * Loro's text type.
 *
 * A state is an immutable ordered array of characters
 *   { id: [peer, counter], ch, deleted: boolean, attrs: { key: value } }.
 * Every operation returns a fresh array (or null when its precondition fails),
 * so states can be memoised and compared through `serialise`.
 *
 * Styles are marks on characters. A mark over the identity interval from
 * `left` to `right` sets its key on every character between them, deleted or
 * not, when it is applied, so it also covers characters inserted concurrently
 * between them; an unmark is a mark with value null and clears its key.
 *
 * Three readings of how the expand configuration acts:
 *   'carry'   an insertion carries the attributes it was issued with, which
 *             are what the expand configuration dictates on the issuing
 *             replica's view (`expandAttrs`, checked by `localEdit`); a mark
 *             covers its identity interval;
 *   'inherit' an insertion takes, when it is applied, what the expand
 *             configuration dictates from its visible neighbours in the
 *             specification state at that point; a mark covers its identity
 *             interval;
 *   'expand'  insertions as under 'carry'; a mark also covers, on each side
 *             its expand type extends to, the gap between its interval and
 *             the visible neighbour its issuer saw there (`outerLeft`,
 *             `outerRight`), so it reaches characters inserted concurrently
 *             at an expanding boundary, as Peritext prescribes. An unmark
 *             extends by the reversed expand type (`unmarkExpand`), as Loro
 *             configures it;
 *   'anchors' insertions as under 'carry'; a mark covers its identity
 *             interval and, on each side, any contiguous part of the gap
 *             between the interval and the issuer's outer neighbour there
 *             that adjoins the interval, whatever the expand type: its
 *             anchors land anywhere in their gaps, as a list insertion does
 *             under the gap rule. Relational.
 * The readings agree on every history without a character inserted
 * concurrently next to a mark's boundary.
 *
 * This module is self-contained: it imports nothing. `textSpec(rule, opts)`
 * packages the functions as an ra-pbt specification.
 */

/** The expand behaviour of each style key used by the instance. */
export const EXPAND = Object.freeze({ bold: 'after', link: 'none', sup: 'before', hl: 'both' });

/** Canonical string key of an id `[peer, counter]`. */
export function idKey(id) {
  return id[0] + ':' + id[1];
}

/** Structural equality of ids. */
export function idEq(a, b) {
  return a[0] === b[0] && a[1] === b[1];
}

/** Attributes with null-valued keys dropped and keys in sorted order. */
export function normaliseAttrs(attrs) {
  const out = {};
  for (const k of Object.keys(attrs ?? {}).sort()) {
    if (attrs[k] !== null && attrs[k] !== undefined) out[k] = attrs[k];
  }
  return out;
}

/** `base` with `key` set to `value`, or removed when `value` is null. */
export function setAttr(base, key, value) {
  const out = { ...base };
  if (value === null || value === undefined) delete out[key];
  else out[key] = value;
  return normaliseAttrs(out);
}

const sameValue = (a, b) => JSON.stringify(a) === JSON.stringify(b);

/** The expand type an unmark of a key with expand type `e` extends by: before and after stay, both and none swap. */
export function unmarkExpand(e) {
  return e === 'both' ? 'none' : e === 'none' ? 'both' : e;
}
const expandsAfter = (e) => e === 'after' || e === 'both';
const expandsBefore = (e) => e === 'before' || e === 'both';

/**
 * The attributes the expand configuration gives text inserted between the
 * view entries `left` and `right` (either may be null, at the ends). For
 * each key: the common value when both neighbours carry the same one; else
 * the left neighbour's value when the key expands after; else the right
 * neighbour's value when it expands before; else none. A key absent from
 * `expand` expands nowhere.
 */
export function expandAttrs(left, right, expand = EXPAND) {
  const la = left ? normaliseAttrs(left.attrs) : {};
  const ra = right ? normaliseAttrs(right.attrs) : {};
  const out = {};
  for (const k of [...new Set([...Object.keys(la), ...Object.keys(ra)])].sort()) {
    const e = expand[k] ?? 'none';
    if (k in la && k in ra && sameValue(la[k], ra[k])) out[k] = la[k];
    else if (k in la && expandsAfter(e)) out[k] = la[k];
    else if (k in ra && expandsBefore(e)) out[k] = ra[k];
  }
  return out;
}

/** The empty document. */
export function initial() {
  return [];
}

function indexOfId(state, id) {
  for (let i = 0; i < state.length; i++) if (idEq(state[i].id, id)) return i;
  return -1;
}

/** Canonical string of a state. */
export function serialise(state) {
  return JSON.stringify(state.map((c) => [idKey(c.id), c.ch, c.deleted, Object.entries(normaliseAttrs(c.attrs))]));
}

/** The bounds [lo, hi] of the insertion gap of `op` in `state`, or null when an origin is missing or out of order. */
function gapOf(state, op) {
  let lo = 0;
  if (op.origin !== null && op.origin !== undefined) {
    const o = indexOfId(state, op.origin);
    if (o === -1) return null;
    lo = o + 1;
  }
  let hi = state.length;
  if (op.rightOrigin !== null && op.rightOrigin !== undefined) {
    const r = indexOfId(state, op.rightOrigin);
    if (r === -1 || r < lo) return null;
    hi = r;
  }
  return [lo, hi];
}

/** The visible neighbours of position `at` (an insertion point) in `state`. */
function visibleNeighbours(state, at) {
  let l = at - 1;
  while (l >= 0 && state[l].deleted) l--;
  let r = at;
  while (r < state.length && state[r].deleted) r++;
  return [l >= 0 ? state[l] : null, r < state.length ? state[r] : null];
}

/** The character `op` inserts at position `at` of `state` under an attribute reading. */
function charAt(state, at, op, attrsMode, expand) {
  const attrs = attrsMode === 'inherit' ? expandAttrs(...visibleNeighbours(state, at), expand) : normaliseAttrs(op.attrs);
  return { id: op.id, ch: op.ch, deleted: false, attrs };
}
const placeAt = (state, at, c) => [...state.slice(0, at), c, ...state.slice(at)];

/**
 * Apply one specification operation.
 *   insert { id, ch, origin, rightOrigin, attrs }: under the one-sided rule
 *     (`rule = 'left'`), place immediately after `origin` (head when null),
 *     ignoring `rightOrigin` as RGA does; under the two-sided rule
 *     (`rule = 'both'`), immediately before `rightOrigin` when it is given,
 *     otherwise immediately after `origin`, requiring `origin` to stand
 *     before `rightOrigin`. The gap rule,
 *     which admits every position strictly between them, is relational and
 *     lives in `applyAll`.
 *   delete { ids }: mark each character deleted; a character already deleted
 *     stays deleted, so concurrent deletes of one character commute.
 *   mark { left, right, outerLeft, outerRight, key, value }: set `key` to
 *     `value` (remove it when `value` is null) on every character from
 *     `left` to `right` inclusive, deleted or not; under the 'expand'
 *     reading the range extends to `outerLeft` and `outerRight` (exclusive)
 *     on the sides the key's expand type extends to.
 * `attrsMode` ('carry', 'inherit', 'expand' or 'anchors') chooses the
 * reading; under 'anchors' `apply` gives a mark its identity interval and
 * `applyAll` every extension. Returns the new state, or null when a
 * precondition fails.
 */
export function apply(state, op, rule = 'both', { attrsMode = 'carry', expand = EXPAND } = {}) {
  switch (op.kind) {
    case 'insert': {
      if (indexOfId(state, op.id) !== -1) return null;
      const g = rule === 'left' ? gapOf(state, { origin: op.origin, rightOrigin: null }) : gapOf(state, op);
      if (g === null) return null;
      const at = rule === 'both' && op.rightOrigin !== null && op.rightOrigin !== undefined ? g[1] : g[0];
      return placeAt(state, at, charAt(state, at, op, attrsMode, expand));
    }
    case 'delete': {
      const positions = new Set();
      for (const id of op.ids) {
        const i = indexOfId(state, id);
        if (i === -1) return null;
        positions.add(i);
      }
      return state.map((c, i) => (positions.has(i) ? { ...c, deleted: true } : c));
    }
    case 'mark': {
      let l = indexOfId(state, op.left);
      let r = indexOfId(state, op.right);
      if (l === -1 || r === -1 || l > r) return null;
      if (attrsMode === 'expand') {
        const e = op.value === null ? unmarkExpand(expand[op.key] ?? 'none') : expand[op.key] ?? 'none';
        if (expandsBefore(e)) {
          const o = op.outerLeft === null || op.outerLeft === undefined ? -1 : indexOfId(state, op.outerLeft);
          if (o === -1 && op.outerLeft) return null;
          if (o > l) return null;
          l = o + 1;
        }
        if (expandsAfter(e)) {
          const o = op.outerRight === null || op.outerRight === undefined ? state.length : indexOfId(state, op.outerRight);
          if (o === -1 || o < r) return null;
          r = o - 1;
        }
      }
      return state.map((c, i) => (i >= l && i <= r ? { ...c, attrs: setAttr(c.attrs, op.key, op.value) } : c));
    }
    default:
      throw new Error('unknown operation kind: ' + op.kind);
  }
}

/**
 * Every state an operation may lead to. Under the gap rule an insertion may
 * land at any position strictly after `origin` (or at the head) and strictly
 * before `rightOrigin` (or at the end): the strong list specification. Under
 * the deterministic rules the result is a singleton. An empty list is a
 * precondition failure.
 */
export function applyAll(state, op, rule = 'gap', opts = {}) {
  if (op.kind === 'mark' && opts.attrsMode === 'anchors') return markCuts(state, op);
  if (rule !== 'gap' || op.kind !== 'insert') {
    const next = apply(state, op, rule === 'gap' ? 'both' : rule, opts);
    return next === null ? [] : [next];
  }
  if (indexOfId(state, op.id) !== -1) return [];
  const g = gapOf(state, op);
  if (g === null) return [];
  return placementsIn(state, op, g[0], g[1], opts);
}

/**
 * Every state a mark may lead to under the 'anchors' reading: the interval
 * from `left` to `right`, extended on the left to any position after
 * `outerLeft` (or the head) and on the right to any position before
 * `outerRight` (or the end).
 */
function markCuts(state, op) {
  const l = indexOfId(state, op.left);
  const r = indexOfId(state, op.right);
  if (l === -1 || r === -1 || l > r) return [];
  const ol = op.outerLeft === null || op.outerLeft === undefined ? -1 : indexOfId(state, op.outerLeft);
  const or = op.outerRight === null || op.outerRight === undefined ? state.length : indexOfId(state, op.outerRight);
  if ((ol === -1 && op.outerLeft) || or === -1 || ol > l || or < r) return [];
  const out = [];
  for (let from = ol + 1; from <= l; from++)
    for (let to = r; to < or; to++) out.push(state.map((c, i) => (i >= from && i <= to ? { ...c, attrs: setAttr(c.attrs, op.key, op.value) } : c)));
  return out;
}

function placementsIn(state, op, lo, hi, { attrsMode = 'carry', expand = EXPAND } = {}) {
  const out = [];
  for (let at = lo; at <= hi; at++) out.push(placeAt(state, at, charAt(state, at, op, attrsMode, expand)));
  return out;
}

/**
 * The gap rule directed by a target: `placed` maps the key of every id in
 * the target view to its position there. Returns every state in which the
 * inserted character sits inside its gap and in the order the target gives
 * it relative to the target's characters; a character absent from the target
 * (deleted later) may sit anywhere in its gap. Characters never move once
 * placed, so a witness under the gap rule exists exactly when one exists
 * among these placements.
 */
export function applyPlaced(state, op, placed, opts = {}) {
  if (op.kind !== 'insert') return applyAll(state, op, 'gap', opts);
  if (indexOfId(state, op.id) !== -1) return [];
  const g = gapOf(state, op);
  if (g === null) return [];
  let [lo, hi] = g;
  const mine = placed.get(idKey(op.id));
  if (mine !== undefined) {
    for (let i = 0; i < state.length; i++) {
      const p = placed.get(idKey(state[i].id));
      if (p === undefined) continue;
      if (p < mine) lo = Math.max(lo, i + 1);
      else hi = Math.min(hi, i);
    }
  }
  return placementsIn(state, op, lo, hi, opts);
}

/** Position of every id in a view that carries ids, keyed by `idKey`. */
export function placementOf(target) {
  const placed = new Map();
  target.forEach((e, i) => {
    if (e.id !== undefined) placed.set(idKey(e.id), i);
  });
  return placed;
}

/** Visible characters as `[ { ch, attrs } ]`, attrs normalised. */
export function view(state) {
  return state.filter((c) => !c.deleted).map((c) => ({ ch: c.ch, attrs: normaliseAttrs(c.attrs) }));
}

/** Visible characters as `[ { id, ch, attrs } ]`, attrs normalised. */
export function viewWithIds(state) {
  return state.filter((c) => !c.deleted).map((c) => ({ id: c.id, ch: c.ch, attrs: normaliseAttrs(c.attrs) }));
}

/** Canonical string of a view; two views are equal exactly when their keys are. */
export function viewKey(v) {
  return JSON.stringify(v.map((e) => [e.ch, Object.entries(normaliseAttrs(e.attrs))]));
}

/** Equality of views up to attribute key order and null-valued keys. */
export function viewsEqual(a, b) {
  return viewKey(a) === viewKey(b);
}

/** Strips identities and normalises attributes: the displayed form of a view. */
export function normaliseView(v) {
  return v.map((e) => ({ ch: e.ch, attrs: normaliseAttrs(e.attrs) }));
}

/**
 * Index-level local edit on a view `[ { ch, attrs } ]` under an expand
 * configuration.
 *   insert { index, text }: splice the characters of `text`, each with
 *     `expandAttrs(view[index - 1], view[index])`.
 *   delete { index, len }: remove positions [index, index + len).
 *   mark { index, len, key, value }: set `key` on exactly positions
 *     [index, index + len).
 *   unmark { index, len, key }: clear `key` on exactly those positions.
 * Throws a RangeError on out-of-range requests.
 */
export function localEdit(v, request, expand = EXPAND) {
  const n = v.length;
  const isNat = (x) => Number.isInteger(x) && x >= 0;
  const ranged = () => {
    if (!isNat(request.index) || !isNat(request.len) || request.len < 1 || request.index + request.len > n)
      throw new RangeError(`${request.kind} range out of range`);
  };
  const norm = (e) => ({ ch: e.ch, attrs: normaliseAttrs(e.attrs) });
  switch (request.kind) {
    case 'insert': {
      if (!isNat(request.index) || request.index > n) throw new RangeError('insert index out of range');
      const a = expandAttrs(v[request.index - 1] ?? null, v[request.index] ?? null, expand);
      const added = [...request.text].map((ch) => ({ ch, attrs: { ...a } }));
      return [...v.slice(0, request.index).map(norm), ...added, ...v.slice(request.index).map(norm)];
    }
    case 'delete':
      ranged();
      return [...v.slice(0, request.index), ...v.slice(request.index + request.len)].map(norm);
    case 'mark':
    case 'unmark': {
      ranged();
      const value = request.kind === 'mark' ? request.value : null;
      return v.map((e, i) => (i >= request.index && i < request.index + request.len ? { ch: e.ch, attrs: setAttr(e.attrs, request.key, value) } : norm(e)));
    }
    default:
      throw new Error('unknown request kind: ' + request.kind);
  }
}

/**
 * The specification operations denoted by a replica record.
 *   insert { chars: [ { id, ch, origin, rightOrigin, attrs, knownMarks } ] }
 *                                                               -> one insert per character, in order
 *   delete { deleted: [id] }                                    -> one delete
 *   mark / unmark { markId, range: { left, right, outerLeft, outerRight }, styleKey, value }
 *                                                               -> one mark (value null for unmark)
 */
export function interpret(record) {
  switch (record.kind) {
    case 'insert':
      return record.chars.map((c) => ({
        kind: 'insert',
        id: c.id,
        ch: c.ch,
        origin: c.origin ?? null,
        rightOrigin: c.rightOrigin ?? null,
        attrs: normaliseAttrs(c.attrs ?? {}),
        knownMarks: c.knownMarks ?? record.knownMarks ?? [],
      }));
    case 'delete':
      return [{ kind: 'delete', ids: record.deleted }];
    case 'mark':
    case 'unmark':
      return [
        {
          kind: 'mark',
          mid: record.markId,
          left: record.range.left,
          right: record.range.right,
          outerLeft: record.range.outerLeft ?? null,
          outerRight: record.range.outerRight ?? null,
          key: record.styleKey,
          value: record.kind === 'mark' ? record.value : null,
        },
      ];
    default:
      throw new Error('unknown record kind: ' + record.kind);
  }
}

const PLACEMENTS = new WeakMap();

function placementCached(target) {
  let placed = PLACEMENTS.get(target);
  if (!placed) PLACEMENTS.set(target, (placed = placementOf(target)));
  return placed;
}

const carriesIds = (target) => target.length > 0 && target[0].id !== undefined;

/**
 * The specification as an ra-pbt specification object under an insertion
 * rule ('gap', the default, 'left' or 'both'), a reading of the expand
 * configuration ('carry', the default, 'inherit', 'expand' or 'anchors') and
 * an expand configuration. The 'anchors' reading is relational in marks, so
 * under it even the deterministic insertion rules use `applyAll`. The gap
 * rule is relational: `applyAll` admits every placement in the gap,
 * `applyDirected` those consistent with a target that carries identities,
 * and `apply` returns the leftmost placement.
 */
export function textSpec(rule = 'gap', { attrsMode = 'carry', expand = EXPAND } = {}) {
  const opts = { attrsMode, expand };
  const common = {
    init: initial,
    view,
    serialise,
    viewKey,
    normalise: normaliseView,
    localEdit: (v, request) => localEdit(v, request, expand),
    expand,
    attrsMode,
  };
  if (rule === 'gap')
    return {
      ...common,
      rule,
      apply: (state, op) => applyAll(state, op, 'gap', opts)[0] ?? null,
      applyAll: (state, op) => applyAll(state, op, 'gap', opts),
      applyDirected: (state, op, target) => applyPlaced(state, op, placementCached(target), opts),
      directs: (target) => target !== null && carriesIds(target),
    };
  if ((rule === 'left' || rule === 'both') && attrsMode === 'anchors')
    return { ...common, rule, apply: (state, op) => apply(state, op, rule, opts), applyAll: (state, op) => applyAll(state, op, rule, opts) };
  if (rule === 'left' || rule === 'both') return { ...common, rule, apply: (state, op) => apply(state, op, rule, opts) };
  throw new Error('unknown insertion rule: ' + rule);
}
