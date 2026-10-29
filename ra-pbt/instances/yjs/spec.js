/**
 * Sequential specification of formatted text with character identities.
 *
 * A state is an immutable ordered array of characters
 *   { id: [client, clock], ch, deleted: boolean, attrs: { key: value } }.
 * Every operation returns a fresh array (or null when its precondition fails),
 * so states can be memoised and compared through `serialise`.
 *
 * This module is self-contained: it imports nothing. `textSpec(rule)` packages
 * the functions as an ra-pbt specification.
 */

/** Canonical string key of an id `[client, clock]`. */
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

/** `base` updated by `delta`: a null value removes the key, any other value sets it. */
export function mergeAttrs(base, delta) {
  const out = { ...base };
  for (const k of Object.keys(delta ?? {})) {
    if (delta[k] === null) delete out[k];
    else out[k] = delta[k];
  }
  return normaliseAttrs(out);
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
  return JSON.stringify(
    state.map((c) => [idKey(c.id), c.ch, c.deleted, Object.entries(normaliseAttrs(c.attrs))]),
  );
}

/**
 * Apply one specification operation.
 *   insert { id, ch, origin, rightOrigin, attrs }: under the two-sided rule
 *     (`rule = 'both'`, the default here), place immediately before
 *     `rightOrigin` when it is present, otherwise immediately after `origin`
 *     (head when null); under the one-sided rule (`rule = 'left'`), always
 *     immediately after `origin`. The gap rule (`rule = 'gap'`), which admits
 *     every position strictly between the two, is relational and lives in
 *     `applyAll`.
 *   delete { ids }: mark each character deleted; a character already deleted
 *     stays deleted, so concurrent deletes of one character commute.
 *   format { left, right, attrs }: merge `attrs` into every character from
 *     `left` to `right` inclusive, deleted or not.
 * Returns the new state, or null when a precondition fails.
 */
export function apply(state, op, rule = 'both') {
  switch (op.kind) {
    case 'insert': {
      if (indexOfId(state, op.id) !== -1) return null;
      let at = 0;
      if (op.origin !== null && op.origin !== undefined) {
        const o = indexOfId(state, op.origin);
        if (o === -1) return null;
        at = o + 1;
      }
      if (rule === 'both' && op.rightOrigin !== null && op.rightOrigin !== undefined) {
        const r = indexOfId(state, op.rightOrigin);
        if (r === -1 || r < at) return null;
        at = r;
      }
      const c = { id: op.id, ch: op.ch, deleted: false, attrs: normaliseAttrs(op.attrs) };
      return [...state.slice(0, at), c, ...state.slice(at)];
    }
    case 'delete': {
      const positions = [];
      for (const id of op.ids) {
        const i = indexOfId(state, id);
        if (i === -1) return null;
        positions.push(i);
      }
      return state.map((c, i) => (positions.includes(i) ? { ...c, deleted: true } : c));
    }
    case 'format': {
      const l = indexOfId(state, op.left);
      const r = indexOfId(state, op.right);
      if (l === -1 || r === -1 || l > r) return null;
      return state.map((c, i) => (i >= l && i <= r ? { ...c, attrs: mergeAttrs(c.attrs, op.attrs) } : c));
    }
    default:
      throw new Error('unknown operation kind: ' + op.kind);
  }
}

/** Visible characters as `[ { ch, attrs } ]`, attrs normalised. */
export function view(state) {
  return state.filter((c) => !c.deleted).map((c) => ({ ch: c.ch, attrs: normaliseAttrs(c.attrs) }));
}

/** Visible characters as `[ { id, ch, attrs } ]`, attrs normalised. */
export function viewWithIds(state) {
  return state
    .filter((c) => !c.deleted)
    .map((c) => ({ id: c.id, ch: c.ch, attrs: normaliseAttrs(c.attrs) }));
}

/** Canonical string of a view; two views are equal exactly when their keys are. */
export function viewKey(v) {
  return JSON.stringify(v.map((e) => [e.ch, Object.entries(normaliseAttrs(e.attrs))]));
}

/** Deep equality of views up to attribute key order and null-valued keys. */
export function viewsEqual(a, b) {
  return viewKey(a) === viewKey(b);
}

/**
 * Index-level local edit on a view `[ { ch, attrs } ]`.
 *   insert { index, text, attrs }: splice the characters of `text`, each with exactly `attrs`.
 *   delete { index, len }: remove positions [index, index + len).
 *   format { index, len, attrs }: merge `attrs` into exactly positions [index, index + len).
 * Throws on out-of-range requests.
 */
export function localEdit(v, request) {
  const n = v.length;
  const isNat = (x) => Number.isInteger(x) && x >= 0;
  switch (request.kind) {
    case 'insert': {
      if (!isNat(request.index) || request.index > n) throw new RangeError('insert index out of range');
      const a = normaliseAttrs(request.attrs ?? {});
      const added = [...request.text].map((ch) => ({ ch, attrs: { ...a } }));
      return [...v.slice(0, request.index), ...added, ...v.slice(request.index)];
    }
    case 'delete': {
      if (!isNat(request.index) || !isNat(request.len) || request.index + request.len > n)
        throw new RangeError('delete range out of range');
      return [...v.slice(0, request.index), ...v.slice(request.index + request.len)];
    }
    case 'format': {
      if (!isNat(request.index) || !isNat(request.len) || request.index + request.len > n)
        throw new RangeError('format range out of range');
      return v.map((e, i) =>
        i >= request.index && i < request.index + request.len
          ? { ch: e.ch, attrs: mergeAttrs(e.attrs, request.attrs) }
          : { ch: e.ch, attrs: normaliseAttrs(e.attrs) },
      );
    }
    default:
      throw new Error('unknown request kind: ' + request.kind);
  }
}

/**
 * Every state an operation may lead to. Under the gap rule an insertion may
 * land at any position after `origin` (or the head) and before `rightOrigin`
 * (or the end), which is the strong list specification: the new character
 * keeps its order relative to the characters that existed when it was issued,
 * and takes any order relative to concurrent ones in the same gap. Under the
 * deterministic rules the result is a singleton. An empty list is a
 * precondition failure.
 */
export function applyAll(state, op, rule = 'gap') {
  if (rule !== 'gap' || op.kind !== 'insert') {
    const next = apply(state, op, rule === 'gap' ? 'both' : rule);
    return next === null ? [] : [next];
  }
  if (indexOfId(state, op.id) !== -1) return [];
  let lo = 0;
  if (op.origin !== null && op.origin !== undefined) {
    const o = indexOfId(state, op.origin);
    if (o === -1) return [];
    lo = o + 1;
  }
  let hi = state.length;
  if (op.rightOrigin !== null && op.rightOrigin !== undefined) {
    const r = indexOfId(state, op.rightOrigin);
    if (r === -1 || r < lo) return [];
    hi = r;
  }
  const c = { id: op.id, ch: op.ch, deleted: false, attrs: normaliseAttrs(op.attrs) };
  const out = [];
  for (let at = lo; at <= hi; at++) out.push([...state.slice(0, at), c, ...state.slice(at)]);
  return out;
}

/**
 * The gap rule directed by a target: `placed` maps the key of every id in
 * the target view to its position there. Returns every state in which the
 * inserted character sits inside its gap and in the order the target gives
 * it relative to the target's characters; a character absent from the target
 * (deleted later) may sit anywhere in its gap, since its position still
 * bounds later insertions. Characters never move once placed, so a witness
 * under the gap rule exists exactly when one exists among these placements.
 * An empty list is a precondition failure.
 */
export function applyPlaced(state, op, placed) {
  if (op.kind !== 'insert') {
    const next = apply(state, op, 'both');
    return next === null ? [] : [next];
  }
  if (indexOfId(state, op.id) !== -1) return [];
  let lo = 0;
  if (op.origin !== null && op.origin !== undefined) {
    const o = indexOfId(state, op.origin);
    if (o === -1) return [];
    lo = o + 1;
  }
  let hi = state.length;
  if (op.rightOrigin !== null && op.rightOrigin !== undefined) {
    const r = indexOfId(state, op.rightOrigin);
    if (r === -1 || r < lo) return [];
    hi = r;
  }
  const mine = placed.get(idKey(op.id));
  if (mine !== undefined) {
    for (let i = 0; i < state.length; i++) {
      const p = placed.get(idKey(state[i].id));
      if (p === undefined) continue;
      if (p < mine) lo = Math.max(lo, i + 1);
      else hi = Math.min(hi, i);
    }
  }
  const c = { id: op.id, ch: op.ch, deleted: false, attrs: normaliseAttrs(op.attrs) };
  const out = [];
  for (let at = lo; at <= hi; at++) out.push([...state.slice(0, at), c, ...state.slice(at)]);
  return out;
}

/** Position of every id in a view that carries ids, keyed by `idKey`. */
export function placementOf(target) {
  const placed = new Map();
  target.forEach((e, i) => { if (e.id !== undefined) placed.set(idKey(e.id), i); });
  return placed;
}

/**
 * The specification operations denoted by a replica operation record.
 *   insert { chars: [ { id, ch, origin, rightOrigin, attrs } ] } -> one insert per character, in order
 *   delete { deleted: [id] }                         -> one delete
 *   format { range: { left, right }, request: { attrs } } -> one format
 * The `covered` field is diagnostic and not consulted.
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
      }));
    case 'delete':
      return [{ kind: 'delete', ids: record.deleted }];
    case 'format':
      return [{ kind: 'format', left: record.range.left, right: record.range.right, attrs: record.request.attrs }];
    default:
      throw new Error('unknown record kind: ' + record.kind);
  }
}

/** Strips identities and normalises attributes: the displayed form of a view. */
export function normaliseView(v) {
  return v.map((e) => ({ ch: e.ch, attrs: normaliseAttrs(e.attrs) }));
}

const PLACEMENTS = new WeakMap();

function placementCached(target) {
  let placed = PLACEMENTS.get(target);
  if (!placed) PLACEMENTS.set(target, (placed = placementOf(target)));
  return placed;
}

/** Whether a target view carries identities, so that placements can be directed by it. */
const carriesIds = (target) => target.length > 0 && target[0].id !== undefined;

/**
 * The specification as an ra-pbt specification object under an insertion
 * rule. The gap rule (the default) is relational: `applyAll` admits every
 * placement in the gap, `applyDirected` those consistent with a target that
 * carries identities, and `apply` returns the leftmost placement. The
 * one-sided (`left`) and two-sided (`both`) rules are deterministic.
 */
export function textSpec(rule = 'gap') {
  const common = {
    init: initial,
    view,
    serialise,
    viewKey,
    normalise: normaliseView,
    localEdit,
  };
  if (rule === 'gap')
    return {
      ...common,
      rule,
      apply: (state, op) => applyAll(state, op, 'gap')[0] ?? null,
      applyAll: (state, op) => applyAll(state, op, 'gap'),
      applyDirected: (state, op, target) => applyPlaced(state, op, placementCached(target)),
      directs: (target) => target !== null && carriesIds(target),
    };
  if (rule === 'left' || rule === 'both') return { ...common, rule, apply: (state, op) => apply(state, op, rule) };
  throw new Error('unknown insertion rule: ' + rule);
}
