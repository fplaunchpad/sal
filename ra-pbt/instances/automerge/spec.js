/**
 * Sequential specification of text with marks and element identities.
 *
 * Identities are Automerge operation ids written "counter@actor". A state is
 * an immutable object
 *   { elems: [elem], marks: [mark] }
 * where `elems` is the ordered list of list elements and `marks` lists the
 * applied mark operations sorted by identity. An element is either a
 * character { id, ch, deleted } or, under the marker semantics only, a mark
 * boundary { id, boundary: 'begin' | 'end', mark }.
 *
 * Two mark semantics share the list part.
 *
 *   anchor   Peritext's anchors (Litt et al. 2022). A mark carries a start
 *            anchor and an end anchor, each null (the start or the end of
 *            the text) or { side: 'before' | 'after', id } naming a
 *            character. A character is covered when it stands after the
 *            start anchor and before the end anchor in the current list:
 *            start { after: x } covers characters strictly after x, start
 *            { before: x } characters from x on, end { before: x }
 *            characters strictly before x, end { after: x } characters up to
 *            and including x. The anchors of a request are fixed by the
 *            expand policy: an expanding start anchors after the character
 *            before the range, a non-expanding start before the first
 *            character, and symmetrically for the end.
 *   marker   Boundaries as list elements. A mark inserts a begin boundary
 *            and an end boundary into the list under the same placement
 *            rule as characters; a character is covered when it stands
 *            between its mark's begin and end boundaries.
 *
 * Under both, the value a character shows for a mark name is the value of
 * the covering mark of that name with the greatest identity (Peritext's
 * rule: greater counter, then greater actor), and a null value (an unmark)
 * shows nothing. Applied sequentially, a mark's identity exceeds those of
 * every mark the issuer has seen, so the mark a replica issues wins on its
 * range there; between concurrent marks the identities decide. The marks
 * of a state are therefore a set, kept sorted by identity.
 *
 * List part. An element is inserted anywhere strictly after its origin
 * (the head when null) and strictly before its right origin (the end when
 * null): the strong list specification of Attiya et al. (PODC 2016) with
 * deleted characters kept as anchors. Deletion is by identity and
 * idempotent.
 *
 * This module imports nothing. `textSpec(options)` packages it as an ra-pbt
 * specification.
 */

/** Mark names and their expand policies. */
export const EXPAND = { bold: 'after', italic: 'before', link: 'none' };

/** The expand policy of a mark name ('after' when the name is not listed). */
export const expandOf = (name) => EXPAND[name] ?? 'after';
const startExpands = (p) => p === 'before' || p === 'both';
const endExpands = (p) => p === 'after' || p === 'both';

/** Attributes with null-valued keys dropped and keys in sorted order. */
export function normaliseAttrs(attrs) {
  const out = {};
  for (const k of Object.keys(attrs ?? {}).sort()) if (attrs[k] !== null && attrs[k] !== undefined) out[k] = attrs[k];
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
  return { elems: [], marks: [] };
}

/** Order of identities "counter@actor": by counter, then by actor; other strings compare as strings. */
export function compareIds(a, b) {
  const pa = a.indexOf('@');
  const pb = b.indexOf('@');
  if (pa !== -1 && pb !== -1) {
    const ca = Number(a.slice(0, pa));
    const cb = Number(b.slice(0, pb));
    if (ca !== cb) return ca - cb;
    a = a.slice(pa + 1);
    b = b.slice(pb + 1);
  }
  return a < b ? -1 : a > b ? 1 : 0;
}

/** `marks` with `m` added, sorted by identity. */
function addMark(marks, m) {
  return [...marks, m].sort((x, y) => compareIds(x.id, y.id));
}

function indexOf(elems, id) {
  for (let i = 0; i < elems.length; i++) if (elems[i].id === id) return i;
  return -1;
}

/** Canonical string of a state. */
export function serialise(state) {
  return JSON.stringify([
    state.elems.map((e) => (e.boundary ? [e.id, e.boundary, e.mark] : [e.id, e.ch, e.deleted])),
    state.marks.map((m) => [m.id, m.name, m.value, m.start ?? null, m.end ?? null]),
  ]);
}

/**
 * The positions strictly between `origin` and `rightOrigin` at which a new
 * element may be inserted, as [lo, hi] (inclusive splice indices), or null
 * when a precondition fails (an anchor is absent, the id exists, or the
 * right origin stands before the origin).
 */
function gapOf(elems, id, origin, rightOrigin) {
  if (indexOf(elems, id) !== -1) return null;
  let lo = 0;
  if (origin !== null && origin !== undefined) {
    const o = indexOf(elems, origin);
    if (o === -1) return null;
    lo = o + 1;
  }
  let hi = elems.length;
  if (rightOrigin !== null && rightOrigin !== undefined) {
    const r = indexOf(elems, rightOrigin);
    if (r === -1 || r < lo) return null;
    hi = r;
  }
  return [lo, hi];
}

/** The gap narrowed to the order `placed` (id -> position) gives the new element; unchanged when the element is not placed. */
function narrow(elems, id, [lo, hi], placed) {
  const mine = placed?.get(id);
  if (mine === undefined) return [lo, hi];
  for (let i = 0; i < elems.length; i++) {
    const p = placed.get(elems[i].id);
    if (p === undefined) continue;
    if (p < mine) lo = Math.max(lo, i + 1);
    else hi = Math.min(hi, i);
  }
  return [lo, hi];
}

/** Every list with `elem` inserted at a position in [lo, hi]. */
function placements(elems, elem, [lo, hi]) {
  const out = [];
  for (let at = lo; at <= hi; at++) out.push([...elems.slice(0, at), elem, ...elems.slice(at)]);
  return out;
}

function insertAll(elems, elem, origin, rightOrigin, placed) {
  const gap = gapOf(elems, elem.id, origin, rightOrigin);
  if (gap === null) return [];
  return placements(elems, elem, narrow(elems, elem.id, gap, placed));
}

/**
 * Every next state of one specification operation; an empty list is a
 * precondition failure. `placed`, when given, restricts placements to the
 * order it records (see `applyPlaced`).
 *
 *   insert { id, ch, origin, rightOrigin }
 *   delete { ids }                 every id must name a character
 *   mark   { id, name, value, start, end }                       (anchor)
 *   mark   { id, name, value, begin: { id, origin, rightOrigin },
 *            end: { id, origin, rightOrigin } }                  (marker)
 */
export function applyAll(state, op, placed = null) {
  switch (op.kind) {
    case 'insert':
      return insertAll(state.elems, { id: op.id, ch: op.ch, deleted: false }, op.origin, op.rightOrigin, placed).map((elems) => ({ elems, marks: state.marks }));
    case 'delete': {
      const at = new Set();
      for (const id of op.ids) {
        const i = indexOf(state.elems, id);
        if (i === -1 || state.elems[i].boundary) return [];
        at.add(i);
      }
      return [{ elems: state.elems.map((e, i) => (at.has(i) ? { ...e, deleted: true } : e)), marks: state.marks }];
    }
    case 'mark': {
      if (state.marks.some((m) => m.id === op.id)) return [];
      const mark = { id: op.id, name: op.name, value: op.value ?? null };
      if (op.begin) {
        const out = [];
        for (const e1 of insertAll(state.elems, { id: op.begin.id, boundary: 'begin', mark: op.id }, op.begin.origin, op.begin.rightOrigin, placed))
          for (const e2 of insertAll(e1, { id: op.end.id, boundary: 'end', mark: op.id }, op.end.origin, op.end.rightOrigin, placed))
            out.push({ elems: e2, marks: addMark(state.marks, { ...mark, begin: op.begin.id, end: op.end.id }) });
        return out;
      }
      for (const a of [op.start, op.end]) {
        if (a === null || a === undefined) continue;
        const i = indexOf(state.elems, a.id);
        if (i === -1 || state.elems[i].boundary) return [];
      }
      return [{ elems: state.elems, marks: addMark(state.marks, { ...mark, start: op.start ?? null, end: op.end ?? null }) }];
    }
    default:
      throw new Error('unknown operation kind: ' + op.kind);
  }
}

/** The leftmost next state, or null on a failed precondition. */
export function apply(state, op) {
  return applyAll(state, op)[0] ?? null;
}

/**
 * The next states consistent with a target placement: `placed` maps the id
 * of every element whose position the target records to that position.
 * A placed element sits in its gap in the order the target gives it
 * relative to the placed elements already present; an unplaced one may sit
 * anywhere in its gap. Elements never move once placed, so a witness under
 * `applyAll` that ends in the target's order exists exactly when one exists
 * among these placements. This identity-order restriction is stronger than
 * viewKey equality and is not used by the packaged visual specification.
 */
export function applyPlaced(state, op, placed) {
  return applyAll(state, op, placed);
}

/** Whether mark `m` covers the character at position `i`, given the position of every id. */
function covers(m, i, pos) {
  if (m.begin !== undefined) {
    const b = pos.get(m.begin);
    const e = pos.get(m.end);
    return b !== undefined && e !== undefined && b < i && i < e;
  }
  if (m.start) {
    const p = pos.get(m.start.id);
    if (m.start.side === 'after' ? !(i > p) : !(i >= p)) return false;
  }
  if (m.end) {
    const p = pos.get(m.end.id);
    if (m.end.side === 'before' ? !(i < p) : !(i <= p)) return false;
  }
  return true;
}

/** Every character, deleted or not, with the attributes it shows: [{ id, ch, deleted, attrs }]. */
export function characters(state) {
  const pos = new Map(state.elems.map((e, i) => [e.id, i]));
  const out = [];
  state.elems.forEach((e, i) => {
    if (e.boundary) return;
    const attrs = {};
    for (const m of state.marks) if (covers(m, i, pos)) attrs[m.name] = m.value; // sorted by id: the greatest covering id is written last
    out.push({ id: e.id, ch: e.ch, deleted: e.deleted, attrs: normaliseAttrs(attrs) });
  });
  return out;
}

/** Visible characters as [{ ch, attrs }]. */
export function view(state) {
  return characters(state).filter((c) => !c.deleted).map((c) => ({ ch: c.ch, attrs: c.attrs }));
}

/** Visible characters as [{ id, ch, attrs }]. */
export function viewWithIds(state) {
  return characters(state).filter((c) => !c.deleted).map((c) => ({ id: c.id, ch: c.ch, attrs: c.attrs }));
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
 * The attributes of a character inserted between displayed neighbours
 * `left` and `right` (either may be null), by the expand policy of each
 * name: 'after' takes the left neighbour's value, 'before' the right
 * neighbour's, 'none' the value both neighbours share (nothing when they
 * differ), and 'both' the value of whichever neighbour has one when they
 * agree or only one has it.
 */
export function insertedAttrs(left, right) {
  const out = {};
  const names = new Set([...Object.keys(left?.attrs ?? {}), ...Object.keys(right?.attrs ?? {})]);
  for (const k of names) {
    const l = left?.attrs?.[k] ?? null;
    const r = right?.attrs?.[k] ?? null;
    const p = expandOf(k);
    let v = null;
    if (p === 'after') v = l;
    else if (p === 'before') v = r;
    else if (p === 'none') v = l === r ? l : null;
    else v = l === r || r === null ? l : l === null ? r : null;
    if (v !== null) out[k] = v;
  }
  return out;
}

/**
 * Index-level local edit on a displayed view [{ ch, attrs }].
 *   insert { index, text, attrs }: splice the characters of `text`; each
 *     takes the attributes `insertedAttrs` gives it between its displayed
 *     neighbours, updated by `attrs`.
 *   delete { index, len }: remove positions [index, index + len).
 *   format { index, len, attrs }: merge `attrs` into exactly positions
 *     [index, index + len).
 * Throws a RangeError on an out-of-range request.
 */
export function localEdit(v, request) {
  const n = v.length;
  const isNat = (x) => Number.isInteger(x) && x >= 0;
  const norm = v.map((e) => ({ ch: e.ch, attrs: normaliseAttrs(e.attrs) }));
  switch (request.kind) {
    case 'insert': {
      if (!isNat(request.index) || request.index > n) throw new RangeError('insert index out of range');
      const right = norm[request.index] ?? null;
      let left = norm[request.index - 1] ?? null;
      const added = [];
      for (const ch of request.text) {
        const plainAttrs = insertedAttrs(left, right);
        const e = { ch, attrs: plainAttrs };
        added.push(e);
        left = e;
      }
      for (const e of added) e.attrs = mergeAttrs(e.attrs, request.attrs ?? {});
      return [...norm.slice(0, request.index), ...added, ...norm.slice(request.index)];
    }
    case 'delete':
      if (!isNat(request.index) || !isNat(request.len) || request.index + request.len > n) throw new RangeError('delete range out of range');
      return [...norm.slice(0, request.index), ...norm.slice(request.index + request.len)];
    case 'format':
      if (!isNat(request.index) || !isNat(request.len) || request.index + request.len > n) throw new RangeError('format range out of range');
      return norm.map((e, i) => (i >= request.index && i < request.index + request.len ? { ch: e.ch, attrs: mergeAttrs(e.attrs, request.attrs) } : e));
    default:
      throw new Error('unknown request kind: ' + request.kind);
  }
}

/**
 * The anchors of a mark request over visible characters `ids` (the
 * identities displayed when the mark is issued) for the range
 * [start, end) under the expand policy of `name`.
 */
export function anchorsOf(ids, start, end, name) {
  const p = expandOf(name);
  const s = startExpands(p) ? (start > 0 ? { side: 'after', id: ids[start - 1] } : null) : { side: 'before', id: ids[start] };
  const e = endExpands(p) ? (end < ids.length ? { side: 'before', id: ids[end] } : null) : { side: 'after', id: ids[end - 1] };
  return { start: s, end: e };
}

/** Position of every element a target records, from its `layout` (ids in list order) or else its visible ids. */
export function placementOf(target, mode) {
  const placed = new Map();
  if (mode === 'layout' && Array.isArray(target.layout)) target.layout.forEach((id, i) => placed.set(id, i));
  else target.forEach((e, i) => { if (e.id !== undefined) placed.set(e.id, i); });
  return placed;
}

/**
 * The specification as an ra-pbt specification object. `semantics` selects
 * the mark semantics ('anchor' or 'marker'); `direct` names the former
 * witness optimisation ('layout' or 'chars'). It remains as
 * configuration metadata, but both now use the full relational search.
 * The observation ignores identities, so restricting the search by target
 * identities or hidden layout can discard visually matching witnesses.
 */
export function textSpec({ semantics = 'anchor', direct = 'layout' } = {}) {
  return {
    semantics,
    direct,
    init: initial,
    apply,
    applyAll: (state, op) => applyAll(state, op),
    // Keep the hook for consumers that wrap it, with no target pruning.
    applyDirected: (state, op) => applyAll(state, op),
    directs: () => false,
    view,
    serialise,
    viewKey,
    normalise: normaliseView,
    localEdit,
  };
}
