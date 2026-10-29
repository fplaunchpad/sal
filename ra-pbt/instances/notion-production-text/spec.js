/**
 * Sequential specification of the text of one block, with character
 * identities and bold.
 *
 * A state is an immutable value { chars, anns }. `chars` is the list of
 * characters { id: [session, counter], ch, deleted, bold }, deleted
 * characters remaining in place as anchors. `anns` lists the applied
 * annotations { id, start, end, value, left, right, seq } in application
 * order (`seq`).
 *
 * Operations (from `interpret`):
 *   insert { id, ch, origin, rightOrigin, bold }
 *     `origin` is the recorded origin (null for the head) and `rightOrigin`
 *     the issuer's visible right neighbour (null at the end). Under the gap
 *     rule the character lands anywhere strictly between them (the strong
 *     list specification); under `left` immediately after `origin`; under
 *     `both` immediately before `rightOrigin` when there is one, otherwise
 *     immediately after `origin`. `bold` is the value the issuer displayed
 *     for the new character, consulted only by the interval reading.
 *   delete { ids }
 *     marks the characters deleted; a deleted character stays deleted.
 *   annotate { id, start, end, value, left, right }
 *     `value` is true for an addition and null for a removal of bold.
 *
 * Two readings of annotate:
 *   anchored (the default)  an annotation is a range between its recorded
 *     anchors, each { id, anchor }. 'before X' is the gap immediately before
 *     character X, 'after X' the gap immediately after it; 'start' and 'end'
 *     stand for the ends of the text. A character is covered when it stands
 *     after the start anchor and before the end anchor at the time the view
 *     is read, so a character inserted into the range later, concurrently or
 *     not, is covered. A character's bold is the value of the last-applied
 *     annotation covering it (none when that value is null or no annotation
 *     covers it). An inserted character carries no bold of its own.
 *   interval  the Yjs-shaped reading: an annotation sets or clears bold on
 *     every character from `left` to `right` (the first and last selected
 *     characters) inclusive when it is applied, and an inserted character
 *     carries exactly the bold its issuer displayed for it.
 *
 * This module imports only the independent index-level request semantics of
 * `experiments/notion-oracle/positional-spec.mjs`, the local meaning of a
 * request on the issuer's own view.
 */
import { request as positionalRequest } from '../../../experiments/notion-oracle/positional-spec.mjs';

/** Canonical key of an id [session, counter]. */
export const idKey = (id) => id[0] + ':' + id[1];

const idEq = (a, b) => a[0] === b[0] && a[1] === b[1];

/** The empty text. */
export function initial() {
  return { chars: [], anns: [] };
}

function indexOfId(chars, id) {
  for (let i = 0; i < chars.length; i++) if (idEq(chars[i].id, id)) return i;
  return -1;
}

/** Canonical string of a state. */
export function serialise(state) {
  return JSON.stringify([
    state.chars.map((c) => [idKey(c.id), c.ch, c.deleted, !!c.bold]),
    state.anns.map((a) => idKey(a.id)),
  ]);
}

/**
 * The gap position of an anchor in units of half characters: 2i is the
 * position of character i, so 'before X' is 2·index(X) − 1 and 'after X' is
 * 2·index(X) + 1. Null when the anchor names an absent character.
 */
export function anchorPosition(chars, anchor) {
  if (anchor.id === 'start') return anchor.anchor === 'after' ? -1 : null;
  if (anchor.id === 'end') return anchor.anchor === 'before' ? 2 * chars.length - 1 : null;
  const i = indexOfId(chars, anchor.id);
  if (i === -1) return null;
  return anchor.anchor === 'before' ? 2 * i - 1 : 2 * i + 1;
}

/** Bold of every character in the anchored reading. */
export function anchoredBold(state) {
  const bold = state.chars.map(() => false);
  for (const a of state.anns) {
    const s = anchorPosition(state.chars, a.start);
    const e = anchorPosition(state.chars, a.end);
    for (let i = 0; i < state.chars.length; i++) if (s < 2 * i && 2 * i < e) bold[i] = a.value === true;
  }
  return bold;
}

/** The insertion bounds [lo, hi] of an insert in `chars`, or null when an anchor is absent. */
function gapOf(chars, op) {
  let lo = 0;
  if (op.origin !== null && op.origin !== undefined) {
    const o = indexOfId(chars, op.origin);
    if (o === -1) return null;
    lo = o + 1;
  }
  let hi = chars.length;
  if (op.rightOrigin !== null && op.rightOrigin !== undefined) {
    const r = indexOfId(chars, op.rightOrigin);
    if (r === -1 || r < lo) return null;
    hi = r;
  }
  return [lo, hi];
}

/**
 * Every state an operation leads to under an insertion rule and an
 * annotation reading. `placed`, when given, maps the key of every id of a
 * target view to its position there and restricts an insertion to the
 * positions keeping the target's order (a character absent from the target
 * may sit anywhere in its gap). An empty list is a precondition failure.
 */
export function applyAll(state, op, { rule = 'gap', reading = 'anchored', placed = null } = {}) {
  const { chars } = state;
  switch (op.kind) {
    case 'insert': {
      if (indexOfId(chars, op.id) !== -1) return [];
      const g = gapOf(chars, op);
      if (g === null) return [];
      let [lo, hi] = g;
      if (rule === 'left') hi = lo;
      else if (rule === 'both') {
        if (op.rightOrigin !== null && op.rightOrigin !== undefined) lo = hi;
        else hi = lo;
      } else if (rule !== 'gap') throw new Error('unknown insertion rule: ' + rule);
      const mine = placed ? placed.get(idKey(op.id)) : undefined;
      if (mine !== undefined)
        for (let i = 0; i < chars.length; i++) {
          const p = placed.get(idKey(chars[i].id));
          if (p === undefined) continue;
          if (p < mine) lo = Math.max(lo, i + 1);
          else hi = Math.min(hi, i);
        }
      const c = { id: op.id, ch: op.ch, deleted: false, bold: reading === 'interval' ? !!op.bold : false };
      const out = [];
      for (let at = lo; at <= hi; at++) out.push({ chars: [...chars.slice(0, at), c, ...chars.slice(at)], anns: state.anns });
      return out;
    }
    case 'delete': {
      const pos = new Set();
      for (const id of op.ids) {
        const i = indexOfId(chars, id);
        if (i === -1) return [];
        pos.add(i);
      }
      return [{ chars: chars.map((c, i) => (pos.has(i) ? { ...c, deleted: true } : c)), anns: state.anns }];
    }
    case 'annotate': {
      if (state.anns.some((a) => idEq(a.id, op.id))) return [];
      const ann = { id: op.id, start: op.start, end: op.end, value: op.value, left: op.left, right: op.right, seq: state.anns.length };
      if (reading === 'anchored') {
        const s = anchorPosition(chars, op.start);
        const e = anchorPosition(chars, op.end);
        if (s === null || e === null || s >= e) return [];
        return [{ chars, anns: [...state.anns, ann] }];
      }
      if (reading !== 'interval') throw new Error('unknown annotation reading: ' + reading);
      const l = indexOfId(chars, op.left);
      const r = indexOfId(chars, op.right);
      if (l === -1 || r === -1 || l > r) return [];
      return [{ chars: chars.map((c, i) => (i >= l && i <= r ? { ...c, bold: op.value === true } : c)), anns: [...state.anns, ann] }];
    }
    default:
      throw new Error('unknown operation kind: ' + op.kind);
  }
}

/** Visible characters as [{ id, ch, bold }] under a reading. */
export function viewWithIds(state, reading = 'anchored') {
  const bold = reading === 'anchored' ? anchoredBold(state) : state.chars.map((c) => !!c.bold);
  return state.chars.map((c, i) => ({ id: c.id, ch: c.ch, bold: bold[i], deleted: c.deleted })).filter((c) => !c.deleted).map(({ id, ch, bold: b }) => ({ id, ch, bold: b }));
}

/** Visible characters as [{ ch, bold }]. */
export const normaliseView = (v) => v.map((e) => ({ ch: e.ch, bold: !!e.bold }));

/** Canonical string of a view: characters and bold flags. */
export const viewKey = (v) => JSON.stringify(v.map((e) => [e.ch, !!e.bold]));

/** Compact rendering: bold characters followed by '*'. */
export const renderView = (v) => v.map((e) => e.ch + (e.bold ? '*' : '')).join('') || '(empty)';

/**
 * A view from a compact rendering: each character, '*' after a bold one.
 * renderView(parseView(s)) === s for every s without '(empty)'.
 */
export function parseView(s) {
  const out = [];
  for (const ch of s) {
    if (ch === '*') out[out.length - 1].bold = true;
    else out.push({ ch, bold: false });
  }
  return out;
}

const toBlock = (v) => [v.map((e) => ({ text: e.ch, bold: !!e.bold }))];
const fromBlock = (blocks) => blocks[0].map((c) => ({ ch: c.text, bold: c.bold }));

/** The request in the vocabulary of positional-spec.mjs (block 0). */
export function positionalOf(request) {
  if (request.kind === 'insert') return { kind: 'insert', block: 0, index: request.index, text: request.text };
  if (request.kind === 'delete' || request.kind === 'bold') return { kind: request.kind, block: 0, start: request.start, end: request.end };
  throw new RangeError('unknown request kind ' + request.kind);
}

/**
 * Local meaning of a request on the issuer's view.
 *   positional  `request` of positional-spec.mjs: insertion adds plain
 *     characters, deletion removes [start, end), bold toggles [start, end)
 *     (removes it when every selected character is bold, adds it otherwise).
 *   inherit     the same, except that inserted characters take the bold of
 *     the visible character to their left, and are plain at index 0.
 * Throws a RangeError on an out-of-range request.
 */
export function localEdit(v, request, mode = 'positional') {
  const n = v.length;
  const nat = (x) => Number.isInteger(x) && x >= 0;
  if (request.kind === 'insert') {
    if (!nat(request.index) || request.index > n || typeof request.text !== 'string' || request.text.length === 0) throw new RangeError('insert out of range');
  } else if (!nat(request.start) || !nat(request.end) || request.start >= request.end || request.end > n) throw new RangeError(`${request.kind} out of range`);
  const out = fromBlock(positionalRequest(toBlock(normaliseView(v)), positionalOf(request)));
  if (mode === 'inherit' && request.kind === 'insert') {
    const b = request.index > 0 && !!v[request.index - 1].bold;
    for (let k = 0; k < request.text.length; k++) out[request.index + k].bold = b;
  } else if (mode !== 'positional' && mode !== 'inherit') throw new Error('unknown local meaning: ' + mode);
  return out;
}

/** Specification operations of an adapter record. */
export function interpret(record) {
  switch (record.kind) {
    case 'insert':
      return record.chars.map((c) => ({ kind: 'insert', id: c.id, ch: c.ch, origin: c.origin, rightOrigin: c.rightOrigin, bold: !!c.bold }));
    case 'delete':
      return [{ kind: 'delete', ids: record.deletedIds }];
    case 'bold':
      return [{ kind: 'annotate', ...record.annotation }];
    default:
      throw new Error('unknown record kind: ' + record.kind);
  }
}

/** Every visible id position of a target view, by key. */
function placementOf(target) {
  const placed = new Map();
  target.forEach((e, i) => e.id !== undefined && placed.set(idKey(e.id), i));
  return placed;
}

/**
 * The specification as an ra-pbt specification object.
 *   rule     'gap' (relational, the default), 'left' or 'both'
 *   reading  'anchored' (the default) or 'interval'
 *   local    'positional' (the default) or 'inherit'
 */
export function textSpec({ rule = 'gap', reading = 'anchored', local = 'positional' } = {}) {
  const placements = new WeakMap();
  const placedOf = (target) => {
    let p = placements.get(target);
    if (!p) placements.set(target, (p = placementOf(target)));
    return p;
  };
  return {
    rule,
    reading,
    local,
    init: initial,
    serialise,
    view: (s) => viewWithIds(s, reading),
    viewKey,
    normalise: normaliseView,
    localEdit: (v, request) => localEdit(v, request, local),
    apply: (s, op) => applyAll(s, op, { rule, reading })[0] ?? null,
    applyAll: (s, op) => applyAll(s, op, { rule, reading }),
    applyDirected: (s, op, target) => applyAll(s, op, { rule, reading, placed: placedOf(target) }),
    directs: (target) => Array.isArray(target) && target.length > 0 && target[0].id !== undefined,
  };
}
