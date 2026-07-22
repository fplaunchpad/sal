// Rich-text editor binding (browser-safe, no DOM): translate editor gestures on
// a Peritext document into peritext ops. The marks analog of editbind.js, and
// the op layer of the #107 editor. It sits on the verified Peritext datatype
// (runtime/src/datatypes/peritext.js), whose read() is [{id, char, marks}].
//
// A gesture becomes an OP LIST (a batch): a contiguous text replacement -> del/
// ins ops; a format gesture over a selection -> one addMark/removeMark. commitOps
// seals the whole list as ONE group-op commit (node.commitBatch, applied via
// peritext.applyBatch in one transient pass, proven equal to folding apply;
// runtime/test/applybatch.test + runtime/test/commitbatch.test). A typing run,
// a paste, and a multi-char format each land as a single commit, not one per
// character.
//
// mint() must be a MONOTONIC counter (fresh strictly-increasing int) shared by
// char ids and mark mids/ts. Two consequences the semantics rely on: a mark's
// ts then exceeds every char that predates it, so end-side growth grabs only
// text typed AFTER the mark; and a removeMark minted later always outranks the
// addMark it retracts (per-(char,mtype) last-writer-wins by mid).

import { peritext } from '../../runtime/src/datatypes/peritext.js';

/** {ids, text} for a read() doc array: ids[i]/text[i] is the char shown at
 *  reading position i. The coordinate the *Ops functions edit against. */
export function docSnapshot(doc) {
  return { ids: doc.map((e) => e.id), text: doc.map((e) => e.char).join('') };
}

/** Contiguous text replacement oldText -> newText as del/ins ops (the same
 *  prefix/suffix diff as editbind.applyTextEdit, returning ops instead of
 *  committing). Deletes are logical; new chars anchor after the surviving char
 *  to the left of the change and chain in typing order. */
export function textEditOps(ids, oldText, newText, mint) {
  let p = 0;
  while (p < oldText.length && p < newText.length && oldText[p] === newText[p]) p++;
  let s = 0;
  while (s < oldText.length - p && s < newText.length - p &&
    oldText[oldText.length - 1 - s] === newText[newText.length - 1 - s]) s++;
  const delCount = oldText.length - p - s;
  const insStr = newText.slice(p, newText.length - s);

  const ops = [];
  for (let i = 0; i < delCount; i++) ops.push({ type: 'del', id: ids[p + i] });
  let anchor = p > 0 ? ids[p - 1] : null; // the character to the LEFT of the change
  for (const ch of insStr) {
    const id = mint();
    ops.push({ type: 'ins', id, el: ch, anchorId: anchor });
    anchor = id;
  }
  return ops;
}

/** Format a selection [from, to) (reading positions, `to` exclusive) with an
 *  mtype. addMark by default; { remove:true } emits the negative mark that
 *  retracts it (wins by the fresh, higher mid). Default gravity is bold/italic:
 *  before/after covers exactly the selected chars now and grows over text typed
 *  at the end. Pass sides for others (a link is before/before). [] on an empty
 *  selection. */
export function formatOps(ids, from, to, mtype, mint, opts = {}) {
  if (to <= from) return [];
  const { remove = false, value = null, startSide = 'before' } = opts;
  let { endSide = 'after' } = opts;
  const mid = mint();
  // endSide 'after' anchors ON the last selected char (inclusive, grows over
  // newer trailing text: bold). endSide 'before' anchors on the FIRST
  // UNSELECTED char (exclusive, never grows: link/comment); at document end
  // there is no successor to anchor on, so fall back to an inclusive end (the
  // mark may then grow over text typed later at the very end).
  let endId;
  if (endSide === 'before' && to < ids.length) endId = ids[to];
  else { endId = ids[to - 1]; endSide = 'after'; }
  return [{
    type: remove ? 'removeMark' : 'addMark',
    mid, mtype, value,
    startId: ids[from], endId,
    startSide, endSide, ts: mid,
  }];
}

/** Apply a gesture's op list to a replica as ONE group-op commit
 *  (node.commitBatch, applied via the datatype's applyBatch in one transient
 *  pass). Falls back to per-op commits on a replica that predates commitBatch.
 *  Returns the ops applied. */
export function commitOps(node, ops) {
  if (ops.length === 0) return ops;
  if (typeof node.commitBatch === 'function') node.commitBatch(ops);
  else for (const op of ops) node.commit(op);
  return ops;
}

// ---- gesture wrappers on a live replica: read -> ops -> commit -------------

/** Type/paste/backspace: reconcile the doc's text to `newText`. */
export function typeEdit(node, newText, mint) {
  const { ids, text } = docSnapshot(node.read());
  return commitOps(node, textEditOps(ids, text, newText, mint));
}

/** Toggle a mark over selection [from, to): addMark, or removeMark if the
 *  selection is already fully covered by `mtype`. */
export function format(node, from, to, mtype, mint, opts = {}) {
  const doc = node.read();
  const ids = doc.map((e) => e.id);
  return commitOps(node, formatOps(ids, from, to, mtype, mint, opts));
}

/** Is every char in [from, to) currently carrying `mtype`? (drives a toggle:
 *  fully-set -> remove, else -> add.) */
export function selectionHas(doc, from, to, mtype) {
  if (to <= from) return false;
  for (let i = from; i < to; i++) {
    if (!doc[i].marks.some((m) => m.mtype === mtype)) return false;
  }
  return true;
}

/** The mtypes (optionally filtered by prefix) covering EVERY char of
 *  [from, to). Drives the comment toggle under the unique-mtype encoding
 *  (each comment is its own `comment:<id>` mtype, note text in `value`, so
 *  overlapping comments never collapse under the per-(char,mtype) LWW). */
export function coveringMarkTypes(doc, from, to, prefix = '') {
  if (to <= from || from < 0 || to > doc.length) return [];
  const cand = [...new Set(doc[from].marks.map((m) => m.mtype))]
    .filter((t) => t.startsWith(prefix));
  return cand.filter((t) => selectionHas(doc, from, to, t));
}

/** SPECULATIVE read: the head state plus PENDING (uncommitted) ops, applied
 *  in one transient pass. The debounced editor renders THIS while it buffers
 *  a typing run; flush seals `pending` as ONE group-op commit whose applyBatch
 *  fold reproduces exactly this state (that is the definition of both sides).
 *  CRDT ops are self-contained (ids, not positions), so pending ops survive a
 *  remote merge landing mid-buffer: re-deriving specRead on the new head is
 *  still correct. */
export function specRead(node, pending) {
  if (!pending || pending.length === 0) return node.read();
  return node.datatype.read(node.datatype.applyBatch(node.head.state, pending));
}

/** Full reading-order extent [lo, hi) of `mtype` in the doc, or null. (A
 *  comment is removed over its WHOLE span, not just the selection.) */
export function markSpan(doc, mtype) {
  let lo = -1, hi = -1;
  for (let i = 0; i < doc.length; i++) {
    if (doc[i].marks.some((m) => m.mtype === mtype)) { if (lo < 0) lo = i; hi = i + 1; }
  }
  return lo < 0 ? null : [lo, hi];
}
