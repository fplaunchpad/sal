/**
 * Mechanism classification of failures of the production block instance.
 *
 * A failure is named by re-executing its schedule with the adapter's
 * observer, which reports every record issued or applied at a replica with
 * the whole document state before and after (`stateOf`): every block record
 * with its alive flag and visible character keys, the page's content, and
 * the search label of every slice. The classifier reads that evidence; it
 * never decides a failure.
 *
 * Evidence per applied record:
 *   rejected        the shipped handlers threw; the replica was restored
 *   misaddressed    some operation of the record names an item (an origin,
 *                   a slice start or end, an annotation anchor) that lies
 *                   within the range of the operation's search label at
 *                   the issuer, when it issued the record, and outside it
 *                   at the receiver. A
 *                   receiver applies a text operation only to the slices
 *                   whose labels lie in the range of the operation's label
 *                   (module 121141, function TA); a label's range is its
 *                   descendants in the binary subdivision that
 *                   `updateSearchLabelAfterSplit` (458789, 663360) applies
 *                   at every split, so labels depend on the order in which
 *                   a replica applied concurrent splits
 *   removedAnchor   a create or split whose new block is listed after a
 *                   block no longer in the page's content (listAfter then
 *                   appends at the end, modules 929891 and 75332)
 *   staleMerge      a merge whose source block was already removed at the
 *                   receiver (its split and move still apply)
 *   removedSplit    a split whose source block was already removed at the
 *                   receiver
 *   relocated       characters whose holding block changed; hidden:
 *                   characters visible before and not after
 *
 * Classes, in priority order for each check:
 *   label-divergence   a rejected record that is misaddressed
 *   past-boundary      a rejected record, not misaddressed, with a split or
 *                      insertion (of a split request, an insert request, or
 *                      a merge's split at the source's start) whose origin,
 *                      at the receiver, is the last item of its slice
 *                      before an end marker the issuer did not have: the
 *                      new item, ordered by identifier among the concurrent
 *                      siblings of its origin, integrates past the end of
 *                      the origin's slice (`splitTextSliceResult must
 *                      exist`, `Failed to find target text slice after
 *                      backfilling`)
 *   rejected-other     any other rejected record
 *   duplicate-marker   (any check at the replica) two slices of one text
 *                      instance start at the same item: split markers
 *                      allocated from per-tree clocks (the library's
 *                      record-model trees, `liveClock: false`)
 *   stale-merge        (RA-linearizability) a staleMerge at the replica
 *   removed-anchor     (RA-linearizability) a removedAnchor at the replica
 *   bold-flags         (RA-linearizability) none of the above, and the
 *                      display's block texts are those of an admitted view
 *                      in order: only bold flags differ
 *   order-mismatch     (RA-linearizability) none of the above, and the
 *                      multiset of block texts of the display is that of
 *                      an admitted view: the blocks are right and their
 *                      order is not
 *   misrouted-label    (RA-linearizability) none of the above, and an
 *                      applied, misaddressed record relocated or hid
 *                      characters
 *   text-loss          (conservation) characters hidden by an applied
 *                      record, no rejection
 *   stale-merge        (convergence) no rejection or concurrent move, and
 *                      a staleMerge applied at some replica
 *   concurrent-move    (convergence) no rejection, and two concurrent
 *                      records move the same slice (same text instance and
 *                      start item) into different blocks: the move applied
 *                      last decides where the text ends up
 *   list-order         (convergence) no rejection, and the replicas show
 *                      the same blocks in different orders: the page's
 *                      `content` is an array edited by `listAfter`, whose
 *                      concurrent insertions after one block land in
 *                      application order
 *   format-carry       (local meaning) the display's texts are the
 *                      expected ones and an insertion's bold flag is not:
 *                      the inserted characters took formatting across a
 *                      block boundary (from the end of the block a split
 *                      came from)
 *   unclassified
 */
import { Execution, finalSyncSteps } from '../../src/index.js';
import { productionBlocksInstance } from './index.js';
import { textsOf } from './spec.js';

/** The label range of module 121141: [lo, hi] covering a label and its descendants. */
export function labelRange(label) {
  if (label === '') return ['', '|'];
  const prefix = label.slice(0, -1);
  const n = label.charCodeAt(label.length - 1) - 61;
  let depth = 0;
  for (let x = n; x % 2 === 1; x >>= 1) depth++;
  const i = (1 << depth) - 1;
  return [prefix + String.fromCharCode(61 + n - i), prefix + String.fromCharCode(61 + n + i) + '|'];
}

const keyOf = (id) => (typeof id === 'string' ? id : `${id[0]}:${id[1]}`);

/**
 * [instance, label, item, role] for each item an operation locates within
 * the range of its label. Role `inner`: an item of the slice other than its
 * end item (an insertion or split origin, a moved slice's start); `end`:
 * the slice's end item (a merge target); `any`: either (annotation anchors).
 */
function addressed(op) {
  const a = op.args ?? {};
  const out = [];
  const label = a.searchLabel ?? a.sourceSearchLabel;
  if (a.textInstanceId !== undefined && label !== undefined) {
    for (const id of [a.originId, a.textSliceStartItemId]) if (id !== undefined) out.push([a.textInstanceId, label, keyOf(id), 'inner']);
    for (const id of [a.start?.id, a.end?.id]) if (id !== undefined) out.push([a.textInstanceId, label, keyOf(id), 'any']);
  }
  if (a.targetTextInstanceId !== undefined && a.targetSearchLabel !== undefined && a.targetTextSliceEndItemId !== undefined)
    out.push([a.targetTextInstanceId, a.targetSearchLabel, keyOf(a.targetTextSliceEndItemId), 'end']);
  return out;
}

const holds = (slice, item, role) =>
  role === 'end' ? slice.items[slice.items.length - 1] === item : role === 'inner' ? slice.items.slice(0, -1).includes(item) : slice.items.includes(item);

/** Whether `item` of `instance` lies, in its role, in some slice whose label is in the range of `label`. */
function inRange(state, instance, label, item, role) {
  const [lo, hi] = labelRange(label);
  return state.slices.some((s) => s.instance === instance && lo <= s.label && s.label <= hi && holds(s, item, role));
}

/**
 * Whether some operation of the record names an item that lies within its
 * label's range at the issuer and outside it at the receiver.
 */
export function misaddressed(ops, issuer, receiver) {
  return ops.some((op) => addressed(op).some(([inst, label, item, role]) => inRange(issuer, inst, label, item, role) && !inRange(receiver, inst, label, item, role)));
}

/** Whether two slices of one text instance start at the same item. */
export function duplicateStarts(state) {
  const seen = new Set();
  for (const sl of state.slices) {
    const k = `${sl.instance}/${sl.items[0]}`;
    if (seen.has(k)) return k;
    seen.add(k);
  }
  return null;
}

/** The slices a record moves into another block: `instance/start` of each move whose target differs from its pointer. */
const movesOf = (ops) =>
  ops
    .filter((o) => (o.command === 'moveTextSlice' || o.command === 'moveTextSliceIntoBlock') && o.args.targetBlockId !== o.pointer.id)
    .map((o) => `${o.args.textInstanceId}/${keyOf(o.args.textSliceStartItemId)}`);

/** Two concurrent issued records that move the same slice, or null. */
function concurrentMoves(events) {
  const issued = events.filter((e) => e.phase === 'issue');
  const past = new Map(issued.map((e) => [e.key, new Set(e.prior)]));
  const before = (a, b) => {
    const seen = new Set();
    const stack = [...(past.get(b) ?? [])];
    while (stack.length) {
      const k = stack.pop();
      if (k === a) return true;
      if (seen.has(k)) continue;
      seen.add(k);
      stack.push(...(past.get(k) ?? []));
    }
    return false;
  };
  for (let i = 0; i < issued.length; i++)
    for (let j = i + 1; j < issued.length; j++) {
      const a = issued[i];
      const b = issued[j];
      const shared = a.moves.filter((m) => b.moves.includes(m));
      if (shared.length && !before(a.key, b.key) && !before(b.key, a.key)) return { records: [a.key, b.key], slice: shared[0] };
    }
  return null;
}

const visible = (st) => new Set(st.content.filter((id) => st.blocks[id]?.alive).flatMap((id) => st.blocks[id].chars));
const holders = (st) => {
  const m = new Map();
  for (const [id, b] of Object.entries(st.blocks)) for (const k of b.chars) m.set(k, id);
  return m;
};

/**
 * Executes a schedule (with the final sync unless `finalSync` is false) on a
 * fresh instance with the observer; returns { events, issued } where each
 * event carries its step index and the evidence above.
 */
export function observeSchedule(lib, options, schedule, { finalSync = true } = {}) {
  const raw = [];
  let step = -1;
  const inst = productionBlocksInstance(lib, { ...options, observe: (e) => e.replica < 1000 && raw.push({ ...e, step }) });
  const ex = new Execution(inst, schedule.replicas, { checks: [] });
  schedule.steps.forEach((s, i) => {
    step = i;
    ex.apply(s);
  });
  if (finalSync)
    for (const s of finalSyncSteps(schedule.replicas)) {
      step = ex.steps.length;
      ex.apply(s);
    }
  const issued = new Map();
  for (const e of raw) if (e.phase === 'issue') issued.set(e.record.update.key, e);
  const events = raw.map((e) => {
    const rec = e.record;
    const out = { phase: e.phase, step: e.step, replica: e.replica, key: rec.update.key, kind: rec.kind, request: rec.request, ok: e.ok, message: e.message, duplicate: duplicateStarts(e.after), prior: rec.update.prior, moves: movesOf(rec.update.ops) };
    if (e.phase !== 'apply') return out;
    const issuer = issued.get(rec.update.key);
    out.misaddressed = !!issuer && misaddressed(rec.update.ops, issuer.before, e.before);
    out.pastBoundary = !!issuer && pastBoundary(rec.update.ops, issuer.before, e.before);
    const after = rec.update.ops.find((o) => o.command === 'listAfter')?.args.after;
    out.removedAnchor = after !== undefined && !e.before.content.includes(after);
    if (!e.ok) return out;
    const hb = holders(e.before);
    const ha = holders(e.after);
    out.relocated = [...ha].filter(([k, b]) => hb.has(k) && hb.get(k) !== b).map(([k]) => k);
    const vb = visible(e.before);
    const va = visible(e.after);
    out.hidden = [...vb].filter((k) => !va.has(k));
    if (rec.kind === 'merge' || rec.kind === 'split') {
      const source = rec.update.ops.find((o) => o.command === 'moveTextSlice' || o.command === 'moveTextSliceIntoBlock')?.pointer.id;
      const alive = source && e.before.blocks[source]?.alive;
      if (rec.kind === 'merge') out.staleMerge = alive === false;
    }
    return out;
  });
  return { events, instance: inst, execution: ex };
}

const rejection = (e) => (e.misaddressed ? 'label-divergence' : e.pastBoundary ? 'past-boundary' : 'rejected-other');

/**
 * Whether some split or insertion of the record has an origin that, at the
 * receiver, is the last item of a slice in its label's range, before an end
 * marker absent from the issuer's slices of that instance.
 */
export function pastBoundary(ops, issuer, receiver) {
  return ops.some((op) => {
    if (op.command !== 'splitText' && op.command !== 'insertText') return false;
    const a = op.args;
    const origin = keyOf(a.originId);
    const [lo, hi] = labelRange(a.searchLabel ?? '');
    const known = new Set(issuer.slices.filter((sl) => sl.instance === a.textInstanceId).flatMap((sl) => sl.items));
    return receiver.slices.some((sl) => {
      if (sl.instance !== a.textInstanceId || sl.label < lo || sl.label > hi) return false;
      const n = sl.items.length;
      return n >= 2 && sl.items[n - 2] === origin && sl.items[n - 1] !== 'end' && !known.has(sl.items[n - 1]);
    });
  });
}

/** The class of one failure of a trace of `schedule` (see above), with the evidence used. */
export function classifyFailure(lib, options, schedule, failure, observed = null) {
  const { events } = observed ?? observeSchedule(lib, options, schedule);
  const applies = events.filter((e) => e.phase === 'apply');
  const rejected = applies.filter((e) => !e.ok);
  const pick = (cls, evidence) => ({ class: cls, evidence });
  const at = Array.isArray(failure.replica) ? failure.replica : [failure.replica];
  const dup = events.find((e) => e.duplicate && at.includes(e.replica) && e.step <= failure.step);
  if (dup) return pick('duplicate-marker', { record: dup.key, slice: dup.duplicate });
  if (failure.check === 'convergence' || failure.check === 'conservation') {
    const r = rejected[0];
    if (r) return pick(rejection(r), { record: r.key, kind: r.kind, replica: r.replica, step: r.step, message: r.message });
    if (failure.check === 'conservation') {
      const h = applies.find((e) => e.hidden?.length);
      if (h) return pick(h.staleMerge ? 'stale-merge' : 'text-loss', { record: h.key, kind: h.kind, replica: h.replica, hidden: h.hidden });
    }
    if (failure.check === 'convergence') {
      const blocks = (v) => JSON.stringify(v.map((cs) => JSON.stringify(cs)).sort());
      if (blocks(failure.expected) === blocks(failure.actual)) return pick('list-order', {});
      const m = concurrentMoves(events);
      if (m) return pick('concurrent-move', m);
      const st = applies.find((x) => x.staleMerge);
      if (st) return pick('stale-merge', { record: st.key, replica: st.replica });
    }
    return pick('unclassified', {});
  }
  if (failure.check === 'raLinearizability') {
    const here = applies.filter((e) => e.replica === failure.replica && e.step <= failure.step);
    const firstOf = (p) => here.find(p);
    let e;
    if ((e = here.find((x) => !x.ok))) return pick(rejection(e), { record: e.key, kind: e.kind, message: e.message });
    if ((e = firstOf((x) => x.staleMerge))) return pick('stale-merge', { record: e.key, request: e.request, relocated: e.relocated });
    if ((e = firstOf((x) => x.removedAnchor))) return pick('removed-anchor', { record: e.key, request: e.request });
    if (failure.expected?.admittedViews?.some((v) => JSON.stringify(textsOf(v)) === JSON.stringify(textsOf(failure.actual)))) return pick('bold-flags', {});
    const bag = (v) => JSON.stringify(textsOf(v).sort());
    if (failure.expected?.admittedViews?.some((v) => bag(v) === bag(failure.actual))) return pick('order-mismatch', {});
    if ((e = firstOf((x) => x.misaddressed && (x.relocated?.length || x.hidden?.length)))) return pick('misrouted-label', { record: e.key, kind: e.kind, request: e.request });
    return pick('unclassified', {});
  }
  if (failure.check === 'localMeaning') {
    const sameText = JSON.stringify(textsOf(failure.expected)) === JSON.stringify(textsOf(failure.actual));
    if (sameText && failure.request.kind === 'insert') return pick('format-carry', { request: failure.request });
    return pick('unclassified', { request: failure.request });
  }
  return pick('unclassified', {});
}
