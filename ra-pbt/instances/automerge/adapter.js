/**
 * Automerge replicas behind the ra-pbt adapter interface.
 *
 * Every replica holds one document whose root map has a single text object
 * `t`, created by a genesis change of actor "00" that every replica applies
 * first (a created replica) or obtains through `load` of a saved document (an
 * opened replica). Replica r has actor id r in hexadecimal, padded to an even
 * number of digits. Changes are committed with time 0, so change hashes are
 * reproducible.
 *
 * Identities. A character, a mark boundary and a deletion are operations of
 * the text object; an element's identity is its operation id
 * "counter@actor", which is also what `Automerge.getCursor` returns for a
 * visible character. `walk(doc)` reconstructs the element list of the text
 * object from the decoded changes the document holds: insert operations
 * (characters, markBegin, markEnd) form a tree by their `elemId` reference,
 * siblings are ordered by descending operation id (counter, then actor), and
 * the list is the preorder; `del` operations mark characters deleted. Every
 * view built from the walk is checked against Automerge's own `getCursor`
 * ids and `spans` rendering and throws on disagreement, so the walk is an
 * observation of the document rather than a model of it.
 *
 * Records. `update` is the change from `getLastLocalChange` (base64) and
 * `hash` its hash. A local insert is placed immediately after its recorded
 * reference, so the element that followed the reference just before the
 * operation is its right neighbour at issue time; `localNeighbours` replays
 * the change's insert operations on the walk taken before the change to
 * obtain both for every inserted element, and checks the result against the
 * walk taken after. Each record carries the specification operations under
 * both mark semantics (`specOpsBySemantics.anchor`, `.marker`).
 *
 * Delivery. `applyChanges` queues a change whose dependencies are missing;
 * `hasPending` reports a queued change (`getMissingDeps` is nonempty), and a
 * record is integrated exactly when its change is in the document
 * (`getChangeByHash`). Automerge emits no changes of its own while
 * integrating, so `emitted` is always empty.
 */
import * as A from '@automerge/automerge';
import { anchorsOf, normaliseAttrs, expandOf } from './spec.js';

export { A };

const toB64 = (bytes) => Buffer.from(bytes).toString('base64');
const fromB64 = (s) => new Uint8Array(Buffer.from(s, 'base64'));
const TEXT = ['t'];

/** The actor id of replica r: r in hexadecimal, padded to an even number of digits. */
export function actorOf(r) {
  const h = r.toString(16);
  return h.length % 2 ? '0' + h : h;
}

const GENESIS = A.getLastLocalChange(A.change(A.init({ actor: '00' }), { time: 0 }, (d) => { d.t = ''; }));

/** Parses "counter@actor". */
export function parseId(id) {
  const at = id.indexOf('@');
  return [Number(id.slice(0, at)), id.slice(at + 1)];
}

/** Automerge's operation order: by counter, then by actor id. */
export function compareIds(a, b) {
  const [ca, xa] = parseId(a);
  const [cb, xb] = parseId(b);
  if (ca !== cb) return ca - cb;
  return xa < xb ? -1 : xa > xb ? 1 : 0;
}

const DECODED = new Map();
function decode(bytes) {
  const k = toB64(bytes);
  let d = DECODED.get(k);
  if (!d) DECODED.set(k, (d = A.decodeChange(bytes)));
  return d;
}

/** Operations of a decoded change with their ids. */
function opsOf(ch) {
  return ch.ops.map((op, i) => ({ ...op, id: `${ch.startOp + i}@${ch.actor}` }));
}

/** The text object's id: the genesis change's first operation. */
const TEXT_OBJ = opsOf(A.decodeChange(GENESIS))[0].id;

/** An element of the walk from an insert operation, or null for any other operation. */
function elementOf(op) {
  if (op.obj !== TEXT_OBJ || !op.insert) return null;
  if (op.action === 'set') return { id: op.id, kind: 'char', ch: op.value, ref: op.elemId, deleted: false };
  if (op.action === 'markBegin') return { id: op.id, kind: 'begin', name: op.name, value: op.value ?? null, expand: op.expand, ref: op.elemId };
  if (op.action === 'markEnd') return { id: op.id, kind: 'end', expand: op.expand, ref: op.elemId };
  throw new Error('unexpected insert operation ' + op.action);
}

/** Orders the elements by the RGA rule: preorder of the reference tree, siblings by descending id. */
function order(elements) {
  const children = new Map();
  for (const e of elements) {
    if (!children.has(e.ref)) children.set(e.ref, []);
    children.get(e.ref).push(e);
  }
  for (const xs of children.values()) xs.sort((x, y) => compareIds(y.id, x.id));
  const out = [];
  const stack = [...(children.get('_head') ?? [])].reverse();
  while (stack.length) {
    const e = stack.pop();
    out.push(e);
    const cs = children.get(e.id);
    if (cs) for (let i = cs.length - 1; i >= 0; i--) stack.push(cs[i]);
  }
  if (out.length !== elements.length) throw new Error(`walk reached ${out.length} of ${elements.length} elements`);
  return out;
}

/** The element list of the text object: [{ id, kind, ch?, name?, value?, expand?, ref, deleted? }]. */
export function walk(doc) {
  const elements = [];
  const deleted = new Set();
  for (const bytes of A.getAllChanges(doc))
    for (const op of opsOf(decode(bytes))) {
      const e = elementOf(op);
      if (e) elements.push(e);
      else if (op.obj === TEXT_OBJ && op.action === 'del') deleted.add(op.elemId);
    }
  const list = order(elements);
  for (const e of list) if (e.kind === 'char' && deleted.has(e.id)) e.deleted = true;
  return list;
}

/**
 * Characters of a walk with the attributes Automerge's rule gives them: for
 * each name, the value of the covering mark (begin seen, end not yet seen)
 * with the greatest operation id; null values show nothing.
 */
export function attributed(list) {
  const active = new Map();
  const out = [];
  for (const e of list) {
    if (e.kind === 'begin') active.set(e.id, e);
    else if (e.kind === 'end') {
      const [c, a] = parseId(e.id);
      active.delete(`${c - 1}@${a}`);
    } else {
      const best = {};
      for (const m of active.values()) if (!best[m.name] || compareIds(m.id, best[m.name].id) > 0) best[m.name] = m;
      const attrs = {};
      for (const [k, m] of Object.entries(best)) attrs[k] = m.value;
      out.push({ id: e.id, ch: e.ch, deleted: e.deleted, attrs: normaliseAttrs(attrs) });
    }
  }
  return out;
}

/** Automerge's own rendering: [{ ch, attrs }] from `spans`. */
function rendered(doc) {
  const out = [];
  for (const s of A.spans(doc, TEXT)) {
    if (s.type !== 'text') throw new Error('non-text span ' + s.type);
    for (const ch of s.value) out.push({ ch, attrs: normaliseAttrs(s.marks ?? {}) });
  }
  return out;
}

const attrsKey = (a) => JSON.stringify(Object.entries(normaliseAttrs(a)));

export class Replica {
  /** A created replica applies the genesis change; an opened one receives a saved document through `loadFrom`. */
  constructor(id, { opened = false } = {}) {
    this.id = id;
    this.actor = actorOf(id);
    this.opened = opened;
    this.doc = opened ? null : A.applyChanges(A.init({ actor: this.actor }), [GENESIS])[0];
  }

  /** Loads `other`'s saved document. */
  loadFrom(other) {
    if (this.doc !== null) throw new Error('loadFrom must precede any use of the replica');
    this.doc = A.load(A.save(other.doc), { actor: this.actor });
  }

  /** Displayed characters with attributes, from Automerge's `spans`. */
  visible() {
    return rendered(this.doc);
  }

  /**
   * Visible characters with ids and attributes from the walk, checked
   * against `getCursor` and `spans`; the array also carries `layout`, the
   * ids of every character (deleted ones included) and `boundaries`, the ids
   * of every element, in list order.
   */
  visibleWithIds() {
    const list = walk(this.doc);
    const chars = attributed(list);
    const vis = chars.filter((c) => !c.deleted);
    const shown = rendered(this.doc);
    if (shown.length !== vis.length) throw new Error(`walk has ${vis.length} visible characters, spans ${shown.length}`);
    vis.forEach((c, i) => {
      if (c.ch !== shown[i].ch || attrsKey(c.attrs) !== attrsKey(shown[i].attrs))
        throw new Error(`walk and spans disagree at ${i}: ${c.ch}${attrsKey(c.attrs)} vs ${shown[i].ch}${attrsKey(shown[i].attrs)}`);
      const cursor = A.getCursor(this.doc, TEXT, i);
      if (cursor !== c.id) throw new Error(`walk id ${c.id} at ${i}, cursor ${cursor}`);
    });
    const out = vis.map((c) => ({ id: c.id, ch: c.ch, attrs: c.attrs }));
    out.layout = list.filter((e) => e.kind === 'char').map((e) => e.id);
    out.boundaries = list.map((e) => e.id);
    return out;
  }

  /** Hashes of every change the document holds. */
  hashes() {
    return new Set(A.getAllChanges(this.doc).map((b) => decode(b).hash));
  }

  /** Runs `fn` inside one change; returns the decoded change, its bytes and the walks before and after. */
  _change(fn) {
    const before = walk(this.doc);
    const past = this.hashes();
    const heads = A.getHeads(this.doc);
    this.doc = A.change(this.doc, { time: 0 }, fn);
    if (A.getHeads(this.doc).join() === heads.join()) throw new RangeError('the request made no change');
    const bytes = A.getLastLocalChange(this.doc);
    const ch = decode(bytes);
    return { ch, bytes, before, after: walk(this.doc), past };
  }

  /**
   * Inserts `text` at visible index `index`, then marks the inserted
   * characters with each attribute of `attrs` (null unmarks) under the
   * name's expand policy, in one change.
   */
  insert(index, text, attrs = {}) {
    const vis0 = this.visibleWithIds();
    if (index < 0 || index > vis0.length) throw new RangeError(`insert index ${index} outside [0, ${vis0.length}]`);
    const keys = Object.keys(attrs).sort();
    const c = this._change((d) => {
      A.splice(d, TEXT, index, 0, text);
      for (const k of keys) {
        const range = { start: index, end: index + text.length, expand: expandOf(k) };
        if (attrs[k] === null) A.unmark(d, TEXT, range, k);
        else A.mark(d, TEXT, range, k, attrs[k]);
      }
    });
    const local = localNeighbours(c.before, c.ch, c.after);
    const chars = local.filter((e) => e.kind === 'char');
    if (chars.map((e) => e.ch).join('') !== text) throw new Error('inserted characters differ from the text');
    const idsAfterSplice = [...vis0.slice(0, index).map((e) => e.id), ...chars.map((e) => e.id), ...vis0.slice(index).map((e) => e.id)];
    const marks = markRecords(local, keys, attrs, idsAfterSplice, index, index + text.length);
    const request = { index, text, attrs: { ...attrs } };
    return this._record('insert', request, c, { chars, marks });
  }

  /** Deletes `len` visible characters starting at `index`. */
  delete(index, len) {
    const vis = this.visibleWithIds();
    if (index < 0 || len < 1 || index + len > vis.length) throw new RangeError(`delete [${index}, ${index + len}) outside [0, ${vis.length}]`);
    const deleted = vis.slice(index, index + len).map((e) => e.id);
    const c = this._change((d) => A.splice(d, TEXT, index, len));
    const dels = opsOf(c.ch).filter((o) => o.action === 'del').map((o) => o.elemId);
    if (dels.join() !== deleted.join()) throw new Error(`deleted ids ${dels} differ from the displayed ${deleted}`);
    return this._record('delete', { index, len }, c, { deleted });
  }

  /** Marks the visible range [index, index + len) with each attribute of `attrs` (null unmarks). */
  format(index, len, attrs) {
    const vis = this.visibleWithIds();
    if (index < 0 || len < 1 || index + len > vis.length) throw new RangeError(`format [${index}, ${index + len}) outside [0, ${vis.length}]`);
    const keys = Object.keys(attrs).sort();
    const c = this._change((d) => {
      for (const k of keys) {
        const range = { start: index, end: index + len, expand: expandOf(k) };
        if (attrs[k] === null) A.unmark(d, TEXT, range, k);
        else A.mark(d, TEXT, range, k, attrs[k]);
      }
    });
    const local = localNeighbours(c.before, c.ch, c.after);
    const marks = markRecords(local, keys, attrs, vis.map((e) => e.id), index, index + len);
    return this._record('format', { index, len, attrs: { ...attrs } }, c, { covered: vis.slice(index, index + len).map((e) => e.id), marks });
  }

  _record(kind, request, c, extra) {
    const record = { replica: this.id, kind, request, update: toB64(c.bytes), hash: c.ch.hash, changeDeps: c.ch.deps, past: [...c.past], ...extra };
    record.specOpsBySemantics = { anchor: interpret(record, 'anchor'), marker: interpret(record, 'marker') };
    return record;
  }

  /** Applies a record's change; returns { pending, emitted: [] }. */
  deliver(record) {
    this.doc = A.applyChanges(this.doc, [fromB64(record.update)])[0];
    return { pending: this.hasPending(), emitted: [] };
  }

  /** Applies every change `other` holds. */
  syncFrom(other) {
    this.doc = A.merge(this.doc, other.doc);
    return { pending: this.hasPending(), emitted: [] };
  }

  hasPending() {
    return A.getMissingDeps(this.doc, A.getHeads(this.doc)).length > 0;
  }

  /** Whether the change with this hash is in the document (a queued change is not). */
  holds(hash) {
    return A.getBackend(this.doc).getChangeByHash(hash) !== null;
  }

  heads() {
    return [...A.getHeads(this.doc)].sort();
  }

  /** Element walk rendered on one line: boundaries as [name=value@id> and <@id], deleted characters with x. */
  items() {
    return walk(this.doc);
  }
}

/**
 * The inserted elements of a local change with the neighbours they had when
 * inserted: each insert operation is placed immediately after its
 * reference in the list as it stood, and its right neighbour is the element
 * that followed the reference then. Checks the replayed list against the
 * walk taken after the change.
 */
export function localNeighbours(before, ch, after) {
  const list = before.map((e) => ({ ...e }));
  const out = [];
  for (const op of opsOf(ch)) {
    const e = elementOf(op);
    if (!e) continue;
    const at = e.ref === '_head' ? 0 : list.findIndex((x) => x.id === e.ref) + 1;
    if (at === 0 && e.ref !== '_head') throw new Error('reference ' + e.ref + ' not in the list');
    const right = list[at]?.id ?? null;
    list.splice(at, 0, e);
    out.push({ ...e, origin: e.ref === '_head' ? null : e.ref, rightOrigin: right, list: list.map((x) => ({ id: x.id, kind: x.kind })) });
  }
  const replayed = list.map((x) => x.id).join(',');
  const walked = after.map((x) => x.id).join(',');
  if (replayed !== walked) throw new Error(`replayed list ${replayed} differs from the walk ${walked}`);
  return out;
}

/** The mark records of a change: one per name, with both boundaries and the anchors of the request. */
function markRecords(local, keys, attrs, ids, start, end) {
  const begins = local.filter((e) => e.kind === 'begin');
  const ends = local.filter((e) => e.kind === 'end');
  if (begins.length !== keys.length || ends.length !== keys.length) throw new Error('a mark wrote no boundary pair');
  return keys.map((k, i) => {
    const b = begins[i];
    const e = ends[i];
    if (b.name !== k) throw new Error(`boundary ${b.id} names ${b.name}, expected ${k}`);
    if (compareIds(e.id, b.id) <= 0) throw new Error('end boundary precedes its begin');
    const anchors = anchorsOf(ids, start, end, k);
    return { id: b.id, name: k, value: attrs[k] ?? null, expand: expandOf(k), begin: b, end: e, anchorStart: anchors.start, anchorEnd: anchors.end };
  });
}

/** The nearest character at or beyond position `i` of `list` in direction `dir` (-1 or +1), or null. */
function nearestChar(list, i, dir) {
  for (let j = i; j >= 0 && j < list.length; j += dir) if (list[j].kind === 'char') return list[j].id;
  return null;
}

/**
 * The specification operations of a record under a mark semantics. An
 * insert's origin and right origin are its recorded neighbours; under the
 * anchor semantics, which has no boundary elements, a boundary neighbour is
 * replaced by the nearest character beyond it (to the left for the origin,
 * to the right for the right origin), which widens the gap.
 */
export function interpret(record, semantics) {
  const insertOp = (e) => {
    if (semantics === 'marker') return { kind: 'insert', id: e.id, ch: e.ch, origin: e.origin, rightOrigin: e.rightOrigin };
    const i = e.list.findIndex((x) => x.id === e.id);
    return { kind: 'insert', id: e.id, ch: e.ch, origin: nearestChar(e.list, i - 1, -1), rightOrigin: nearestChar(e.list, i + 1, +1) };
  };
  const markOp = (m) =>
    semantics === 'marker'
      ? { kind: 'mark', id: m.id, name: m.name, value: m.value, begin: { id: m.begin.id, origin: m.begin.origin, rightOrigin: m.begin.rightOrigin }, end: { id: m.end.id, origin: m.end.origin, rightOrigin: m.end.rightOrigin } }
      : { kind: 'mark', id: m.id, name: m.name, value: m.value, start: m.anchorStart, end: m.anchorEnd };
  switch (record.kind) {
    case 'insert':
      return [...record.chars.map(insertOp), ...record.marks.map(markOp)];
    case 'delete':
      return [{ kind: 'delete', ids: record.deleted }];
    case 'format':
      return record.marks.map(markOp);
    default:
      throw new Error('unknown record kind: ' + record.kind);
  }
}

/** Validates an index-level request against a view length; throws a RangeError when it is out of range. */
export function validateEdit(request, length) {
  const nat = (x) => Number.isInteger(x) && x >= 0;
  if (request.kind === 'insert') {
    if (!nat(request.index) || request.index > length) throw new RangeError(`insert index ${request.index} outside [0, ${length}]`);
    if (typeof request.text !== 'string' || request.text.length === 0) throw new RangeError('insert text must be non-empty');
  } else if (request.kind === 'delete' || request.kind === 'format') {
    if (!nat(request.index) || !nat(request.len) || request.len < 1 || request.index + request.len > length)
      throw new RangeError(`${request.kind} [${request.index}, ${request.index + request.len}) outside [0, ${length}]`);
  } else throw new RangeError('unknown edit kind ' + request.kind);
}

/** The index-level request of an edit step (insert attrs default to {}). */
export function requestOf(step) {
  if (step.kind === 'insert') return { kind: 'insert', index: step.index, text: step.text, attrs: step.attrs ?? {} };
  if (step.kind === 'delete') return { kind: 'delete', index: step.index, len: step.len };
  return { kind: 'format', index: step.index, len: step.len, attrs: step.attrs };
}

function issueOn(rep, request) {
  if (request.kind === 'insert') return rep.insert(request.index, request.text, request.attrs ?? {});
  if (request.kind === 'delete') return rep.delete(request.index, request.len);
  if (request.kind === 'format') return rep.format(request.index, request.len, request.attrs);
  throw new RangeError('unknown edit kind ' + request.kind);
}

/**
 * The ra-pbt adapter under a mark semantics ('anchor' or 'marker'). The
 * view carries identities and the element layout, the displayed value is
 * Automerge's `spans` rendering, and the state vector is the sorted heads.
 */
export function automergeAdapter(semantics = 'anchor') {
  return {
    semantics,
    createReplica: (id, { opened = false } = {}) => new Replica(id, { opened }),
    loadInto: (rep, source) => rep.loadFrom(source),
    requestOf,
    validRequest(rep, request) {
      validateEdit(request, rep.visible().length);
      return true;
    },
    issue(rep, request) {
      const record = issueOn(rep, request);
      record.specOps = record.specOpsBySemantics[semantics];
      return record;
    },
    deliver: (rep, record) => rep.deliver(record),
    sync: (to, from) => to.syncFrom(from),
    view(rep) {
      const v = rep.visibleWithIds();
      const out = v.map((c) => ({ id: c.id, ch: c.ch, attrs: c.attrs }));
      out.layout = semantics === 'marker' ? v.boundaries : v.layout;
      return out;
    },
    displayed: (rep) => rep.visible(),
    stateVector: (rep) => ({ heads: rep.heads() }),
    hasPending: (rep) => rep.hasPending(),
    integrated(rep, records) {
      return new Set(records.filter((r) => rep.holds(r.hash)).map((r) => r.key));
    },
    /** The change's causal past (the hashes the issuer held) and the tracked past must agree. */
    crossCheck(record, records) {
      const past = new Set(record.past);
      const deps = new Set(record.deps);
      const notes = [];
      for (const o of records) {
        if (o === record) continue;
        if (past.has(o.hash) !== deps.has(o.key)) notes.push(`past of ${record.key}: ${o.key} held=${past.has(o.hash)} tracked=${deps.has(o.key)}`);
      }
      return notes;
    },
    snapshot: (rep) => ({ heads: rep.heads(), pending: rep.hasPending() }),
    traceRecord: (o) => ({
      hash: o.hash,
      chars: o.chars?.map((c) => ({ id: c.id, ch: c.ch, origin: c.origin, rightOrigin: c.rightOrigin })),
      deleted: o.deleted,
      marks: o.marks?.map((m) => ({ id: m.id, name: m.name, value: m.value, expand: m.expand, start: m.anchorStart, end: m.anchorEnd, begin: [m.begin.id, m.begin.origin, m.begin.rightOrigin], endBoundary: [m.end.id, m.end.origin, m.end.rightOrigin] })),
    }),
    inserted: (o) => (o.kind === 'insert' ? o.chars.map((c) => [c.id, c.id + '=' + c.ch]) : []),
    deleted: (o) => (o.kind === 'delete' ? o.deleted : []),
    present: (rep) => rep.visibleWithIds().map((c) => c.id + '=' + c.ch),
  };
}
