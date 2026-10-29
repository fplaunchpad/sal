/**
 * One Loro replica: a LoroDoc with a fixed peer id, the instance's text
 * style configuration, and a single root text container `t`.
 *
 * Identity convention: an id is a pair [peer, counter], the op id Loro
 * assigned to the character. Ids are read with `LoroText.getCursor(i)`, whose
 * `pos()` is the op id of the character at visible index i; the counters of
 * an insertion's characters are checked against the replica's version
 * vector before and after the commit, so an id is never inferred. Characters
 * are UTF-16 code units (the generator uses ASCII only).
 *
 * Every request is one transaction followed by `commit()`. Its update is
 * `export({ mode: 'update', from: vvBefore })`, exactly the ops the commit
 * created. A request Loro records no op for (a mark over characters that
 * already carry the value, an unmark over characters without the key) is
 * rejected with a RangeError.
 *
 * `loroAdapter` packages replicas as an ra-pbt adapter.
 */
import { LoroDoc } from 'loro-crdt';
import { interpret, normaliseAttrs, EXPAND } from './spec.js';

export { LoroDoc };

/** Loro's style configuration for the instance's expand table. */
export const STYLE_CONFIG = Object.freeze(Object.fromEntries(Object.entries(EXPAND).map(([k, e]) => [k, { expand: e }])));

const toB64 = (bytes) => Buffer.from(bytes).toString('base64');
const fromB64 = (s) => new Uint8Array(Buffer.from(s, 'base64'));
const vvObject = (vv) => Object.fromEntries([...vv.toJSON().entries()].sort((x, y) => (BigInt(x[0]) < BigInt(y[0]) ? -1 : 1)).map(([p, c]) => [String(p), c]));

export class Replica {
  /**
   * A created replica (`opened` false) obtains its text container at
   * construction, before any state arrives, as a client creating the
   * document does. An opened replica touches the container only after
   * `loadFrom` has imported a snapshot, as a client opening a stored
   * document does.
   */
  constructor(peer, { opened = false } = {}) {
    this.peer = peer;
    this.opened = opened;
    this.doc = new LoroDoc();
    this.doc.setPeerId(BigInt(peer));
    this.doc.configTextStyle(STYLE_CONFIG);
    this._text = opened ? null : this.doc.getText('t');
  }

  get text() {
    if (this._text === null) this._text = this.doc.getText('t');
    return this._text;
  }

  /** Imports `other`'s snapshot (and any updates it holds pending) before the text container is first touched. */
  loadFrom(other) {
    if (this._text !== null) throw new Error('loadFrom must precede any use of the text container');
    this.doc.import(other.doc.export({ mode: 'snapshot' }));
    const pending = other.doc.exportPendingUpdates();
    if (pending !== undefined) this.doc.import(pending);
    return this.text;
  }

  /** Version vector of the oplog as { peer: counterEnd }, string keys. */
  stateVector() {
    return vvObject(this.doc.oplogVersion());
  }

  hasPending() {
    return this.doc.exportPendingUpdates() !== undefined;
  }

  /** Displayed characters with attributes, from Loro's `toDelta`. */
  visible() {
    const out = [];
    for (const d of this.text.toDelta()) {
      if (typeof d.insert !== 'string') throw new Error('non-string content in delta');
      const attrs = normaliseAttrs(d.attributes ?? {});
      for (const ch of d.insert) out.push({ ch, attrs: { ...attrs } });
    }
    return out;
  }

  /** visible() with the op id of each character, read through getCursor. */
  visibleWithIds() {
    const vis = this.visible();
    const s = this.text.toString();
    if (s.length !== vis.length) throw new Error(`toString has ${s.length} units, delta ${vis.length}`);
    return vis.map((v, i) => {
      const c = this.text.getCursor(i);
      const p = c?.pos();
      c?.free();
      if (!p) throw new Error(`no cursor id at ${i}`);
      if (s[i] !== v.ch) throw new Error(`character mismatch at ${i}`);
      return { id: [Number(p.peer), p.counter], ch: v.ch, attrs: v.attrs };
    });
  }

  string() {
    return this.text.toString();
  }

  /** Runs `fn` as one transaction; returns the exported update and the counter range it created. */
  _localOp(fn) {
    const vvBefore = this.doc.oplogVersion();
    const before = this.stateVector()[String(this.peer)] ?? 0;
    fn();
    this.doc.commit();
    const svAfter = this.stateVector();
    const after = svAfter[String(this.peer)] ?? 0;
    if (after === before) throw new RangeError('local operation created no op');
    const update = toB64(this.doc.export({ mode: 'update', from: vvBefore }));
    return { update, from: before, to: after };
  }

  /** Keys "peer:counter" of every mark and unmark op the replica has integrated, from its JSON updates. */
  markIds() {
    const json = this.doc.exportJsonUpdates();
    const out = [];
    for (const ch of json.changes) {
      const peer = json.peers[Number(ch.id.split('@')[1])];
      for (const op of ch.ops) if (op.content.type === 'mark') out.push(`${peer}:${op.counter}`);
    }
    return out.sort();
  }

  /**
   * Inserts `text` at visible index `index`. chars[i].origin / rightOrigin
   * are the visible neighbours at issue time (for i > 0 the origin is the
   * previous inserted character); attrs is what Loro displays for the
   * character immediately after the commit; knownMarks are the marks the
   * replica had integrated when it issued the insert.
   */
  insert(index, text) {
    const before = this.visibleWithIds();
    const knownMarks = this.markIds();
    if (index < 0 || index > before.length) throw new RangeError(`insert index ${index} outside [0, ${before.length}]`);
    if (typeof text !== 'string' || text.length === 0) throw new RangeError('insert text must be non-empty');
    const svBefore = this.stateVector();
    const left = index > 0 ? before[index - 1].id : null;
    const right = index < before.length ? before[index].id : null;
    const op = this._localOp(() => this.text.insert(index, text));
    if (op.to - op.from !== text.length) throw new Error(`insert of ${text.length} units created ${op.to - op.from} ops`);
    const run = this.visibleWithIds().slice(index, index + text.length);
    const chars = run.map((c, k) => {
      if (c.id[0] !== this.peer || c.id[1] !== op.from + k || c.ch !== text[k]) throw new Error(`inserted character ${k} not found at visible index ${index + k}`);
      return { id: c.id, ch: c.ch, origin: k === 0 ? left : run[k - 1].id, rightOrigin: right, attrs: { ...c.attrs }, knownMarks };
    });
    return { replica: this.peer, kind: 'insert', request: { kind: 'insert', index, text }, svBefore, update: op.update, chars, counters: [op.from, op.to] };
  }

  /** Deletes `len` visible characters starting at `index`. */
  delete(index, len) {
    const before = this.visibleWithIds();
    if (index < 0 || len < 1 || index + len > before.length) throw new RangeError(`delete [${index}, ${index + len}) outside [0, ${before.length}]`);
    const svBefore = this.stateVector();
    const deleted = before.slice(index, index + len).map((c) => c.id);
    const op = this._localOp(() => this.text.delete(index, len));
    return { replica: this.peer, kind: 'delete', request: { kind: 'delete', index, len }, svBefore, update: op.update, deleted, counters: [op.from, op.to] };
  }

  /**
   * Marks (value given) or unmarks (value null) `key` over the visible range
   * [index, index + len). range.left / right are the first and last selected
   * characters; range.outerLeft / outerRight their visible neighbours outside
   * the selection (null at the ends). markId is "peer:counter" of the op
   * Loro created for the style's start.
   */
  style(index, len, key, value) {
    const before = this.visibleWithIds();
    if (index < 0 || len < 1 || index + len > before.length) throw new RangeError(`style [${index}, ${index + len}) outside [0, ${before.length}]`);
    const svBefore = this.stateVector();
    const covered = before.slice(index, index + len).map((c) => c.id);
    const range = { start: index, end: index + len };
    const op = this._localOp(() => (value === null ? this.text.unmark(range, key) : this.text.mark(range, key, value)));
    const kind = value === null ? 'unmark' : 'mark';
    const request = value === null ? { kind, index, len, key } : { kind, index, len, key, value };
    return { replica: this.peer, kind, request, svBefore, update: op.update, styleKey: key, value, markId: `${this.peer}:${op.from}`, range: { left: covered[0], right: covered[covered.length - 1], outerLeft: before[index - 1]?.id ?? null, outerRight: before[index + len]?.id ?? null, covered }, counters: [op.from, op.to] };
  }

  /** Imports bytes; returns { pending, status }. */
  importBytes(bytes) {
    const status = this.doc.import(bytes);
    return { pending: this.hasPending(), status };
  }

  /** Brings this replica up to date with `other`'s oplog. */
  syncFrom(other) {
    return this.importBytes(other.doc.export({ mode: 'update', from: this.doc.oplogVersion() }));
  }

  snapshot() {
    return { string: this.string(), pending: this.hasPending(), sv: this.stateVector() };
  }
}

/**
 * Validates an index-level request against a current view length; throws a
 * RangeError when it is out of range.
 */
export function validateEdit(request, length) {
  const nat = (x) => Number.isInteger(x) && x >= 0;
  if (request.kind === 'insert') {
    if (!nat(request.index) || request.index > length) throw new RangeError(`insert index ${request.index} outside [0, ${length}]`);
    if (typeof request.text !== 'string' || request.text.length === 0) throw new RangeError('insert text must be non-empty');
  } else if (['delete', 'mark', 'unmark'].includes(request.kind)) {
    if (!nat(request.index) || !nat(request.len) || request.len < 1 || request.index + request.len > length)
      throw new RangeError(`${request.kind} [${request.index}, ${request.index + request.len}) outside [0, ${length}]`);
    if (request.kind !== 'delete' && !(request.key in STYLE_CONFIG)) throw new RangeError('unconfigured style key ' + request.key);
  } else throw new RangeError('unknown edit kind ' + request.kind);
}

/** The index-level request of an edit step, in `localEdit` form. */
export function requestOf(step) {
  if (step.kind === 'insert') return { kind: 'insert', index: step.index, text: step.text };
  if (step.kind === 'delete') return { kind: 'delete', index: step.index, len: step.len };
  if (step.kind === 'mark') return { kind: 'mark', index: step.index, len: step.len, key: step.key, value: step.value };
  return { kind: 'unmark', index: step.index, len: step.len, key: step.key };
}

/** Issues a request on a replica; returns the record Replica produces. */
export function issueOn(rep, request) {
  if (request.kind === 'insert') return rep.insert(request.index, request.text);
  if (request.kind === 'delete') return rep.delete(request.index, request.len);
  if (request.kind === 'mark') return rep.style(request.index, request.len, request.key, request.value);
  if (request.kind === 'unmark') return rep.style(request.index, request.len, request.key, null);
  throw new RangeError('unknown edit kind ' + request.kind);
}

const k2 = (id) => id[0] + ':' + id[1];

/**
 * The ra-pbt adapter for Loro text.
 *
 * Records are Replica records extended with `specOps` (from `interpret`) and
 * `dot = [peer, counterEnd]`. Loro integrates a change only when all its
 * dependencies are present and holds it pending otherwise, so a record is
 * integrated exactly when the replica's oplog version vector covers its
 * counter range (the default `integrated` by dots, counters ending at
 * `counterEnd`). The view carries character identities for the classifier; the
 * witness search compares views without them. The displayed value is Loro's own `toDelta`.
 */
export const loroAdapter = {
  createReplica: (id, { opened = false } = {}) => new Replica(id, { opened }),
  loadInto: (rep, source) => rep.loadFrom(source),
  requestOf,
  validRequest(rep, request) {
    validateEdit(request, rep.visible().length);
    return true;
  },
  issue(rep, request) {
    const record = issueOn(rep, request);
    record.specOps = interpret(record);
    record.dot = [String(rep.peer), record.counters[1]];
    return record;
  },
  deliver(rep, record) {
    const res = rep.importBytes(fromB64(record.update));
    return { pending: res.pending, emitted: [] };
  },
  sync(to, from) {
    const res = to.syncFrom(from);
    return { pending: res.pending, emitted: [] };
  },
  view: (rep) => rep.visibleWithIds(),
  displayed: (rep) => rep.visible(),
  fingerprint: (rep) => rep.string(),
  stateVector: (rep) => rep.stateVector(),
  hasPending: (rep) => rep.hasPending(),
  /** The tracked past of a new record and the version vector it was issued at must agree. */
  crossCheck(record, records) {
    const deps = new Set(record.deps);
    const notes = [];
    for (const o of records) {
      if (o === record) continue;
      const bySv = (record.svBefore[o.dot[0]] ?? 0) >= o.dot[1];
      if (bySv !== deps.has(o.key)) notes.push(`past of ${record.key}: ${o.key} svBefore=${bySv} tracked=${deps.has(o.key)}`);
    }
    return notes;
  },
  snapshot: (rep) => ({ string: rep.string() }),
  traceRecord: (o) => ({
    chars: o.chars?.map((c) => ({ id: c.id, ch: c.ch, origin: c.origin, rightOrigin: c.rightOrigin, attrs: c.attrs })),
    deleted: o.deleted,
    range: o.range ? { left: o.range.left, right: o.range.right, outerLeft: o.range.outerLeft, outerRight: o.range.outerRight } : undefined,
    styleKey: o.styleKey,
    markId: o.markId,
    knownMarks: o.chars?.[0]?.knownMarks,
    value: o.value,
    counters: o.counters,
  }),
  inserted: (o) => (o.kind === 'insert' ? o.chars.map((c) => [k2(c.id), k2(c.id) + '=' + c.ch]) : []),
  deleted: (o) => (o.kind === 'delete' ? o.deleted.map(k2) : []),
  present: (rep) => rep.visibleWithIds().map((c) => k2(c.id) + '=' + c.ch),
};

export { toB64, fromB64 };
