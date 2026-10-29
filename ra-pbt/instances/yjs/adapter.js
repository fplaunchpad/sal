/**
 * One Yjs replica: a Y.Doc with a fixed clientID, garbage collection off, and
 * a single shared text `t`.
 *
 * Identity convention: an id is a pair [client, clock]. Characters are
 * UTF-16 code units, matching Yjs's own item lengths and indices.
 *
 * Local operations return op records (see `insert`, `delete`, `format`)
 * carrying the update bytes (base64) together with the index-level request
 * and the character ids it resolved to at issue time. Every op record also
 * lists `markers` (format items the op created, with their deleted flag at
 * the end of the op) and `deletedMarkers` (previously live format items the
 * op deleted); Yjs's format, insert and delete may all remove markers. A
 * request Yjs records no update for (a format that changes nothing) is
 * rejected with a RangeError.
 *
 * `yjsAdapter` packages replicas as an ra-pbt adapter.
 */
import * as Y from 'yjs';
import { interpret, normaliseAttrs } from './spec.js';

export { Y };

const toB64 = (bytes) => Buffer.from(bytes).toString('base64');
const fromB64 = (s) => new Uint8Array(Buffer.from(s, 'base64'));
const idPair = (id) => (id ? [id.client, id.clock] : null);
const svObject = (map) => Object.fromEntries([...map.entries()].sort((x, y) => x[0] - y[0]).map(([c, k]) => [String(c), k]));

const contentKind = (item) => {
  const name = item.content?.constructor?.name;
  if (name === 'ContentString') return 'string';
  if (name === 'ContentFormat') return 'format';
  return 'other';
};

export class Replica {
  /**
   * A replica either holds its text type from the start (`loaded` absent or
   * false), as a client that creates the document does, or obtains the text
   * type only after `loadFrom` has applied an existing state, as a client
   * opening a stored or served document does. Yjs keeps different internal
   * flags on the text type in the two cases.
   */
  constructor(clientID, { loaded = false } = {}) {
    this.clientID = clientID;
    this.loaded = loaded;
    this.doc = new Y.Doc({ gc: false });
    this.doc.clientID = clientID;
    this.doc.gc = false;
    this._text = loaded ? null : this.doc.getText('t');
    this._capture = null;
    this.doc.on('update', (update, _origin, _doc, tr) => {
      if (this._capture) this._capture.push({ update, local: tr.local });
    });
  }

  get text() {
    if (this._text === null) this._text = this.doc.getText('t');
    return this._text;
  }

  /** Applies `other`'s whole state before the text type is first touched. */
  loadFrom(other) {
    if (this._text !== null) throw new Error('loadFrom must precede any use of the text type');
    Y.applyUpdate(this.doc, Y.encodeStateAsUpdate(other.doc));
    return this.text;
  }

  /** Runs fn while collecting every update the doc emits; returns { result, updates }. */
  _collect(fn) {
    const prev = this._capture;
    this._capture = [];
    try {
      const result = fn();
      return { result, updates: this._capture };
    } finally {
      this._capture = prev;
    }
  }

  _localOp(fn) {
    const { updates } = this._collect(() => this.doc.transact(fn));
    if (updates.length === 0) throw new RangeError('local operation emitted no update');
    if (updates.some((u) => !u.local)) throw new Error('local operation emitted a non-local update');
    const bytes = updates.length === 1 ? updates[0].update : Y.mergeUpdates(updates.map((u) => u.update));
    return { update: toB64(bytes), updateCount: updates.length };
  }

  /** Ids of live format markers, as "client:clock" keys. */
  _liveMarkerKeys() {
    return new Set(this.items().filter((it) => it.kind === 'format' && !it.deleted).map((it) => `${it.id[0]}:${it.id[1]}`));
  }

  /** Markers live in `beforeKeys` and deleted now, in list order. */
  _markersDeletedSince(beforeKeys) {
    return this.items()
      .filter((it) => it.kind === 'format' && it.deleted && beforeKeys.has(`${it.id[0]}:${it.id[1]}`))
      .map((it) => ({ id: it.id, key: it.key, value: it.value }));
  }

  /** Format items created by this client with clock in [from, to). */
  _ownMarkers(from, to) {
    return this.items()
      .filter((it) => it.kind === 'format' && it.id[0] === this.clientID && it.id[1] >= from && it.id[1] < to)
      .map((it) => ({ id: it.id, key: it.key, value: it.value, deleted: it.deleted }));
  }

  /**
   * Inserts `text` at visible index `index`, with optional formatting attrs.
   * chars[i].origin / rightOrigin are the origins Yjs recorded for the run,
   * resolved to characters (a marker origin stands for the nearest character
   * beyond it); for i > 0 the origin is the previous inserted character.
   * visibleOrigin / visibleRightOrigin
   * are the displayed neighbours; yOrigin / yRightOrigin are the origins
   * Yjs encoded in the update (which may name a format marker). attrs is
   * the attributes object passed; when none is passed Yjs places the text
   * without attributes of its own, and attrs is then what Yjs displays for
   * the character immediately after the operation. shown is always that
   * displayed value.
   */
  insert(index, text, attrs) {
    const before = this.visibleWithIds();
    if (index < 0 || index > before.length) throw new RangeError(`insert index ${index} outside [0, ${before.length}]`);
    const svBefore = this.stateVector();
    const clockBefore = Y.getState(this.doc.store, this.clientID);
    const left = index > 0 ? before[index - 1].id : null;
    const right = index < before.length ? before[index].id : null;
    // Yjs writes negated keys into the attributes object it is given, so it receives a copy.
    const liveMarkers = this._liveMarkerKeys();
    const op = this._localOp(() => (attrs === undefined ? this.text.insert(index, text) : this.text.insert(index, text, { ...attrs })));
    const clockAfter = Y.getState(this.doc.store, this.clientID);
    const after = this.visibleWithIds();
    const run = after.slice(index, index + text.length);
    const yOrigins = this._decodeStringOrigins(op.update);
    const retained = run.length > 0 ? this._recordedNeighbours(yOrigins.get(`${run[0].id[0]}:${run[0].id[1]}`)) : null;
    const chars = run.map((c, k) => {
      if (c.id[0] !== this.clientID || c.id[1] < clockBefore || c.id[1] >= clockAfter || c.ch !== text[k]) {
        throw new Error(`inserted character ${k} not found at visible index ${index + k}`);
      }
      const y = yOrigins.get(`${c.id[0]}:${c.id[1]}`);
      return {
        id: c.id,
        ch: c.ch,
        origin: k === 0 ? retained.left : run[k - 1].id,
        rightOrigin: retained.right,
        visibleOrigin: k === 0 ? left : run[k - 1].id,
        visibleRightOrigin: right,
        attrs: attrs === undefined ? { ...c.attrs } : { ...attrs },
        shown: c.attrs,
        yOrigin: y.origin,
        yRightOrigin: y.rightOrigin,
      };
    });
    const request = { index, text };
    if (attrs !== undefined) request.attrs = { ...attrs };
    return {
      replica: this.clientID,
      kind: 'insert',
      request,
      svBefore,
      update: op.update,
      chars,
      markers: this._ownMarkers(clockBefore, clockAfter),
      deletedMarkers: this._markersDeletedSince(liveMarkers),
    };
  }

  /**
   * The origins Yjs recorded for a run, resolved to characters: a string
   * character stands as it is, a format marker stands for the nearest string
   * character beyond it in the item list (to the left for the origin, to the
   * right for the right origin), and null stays null. Markers never move
   * relative to characters, so the resolution does not depend on when it is
   * read.
   */
  _recordedNeighbours(recorded) {
    const itemOf = (id) => {
      if (id === null) return null;
      for (let it = this.text._start; it !== null; it = it.right) {
        if (it.id.client === id[0] && it.id.clock <= id[1] && id[1] < it.id.clock + it.length) return it;
      }
      throw new Error(`origin ${id[0]}:${id[1]} not found in the item list`);
    };
    const resolve = (id, side) => {
      const item = itemOf(id);
      if (item === null) return null;
      if (item.content.constructor.name === 'ContentString') return id;
      for (let it = side === 'left' ? item.left : item.right; it !== null; it = side === 'left' ? it.left : it.right) {
        if (it.content.constructor.name === 'ContentString') {
          return side === 'left' ? [it.id.client, it.id.clock + it.length - 1] : [it.id.client, it.id.clock];
        }
      }
      return null;
    };
    return { left: resolve(recorded.origin, 'left'), right: resolve(recorded.rightOrigin, 'right') };
  }

  /** Map "client:clock" -> { origin, rightOrigin } for every string character in an update. */
  _decodeStringOrigins(updateB64) {
    const { structs } = Y.decodeUpdate(fromB64(updateB64));
    const out = new Map();
    for (const s of structs) {
      if (!(s instanceof Y.Item) || s.content.constructor.name !== 'ContentString') continue;
      for (let k = 0; k < s.length; k++) {
        out.set(`${s.id.client}:${s.id.clock + k}`, {
          origin: k === 0 ? idPair(s.origin) : [s.id.client, s.id.clock + k - 1],
          rightOrigin: idPair(s.rightOrigin),
        });
      }
    }
    return out;
  }

  /** Deletes `len` visible characters starting at `index`. */
  delete(index, len) {
    const before = this.visibleWithIds();
    if (index < 0 || len < 0 || index + len > before.length) throw new RangeError(`delete [${index}, ${index + len}) outside [0, ${before.length}]`);
    const svBefore = this.stateVector();
    const deleted = before.slice(index, index + len).map((c) => c.id);
    const liveMarkers = this._liveMarkerKeys();
    const op = this._localOp(() => this.text.delete(index, len));
    return {
      replica: this.clientID,
      kind: 'delete',
      request: { index, len },
      svBefore,
      update: op.update,
      deleted,
      deletedMarkers: this._markersDeletedSince(liveMarkers),
    };
  }

  /** Applies formatting attrs to the visible range [index, index + len). */
  format(index, len, attrs) {
    const before = this.visibleWithIds();
    if (index < 0 || len < 1 || index + len > before.length) throw new RangeError(`format [${index}, ${index + len}) outside [0, ${before.length}]`);
    const svBefore = this.stateVector();
    const clockBefore = Y.getState(this.doc.store, this.clientID);
    const covered = before.slice(index, index + len).map((c) => c.id);
    const liveMarkers = this._liveMarkerKeys();
    const op = this._localOp(() => this.text.format(index, len, { ...attrs }));
    const clockAfter = Y.getState(this.doc.store, this.clientID);
    return {
      replica: this.clientID,
      kind: 'format',
      request: { index, len, attrs: { ...attrs } },
      svBefore,
      update: op.update,
      range: { left: covered[0], right: covered[covered.length - 1], covered },
      markers: this._ownMarkers(clockBefore, clockAfter),
      deletedMarkers: this._markersDeletedSince(liveMarkers),
    };
  }

  /**
   * Applies a remote op record. `emitted` lists any local updates Yjs
   * produced while integrating it (its formatting cleanup deletes redundant
   * markers in a follow-up local transaction), base64 encoded.
   */
  deliver(opRecord) {
    const { updates } = this._collect(() => Y.applyUpdate(this.doc, fromB64(opRecord.update), 'remote'));
    return { pending: this.hasPending(), emitted: updates.filter((u) => u.local).map((u) => toB64(u.update)) };
  }

  /** Brings this replica up to date with `other`; same result shape as deliver. */
  syncFrom(other) {
    const bytes = Y.encodeStateAsUpdate(other.doc, Y.encodeStateVector(this.doc));
    const { updates } = this._collect(() => Y.applyUpdate(this.doc, bytes, 'remote'));
    return { pending: this.hasPending(), emitted: updates.filter((u) => u.local).map((u) => toB64(u.update)) };
  }

  /** State vector as a plain object { client: clock } with string keys. */
  stateVector() {
    return svObject(Y.decodeStateVector(Y.encodeStateVector(this.doc)));
  }

  hasPending() {
    return this.doc.store.pendingStructs !== null || this.doc.store.pendingDs !== null;
  }

  /** Displayed characters with attributes, from Yjs's own toDelta rendering. */
  visible() {
    const out = [];
    for (const d of this.text.toDelta()) {
      if (typeof d.insert !== 'string') throw new Error('non-string content in delta');
      const attrs = d.attributes ?? {};
      for (let k = 0; k < d.insert.length; k++) out.push({ ch: d.insert[k], attrs: { ...attrs } });
    }
    return out;
  }

  /** visible() with each character's id, from a walk of the item list. */
  visibleWithIds() {
    const ids = [];
    for (let it = this.text._start; it !== null; it = it.right) {
      if (it.deleted || contentKind(it) !== 'string') continue;
      const str = it.content.str;
      for (let k = 0; k < it.length; k++) ids.push({ id: [it.id.client, it.id.clock + k], ch: str[k] });
    }
    const vis = this.visible();
    if (vis.length !== ids.length) throw new Error(`walk found ${ids.length} characters, delta ${vis.length}`);
    return vis.map((v, i) => {
      if (v.ch !== ids[i].ch) throw new Error(`character mismatch at ${i}: walk ${ids[i].ch}, delta ${v.ch}`);
      return { id: ids[i].id, ch: v.ch, attrs: v.attrs };
    });
  }

  /** Full internal item list, including tombstones and format markers. */
  items() {
    const out = [];
    for (let it = this.text._start; it !== null; it = it.right) {
      const kind = contentKind(it);
      const e = { id: [it.id.client, it.id.clock], len: it.length, kind };
      if (kind === 'string') e.str = it.content.str;
      if (kind === 'format') {
        e.key = it.content.key;
        e.value = it.content.value;
      }
      e.deleted = it.deleted;
      e.origin = idPair(it.origin);
      e.rightOrigin = idPair(it.rightOrigin);
      out.push(e);
    }
    return out;
  }

  string() {
    return this.text.toString();
  }

  snapshot() {
    return { visible: this.visible(), items: this.items(), pending: this.hasPending(), sv: this.stateVector() };
  }
}



/** Clock ranges and deleted ids carried by an op record's update. */
export function effectOf(record) {
  const bytes = fromB64(record.update);
  const meta = Y.parseUpdateMeta(bytes);
  const structs = [];
  for (const [client, to] of meta.to) {
    const from = meta.from.get(client);
    if (to > from) structs.push({ client, from, to });
  }
  const { ds } = Y.decodeUpdate(bytes);
  const deletes = [];
  for (const [client, items] of ds.clients) for (const d of items) deletes.push({ client, clock: d.clock, len: d.len });
  return { structs, deletes };
}

/** Set of 'client:clock' for every deleted item unit at a replica. */
export function deletedUnits(replica) {
  const out = new Set();
  for (const it of replica.items()) {
    if (!it.deleted) continue;
    for (let k = 0; k < it.len; k++) out.add(it.id[0] + ':' + (it.id[1] + k));
  }
  return out;
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
  } else if (request.kind === 'delete' || request.kind === 'format') {
    if (!nat(request.index) || !nat(request.len) || request.len < 1 || request.index + request.len > length)
      throw new RangeError(`${request.kind} [${request.index}, ${request.index + request.len}) outside [0, ${length}]`);
  } else throw new RangeError('unknown edit kind ' + request.kind);
}

/** The index-level request of an edit step, in `localEdit` form (insert attrs default to {}). */
export function requestOf(step) {
  if (step.kind === 'insert') return { kind: 'insert', index: step.index, text: step.text, attrs: step.attrs ?? {} };
  if (step.kind === 'delete') return { kind: 'delete', index: step.index, len: step.len };
  return { kind: 'format', index: step.index, len: step.len, attrs: step.attrs };
}

/** Issues a request on a replica; returns the op record Replica produces. */
function issueOn(rep, request) {
  if (request.kind === 'insert') return rep.insert(request.index, request.text, request.attrs ?? {});
  if (request.kind === 'delete') return rep.delete(request.index, request.len);
  if (request.kind === 'format') return rep.format(request.index, request.len, request.attrs);
  throw new RangeError('unknown edit kind ' + request.kind);
}

/** A cleanup record for an update a replica emitted while integrating a remote one. */
function cleanupRecord(rep, update) {
  const rec = { replica: rep.clientID, kind: 'cleanup', request: {}, svBefore: rep.stateVector(), update, specOps: [] };
  rec.effect = effectOf(rec);
  return rec;
}

const k2 = (id) => id[0] + ':' + id[1];

/**
 * The ra-pbt adapter for Y.Text.
 *
 * Records are Replica op records extended with `specOps` (from `interpret`)
 * and `effect` (the clock ranges the update creates and the units it
 * deletes). A record is integrated at a replica when every struct it
 * created is covered by the replica's state vector and every unit its update
 * deletes is deleted there; it is partly integrated when some but not all
 * of that effect is present. Delete effects are attributed only to records
 * the replica has received, so two concurrent deletes of one character are
 * not confused. The view carries character identities for the classifier; the
 * witness search compares views without them. The displayed value is Yjs's own `toDelta`
 * rendering.
 */
export const yjsAdapter = {
  createReplica: (id, { opened = false } = {}) => new Replica(id, { loaded: opened }),
  loadInto: (rep, source) => rep.loadFrom(source),
  requestOf,
  validRequest(rep, request) {
    validateEdit(request, rep.visible().length);
    return true;
  },
  issue(rep, request) {
    const record = issueOn(rep, request);
    record.specOps = interpret(record);
    record.effect = effectOf(record);
    return record;
  },
  deliver(rep, record) {
    const res = rep.deliver(record);
    return { pending: res.pending, emitted: res.emitted.map((u) => cleanupRecord(rep, u)) };
  },
  sync(to, from) {
    const res = to.syncFrom(from);
    return { pending: res.pending, emitted: res.emitted.map((u) => cleanupRecord(to, u)) };
  },
  view: (rep) => rep.visibleWithIds().map((c) => ({ id: c.id, ch: c.ch, attrs: normaliseAttrs(c.attrs) })),
  displayed: (rep) => rep.visible(),
  fingerprint: (rep) => rep.string(),
  stateVector: (rep) => rep.stateVector(),
  hasPending: (rep) => rep.hasPending(),
  integrated(rep, records) {
    const sv = rep.stateVector();
    const dead = deletedUnits(rep);
    const integrated = new Set();
    const partial = [];
    for (const op of records) {
      let all = true;
      let some = false;
      for (const s of op.effect.structs) {
        const have = sv[String(s.client)] ?? 0;
        if (have >= s.to) some = true;
        else {
          all = false;
          if (have > s.from) some = true;
        }
      }
      for (const d of op.effect.deletes) {
        for (let k = 0; k < d.len; k++) {
          if (dead.has(d.client + ':' + (d.clock + k))) some = true;
          else all = false;
        }
      }
      if (all) integrated.add(op.key);
      else if (some) partial.push(op.key);
    }
    return { integrated, partial };
  },
  /** For records that create structs, the svBefore rule and the tracked past must agree. */
  crossCheck(record, records) {
    const deps = new Set(record.deps);
    const notes = [];
    for (const o of records) {
      if (o.effect.structs.length === 0) continue;
      const bySv = o.effect.structs.every((s) => (record.svBefore[String(s.client)] ?? 0) >= s.to);
      if (bySv !== deps.has(o.key)) notes.push(`past of ${record.key}: ${o.key} svBefore=${bySv} tracked=${deps.has(o.key)}`);
    }
    return notes;
  },
  snapshot: (rep) => ({ string: rep.string() }),
  traceRecord: (o) => ({
    chars: o.chars?.map((c) => ({ id: c.id, ch: c.ch, origin: c.origin, attrs: c.attrs })),
    deleted: o.deleted,
    range: o.range ? { left: o.range.left, right: o.range.right } : undefined,
    markers: o.markers,
    deletedMarkers: o.deletedMarkers,
  }),
  inserted: (o) => (o.kind === 'insert' ? o.chars.map((c) => [k2(c.id), k2(c.id) + '=' + c.ch]) : []),
  deleted: (o) => (o.kind === 'delete' ? o.deleted.map(k2) : []),
  present: (rep) => rep.visibleWithIds().map((c) => k2(c.id) + '=' + c.ch),
};
