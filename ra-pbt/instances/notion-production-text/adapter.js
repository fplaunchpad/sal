/**
 * Replicas of the production Notion editing code, at the text layer of one
 * block.
 *
 * The library is the standalone export of
 * `experiments/notion-production-client/extract.mjs`, which lives outside
 * the repository at the path in `NOTION_PRODUCTION_LIBRARY` (see
 * `library.js`). A replica wraps one `createClient(session)` of that export
 * and one block. A created replica builds the block record itself with the
 * shipped empty-tree constructor (`createBlock`); every created replica holds
 * the same empty record, since the text instance id is derived from the block
 * id. An opened replica is `createClient(session, snapshot)` from another
 * replica's `snapshot()`.
 *
 * Identities are read from the operations the shipped builders emit:
 *   insertText   `id: [session, counter]` names the first character, the
 *                k-th has [session, counter + k]; `originId` is the origin of
 *                the first ('start' for the head), each later character's
 *                origin is the character before it. The visible right
 *                neighbour at issue time is recorded as `rightOrigin`, since
 *                the operation carries none.
 *   deleteText   `idRanges: [[id, length]]`, expanded to character ids and
 *                checked against the characters selected on the display.
 *   add/removeAnnotation  `id`, and `start`, `end` as { id, anchor }.
 * Visible characters and their ids are read by walking the shipped text
 * slice's item list (`iterateItems`), checked against the shipped `text()`
 * and rich-text serialisation.
 *
 * Bold requests are toggles, as in the positional specification: remove when
 * every selected character is bold on the issuer's display, add otherwise.
 *
 * Delivery. The client applies an operation once and does not buffer one
 * whose causal predecessors are missing (a delete then names absent
 * characters and changes nothing; an annotation with an absent anchor
 * throws). The adapter is the transport: a record is applied at most once,
 * and only after every record in its causal past (`deps`), so every
 * schedule, `send` steps included, is delivered causally. The probe in
 * `experiments/notion-production-text/out-of-order.mjs` removes this buffer.
 */
import { interpret, idKey } from './spec.js';
import { library } from './library.js';

/** The block every replica edits. */
export const BLOCK = { table: 'block', id: '00000000-0000-4000-8000-0000000000b1', spaceId: '00000000-0000-4000-8000-000000000100' };

export const sessionOf = (id) => `s${id}`;

const sameId = (a, b) => (typeof a === 'string' || typeof b === 'string' ? a === b : a[0] === b[0] && a[1] === b[1]);

/** The item list of a client's block, from the shipped text slices: [{ kind, id, len, deleted, content, before, after }]. */
export function items(client, pointer = BLOCK) {
  const out = [];
  for (const tree of client.tree(pointer).iterateTextSliceTrees()) {
    for (const it of tree.getTextSlice().iterateItems({ includeDeleted: true, includeEndItem: true })) {
      const sets = {};
      for (const side of ['before', 'after']) {
        const s = it.getAnnotationOpSetForAnchor(side);
        if (s) sets[side] = s.getOps().map((o) => ({ id: o.id, type: o.type }));
      }
      const e = { kind: it.className, id: it.id };
      if (it.className === 'TextItem') Object.assign(e, { len: it.getLength(), deleted: it.isDeleted(), originId: it.originId, content: it.isDeleted() ? undefined : it.getDefinedContent() });
      Object.assign(e, sets);
      out.push(e);
    }
  }
  return out;
}

/** Visible characters [{ id, ch, bold }]: ids from the item walk, bold from the shipped rich-text value. */
export function visibleWithIds(client, pointer = BLOCK) {
  const ids = [];
  for (const it of items(client, pointer))
    if (it.kind === 'TextItem' && !it.deleted) for (let k = 0; k < it.len; k++) ids.push({ id: [it.id[0], it.id[1] + k], ch: it.content[k] });
  const shown = displayedOf(client, pointer);
  if (shown.length !== ids.length) throw new Error(`item walk found ${ids.length} characters, rich text ${shown.length}`);
  return shown.map((c, i) => {
    if (c.ch !== ids[i].ch) throw new Error(`character mismatch at ${i}: walk ${ids[i].ch}, rich text ${c.ch}`);
    return { id: ids[i].id, ch: c.ch, bold: c.bold };
  });
}

/** Displayed characters [{ ch, bold }] from the shipped rich-text value; checked against `text()`. */
export function displayedOf(client, pointer = BLOCK) {
  const out = [];
  for (const [text, annotations] of client.rich(pointer)) {
    const bold = (annotations ?? []).some((a) => a[0] === 'b');
    for (const ch of text) out.push({ ch, bold });
  }
  const text = client.text(pointer);
  if (out.map((c) => c.ch).join('') !== text) throw new Error('rich text and text() disagree');
  return out;
}

export class Replica {
  constructor(id, { opened = false } = {}) {
    this.id = id;
    this.session = sessionOf(id);
    this.opened = opened;
    this.client = null;
    this.log = [];
    this.pending = [];
    if (!opened) {
      this.client = library().createClient(this.session);
      this.client.createBlock(BLOCK);
    }
  }

  /** Constructs the client from `source`'s snapshot; the transport state travels with it. */
  loadFrom(source) {
    if (this.client) throw new Error('loadFrom must precede any use of an opened replica');
    this.client = library().createClient(this.session, source.client.snapshot());
    this.log = [...source.log];
    this.pending = [...source.pending];
  }

  visible() {
    return visibleWithIds(this.client);
  }

  displayed() {
    return displayedOf(this.client);
  }

  /** Keys of the records applied here, own records included (the executor keys a record after issue). */
  get applied() {
    return new Set(this.log.map((r) => r.key));
  }

  /** Applies a received record once, after its causal past; drains the buffer. */
  receive(record) {
    if (this.log.includes(record) || this.pending.includes(record)) return;
    this.pending.push(record);
    let progress = true;
    while (progress) {
      progress = false;
      for (const r of [...this.pending]) {
        const applied = this.applied;
        if (!(r.deps ?? []).every((d) => applied.has(d))) continue;
        this.pending = this.pending.filter((p) => p !== r);
        this.client.apply(r.update);
        this.log.push(r);
        progress = true;
      }
    }
  }

  /** Issues a request; returns the record (without key and deps, which the executor assigns). */
  issue(request) {
    const before = this.visible();
    validateRequest(request, before.length);
    const c = this.client;
    let ops;
    const record = { replica: this.id, kind: request.kind, request: { ...request } };
    if (request.kind === 'insert') {
      ops = c.prepareInsert(BLOCK, request.index, request.text).map((o) => JSON.parse(JSON.stringify(o)));
      if (ops.length !== 1 || ops[0].command !== 'insertText') throw new Error('insert prepared ' + ops.map((o) => o.command).join(','));
      const args = ops[0].args;
      if (args.content !== request.text) throw new Error('insert content differs from the request');
      c.apply(ops);
      const after = this.visible();
      const first = args.originId === 'start' ? null : args.originId;
      const rightOrigin = request.index < before.length ? before[request.index].id : null;
      record.chars = [...request.text].map((ch, k) => {
        const id = [args.id[0], args.id[1] + k];
        const shown = after[request.index + k];
        if (!shown || !sameId(shown.id, id) || shown.ch !== ch) throw new Error(`inserted character ${k} not found at visible index ${request.index + k}`);
        return { id, ch, origin: k === 0 ? first : [args.id[0], args.id[1] + k - 1], rightOrigin, bold: shown.bold, visibleOrigin: k === 0 ? (request.index > 0 ? before[request.index - 1].id : null) : [args.id[0], args.id[1] + k - 1] };
      });
    } else if (request.kind === 'delete') {
      ops = c.prepareDelete(BLOCK, request.start, request.end).map((o) => JSON.parse(JSON.stringify(o)));
      const ids = [];
      for (const o of ops) {
        if (o.command !== 'deleteText') throw new Error('delete prepared ' + o.command);
        for (const [id, len] of o.args.idRanges) for (let k = 0; k < len; k++) ids.push([id[0], id[1] + k]);
      }
      const selected = before.slice(request.start, request.end).map((x) => x.id);
      const key = (xs) => xs.map(idKey).sort().join(',');
      if (key(ids) !== key(selected)) throw new Error('deleteText names characters other than the selected ones');
      c.apply(ops);
      record.deletedIds = selected;
    } else {
      const selected = before.slice(request.start, request.end);
      const add = !selected.every((x) => x.bold);
      ops = c.prepareBold(BLOCK, request.start, request.end, add).map((o) => JSON.parse(JSON.stringify(o)));
      if (ops.length !== 1) throw new Error(`bold prepared ${ops.length} operations`);
      const args = ops[0].args;
      const expected = add ? 'addAnnotation' : 'removeAnnotation';
      if (ops[0].command !== expected) throw new Error(`bold prepared ${ops[0].command}, expected ${expected}`);
      if (add ? JSON.stringify(args.annotation) !== '["b"]' : args.annotationKey !== 'b') throw new Error('bold prepared another annotation');
      c.apply(ops);
      record.annotation = { id: args.id, start: args.start, end: args.end, value: add ? true : null, left: selected[0].id, right: selected[selected.length - 1].id };
      record.add = add;
    }
    record.update = JSON.parse(JSON.stringify(ops));
    record.specOps = interpret(record);
    this.log.push(record);
    return record;
  }
}

/** Throws a RangeError for a request out of range on a display of `length` characters. */
export function validateRequest(request, length) {
  const nat = (x) => Number.isInteger(x) && x >= 0;
  if (request.kind === 'insert') {
    if (!nat(request.index) || request.index > length) throw new RangeError(`insert index ${request.index} outside [0, ${length}]`);
    if (typeof request.text !== 'string' || request.text.length === 0 || !/^[a-z]+$/.test(request.text)) throw new RangeError('insert text must be nonempty lowercase ASCII');
  } else if (request.kind === 'delete' || request.kind === 'bold') {
    if (!nat(request.start) || !nat(request.end) || request.start >= request.end || request.end > length)
      throw new RangeError(`${request.kind} [${request.start}, ${request.end}) outside [0, ${length}]`);
  } else throw new RangeError('unknown request kind ' + request.kind);
}

/** The request of an edit step. */
export function requestOf(step) {
  if (step.kind === 'insert') return { kind: 'insert', index: step.index, text: step.text };
  return { kind: step.kind, start: step.start, end: step.end };
}

/** Character ids an annotation's anchors and its selection name. */
function annotationIds(a) {
  return [a.start.id, a.end.id, a.left, a.right].filter((x) => Array.isArray(x));
}

/**
 * The ra-pbt adapter. The view carries ids, so the gap rule's witness search
 * is directed by it; the displayed value is the shipped rich-text value.
 */
export const notionTextAdapter = {
  createReplica: (id, { opened = false } = {}) => new Replica(id, { opened }),
  loadInto: (rep, source) => rep.loadFrom(source),
  requestOf,
  validRequest(rep, request) {
    validateRequest(request, rep.displayed().length);
    return true;
  },
  issue: (rep, request) => rep.issue(request),
  deliver(rep, record) {
    rep.receive(record);
    return { pending: rep.pending.length > 0, emitted: [] };
  },
  sync(to, from) {
    for (const r of [...from.log, ...from.pending]) to.receive(r);
    return { pending: to.pending.length > 0, emitted: [] };
  },
  view: (rep) => rep.visible(),
  displayed: (rep) => rep.displayed(),
  fingerprint: (rep) => rep.client.text(BLOCK),
  stateVector: (rep) => ({ applied: [...rep.applied].sort() }),
  hasPending: (rep) => rep.pending.length > 0,
  integrated(rep, records) {
    return new Set(records.filter((r) => rep.log.includes(r)).map((r) => r.key));
  },
  /**
   * Identity checks on a new record: its ids exceed every id in its causal
   * past (the counter is a Lamport clock), and every character id it names
   * was inserted by a record in its causal past.
   */
  crossCheck(record, records) {
    const deps = new Set(record.deps);
    const notes = [];
    const own = record.kind === 'insert' ? record.chars.map((c) => c.id) : record.kind === 'bold' ? [record.annotation.id] : [];
    const minOwn = Math.min(...own.map((x) => x[1]));
    const past = new Map();
    for (const o of records) {
      if (!deps.has(o.key)) continue;
      const theirs = o.kind === 'insert' ? o.chars.map((c) => c.id) : o.kind === 'bold' ? [o.annotation.id] : [];
      for (const x of theirs) {
        past.set(idKey(x), o.key);
        if (own.length && x[1] >= minOwn) notes.push(`${record.key} counter ${minOwn} does not exceed ${o.key}'s ${x[1]}`);
      }
    }
    const named = record.kind === 'insert' ? record.chars.flatMap((c) => [c.origin, c.rightOrigin]).filter((x) => x && !own.some((y) => sameId(x, y))) : record.kind === 'delete' ? record.deletedIds : record.kind === 'bold' ? annotationIds(record.annotation) : [];
    for (const x of named) if (!past.has(idKey(x))) notes.push(`${record.key} names ${idKey(x)}, which no record in its past inserted`);
    return notes;
  },
  snapshot: (rep) => ({ text: rep.client.text(BLOCK) }),
  traceRecord: (o) => ({
    chars: o.chars?.map((c) => ({ id: c.id, ch: c.ch, origin: c.origin, rightOrigin: c.rightOrigin, bold: c.bold })),
    deletedIds: o.deletedIds,
    annotation: o.annotation,
  }),
  inserted: (o) => (o.kind === 'insert' ? o.chars.map((c) => [idKey(c.id), idKey(c.id) + '=' + c.ch]) : []),
  deleted: (o) => (o.kind === 'delete' ? o.deletedIds.map(idKey) : []),
  present: (rep) => rep.visible().map((c) => idKey(c.id) + '=' + c.ch),
};
