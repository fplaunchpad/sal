/**
 * ra-pbt adapter over clients of the exported production Notion library.
 *
 * Document. One page block whose `content` lists the blocks, as in the
 * production client's ReplayReplica: a block is a record created with the
 * shipped empty-tree constructor (`createBlock`), sent as a `set` of its
 * value with `parent_id` the page, and listed by `listAfter` on the page's
 * content. The displayed document is the page's content filtered by each
 * block's `alive` flag; a block's characters are read from its slice tree
 * by the shipped iterators, its text and bold flags by the shipped readers.
 *
 * Requests. Every valid request is one record: the production operations it
 * emitted, applied locally by the shipped record handlers (module 971340).
 *   create  `set` + `listAfter` (the fixture block creation of ReplayReplica);
 *   insert  `prepareInsert` (the shipped insertion builder);
 *   split   creation of the new block after the source, then the original
 *           split request builder (`RequestBuilder.split`, module 701590);
 *   merge   the original merge request builder (`RequestBuilder.merge`),
 *           then `set alive false` on the source and `listRemove` from the
 *           page's content (the harness's removal, as in ReplayReplica);
 *   bold    `prepareBold` with an explicit add/remove: add unless every
 *           selected character is bold.
 * A request the production code throws on is rejected (a RangeError, the
 * step is dropped) and counted in `adapterStats`.
 *
 * Delivery. A record carries its operations and the keys of every record
 * its issuer held (its causal past). `deliver` holds a record until its past
 * is present, then applies its operations once; `sync(to, from)` offers `to`
 * every record `from` holds, in `from`'s order, and the records `from`
 * holds back. A record is integrated when applied. An apply that throws is
 * restored from the snapshot before it, counted, and leaves the replica
 * pending (the record is never integrated).
 *
 * Clients. `clientFactory(lib)` returns clients that share one runtime
 * (one VM context and one instance of each extracted module): the body of
 * the library's `ProductionClient` constructor with the runtime created
 * once per loaded library. `clientFactory(lib, { isolated: true })` is the library's own
 * `createClient`, one runtime per client, which is too costly for searches;
 * the regressions check that both give identical traces.
 *
 * Replicas. Replica r has session `sessions[r - 1]` (default A, B, ...); a
 * determinism fork (id 1000 + r) has session `F<id>`. All start from the
 * seed snapshot. An opened replica is a client constructed from the
 * source's `RecordMap` snapshot, holding the source's records.
 *
 * Specification operations. One per record: `{ key, commands }`, the
 * decoded command group (decode.js), with the bold command of the issuer's
 * selection for a bold request and the inherited flag for an insertion.
 *
 * Element accounting. Characters are keyed by `instance/session:counter`
 * and labelled `text@key`. The seed's characters are reported as inserted
 * by every record; nothing is deleted at the block layer.
 */
import { createHash } from 'node:crypto';
import { decodeOps, insertedCharacters, siblingMoves } from './decode.js';
import { blocksOf } from './spec.js';
import { validOn } from './requests.js';

export const DEFAULT_SESSIONS = ['A', 'B', 'C', 'D', 'E', 'F'];
export const adapterStats = { rejected: 0, rejections: [], applyFailures: 0, applyFailureMessages: [] };

export const uuid = (label) => {
  const h = createHash('sha256').update(label).digest('hex');
  return `${h.slice(0, 8)}-${h.slice(8, 12)}-4${h.slice(13, 16)}-8${h.slice(17, 20)}-${h.slice(20, 32)}`;
};
export const SPACE_ID = uuid('production-blocks-space');
export const PAGE = { table: 'block', id: uuid('production-blocks-page'), spaceId: SPACE_ID };
export const pointer = (id) => ({ table: 'block', id, spaceId: SPACE_ID });

const copy = (v) => JSON.parse(JSON.stringify(v));

/**
 * Live clocks. The library's `ProductionClient.tree` reads a block through
 * the record model (module 500183), which parses the slice tree with one
 * plain clock per tree (508649). The editor's record store (970831), whose
 * trees the request builders receive in the application, parses with clock
 * holders of class `997076.W`, backed by a map from text instance to the
 * largest counter the process has seen or reserved. Without that map, two
 * splits by one session in different blocks of one text instance allocate
 * the same marker identifier. `liveTrees(c, overrides)` replaces the
 * client's `tree` by the record store's parse (266858 with `997076.W`
 * holders) and gives the client its own map, as each client process has.
 * The map is installed on the class before each parse; every use of a tree
 * follows its parse on the same client.
 */
export function liveTrees(c, overrides = new Map()) {
  const W = c.runtime.require('997076').W;
  const parse = c.runtime.require('266858').r;
  c.clockOverrides = overrides;
  c.tree = function tree(p) {
    const title = this.recordMap.getValue(p)?.crdt_data?.title;
    if (!title) throw new Error(`Unknown block ${p.id}`);
    W.overrides = overrides;
    return parse(title, ({ value, textInstanceId }) => new W(value, textInstanceId), this.session);
  };
  return c;
}

/**
 * A client constructor `(session, snapshot, overrides?) => client` over
 * `lib`, with live clocks unless `liveClock` is false (the library's own
 * record-model trees).
 */
const runtimes = new WeakMap();

export function clientFactory(lib, { isolated = false, liveClock = true } = {}) {
  let make;
  if (isolated) make = (session, snapshot) => lib.createClient(session, snapshot);
  else {
    if (!runtimes.has(lib)) runtimes.set(lib, lib.createClient('runtime'));
    const base = runtimes.get(lib);
    const proto = Object.getPrototypeOf(base);
    const { RecordMap } = base.runtime.require('412951');
    make = (session, snapshot) => {
      const c = Object.create(proto);
      c.runtime = base.runtime;
      c.session = session;
      c.recordMap = RecordMap.create(snapshot && copy(snapshot));
      return c;
    };
  }
  return liveClock ? (session, snapshot, overrides) => liveTrees(make(session, snapshot), overrides) : make;
}

/** The fixture creation of block `id` on client `c`, after `after`: applied, and returned as operations. */
export function createOps(c, id, after) {
  const p = pointer(id);
  c.createBlock(p);
  const value = { ...c.value(p), parent_table: 'block', parent_id: PAGE.id };
  const ops = [
    { command: 'set', pointer: p, path: [], args: value },
    { command: 'listAfter', pointer: PAGE, path: ['content'], args: { id, ...(after ? { after } : {}) } },
  ];
  c.apply(ops);
  return ops;
}

/** Visible characters of a block from the shipped slice-tree iterators: [{ text, bold, key }]. */
export function charactersOf(c, id) {
  const p = pointer(id);
  const out = [];
  for (const tree of c.tree(p).iterateTextSliceTrees()) {
    const slice = tree.getTextSlice();
    for (const item of slice.iterateItems()) {
      if (typeof item.content !== 'string' || item.deleted) continue;
      [...item.content].forEach((text, k) => out.push({ text, key: `${slice.textInstanceId}/${item.id[0]}:${item.id[1] + k}` }));
    }
  }
  const text = c.text(p);
  if (out.map((x) => x.text).join('') !== text) throw new Error(`slice iteration disagrees with getText on ${id}: ${JSON.stringify(out.map((x) => x.text).join(''))} vs ${JSON.stringify(text)}`);
  const bold = c.rich(p).flatMap(([t, annotations = []]) => [...t].map(() => annotations.some((x) => x[0] === 'b')));
  out.forEach((x, i) => (x.bold = bold[i]));
  return out;
}

/** Item keys of a serialised slice's items: start, end, markers, and every character of a run. */
function sliceItemKeys(items) {
  const out = [];
  for (const it of items) {
    if (it.t === 's') out.push('start');
    else if (it.t === 'e') out.push('end');
    else if (it.t === 't') for (let k = 0; k < (it.l ?? 1); k++) out.push(`${it.i[0]}:${it.i[1] + k}`);
    else if (it.i) out.push(`${it.i[0]}:${it.i[1]}`);
  }
  return out;
}

/**
 * The whole document state of a client, for classification: every block
 * record (alive or not) with its visible character keys, the page's
 * content, the label of every slice (`instance/start` -> label), and every
 * slice with its instance, label, holding block and item keys, read from
 * the serialised record values.
 */
export function stateOf(c) {
  const snap = c.snapshot();
  const blocks = {};
  const labels = {};
  const slices = [];
  for (const [id, rec] of Object.entries(snap.block ?? {})) {
    if (id === PAGE.id) continue;
    const v = rec.value;
    blocks[id] = { alive: !!v.alive, chars: charactersOf(c, id).map((x) => x.key) };
    for (const node of Object.values(v.crdt_data?.title?.n ?? {})) {
      const keys = sliceItemKeys(node.s.i);
      labels[`${node.s.x}/${keys[0]}`] = node.s.l;
      slices.push({ instance: node.s.x, label: node.s.l, block: id, items: keys });
    }
  }
  return { blocks, labels, slices, content: [...contentOf(c)] };
}

/** The page's content ids, alive or not, in order. */
export const contentOf = (c) => c.value(PAGE)?.content ?? [];

/** The displayed view: alive listed blocks with characters. */
export function viewOf(c) {
  return contentOf(c)
    .filter((id) => c.value(pointer(id))?.alive)
    .map((id) => ({ id, chars: charactersOf(c, id) }));
}

function insertedOf(ops) {
  return ops.filter((o) => o.command === 'insertText').flatMap((o) => insertedCharacters(o.args).map((x) => [`${o.args.textInstanceId}/${x.id}`, `${x.text}@${o.args.textInstanceId}/${x.id}`]));
}

/** The seed document: a page with blocks of the given texts, issued by session `seed`. */
export function seedDocument(lib, texts, newClient = clientFactory(lib)) {
  const c = newClient('seed');
  c.createBlock(PAGE);
  c.apply([
    { command: 'set', pointer: PAGE, path: ['type'], args: 'page' },
    { command: 'set', pointer: PAGE, path: ['content'], args: [] },
  ]);
  const records = [];
  let previous;
  texts.forEach((t, n) => {
    const id = uuid(`seed:block:${n + 1}`);
    const ops = createOps(c, id, previous);
    if (t) {
      const ins = c.prepareInsert(pointer(id), 0, t);
      c.apply(ins);
      ops.push(...ins);
    }
    records.push(ops);
    previous = id;
  });
  return { snapshot: c.snapshot(), groups: records.map((ops) => decodeOps(ops, { pageId: PAGE.id })), inserted: records.flatMap(insertedOf), texts };
}

/** Issues a positional request on replica x; returns { ops, commands }. Throws RangeError on rejection. */
export function issueOn(lib, x, q, newClient) {
  const view = viewOf(x.client);
  if (!validOn(view, q)) throw new RangeError(`invalid request ${JSON.stringify(q)}`);
  const before = x.client.snapshot();
  const counter = x.counter;
  const c = x.client;
  const ops = [];
  let extra = null;
  let insertBold = false;
  try {
    if (q.kind === 'create') ops.push(...createOps(c, uuid(`${x.session}:block:${++x.counter}`), q.after >= 0 ? view[q.after].id : undefined));
    else {
      const id = view[q.block].id;
      if (q.kind === 'insert') {
        insertBold = q.index > 0 && view[q.block].chars[q.index - 1].bold;
        const ins = c.prepareInsert(pointer(id), q.index, q.text);
        c.apply(ins);
        ops.push(...ins);
      } else if (q.kind === 'split') {
        const target = uuid(`${x.session}:block:${++x.counter}`);
        ops.push(...createOps(c, target, id));
        const builder = new lib.RequestBuilder(c);
        try {
          builder.split(pointer(id), pointer(target), q.index);
        } finally {
          ops.push(...builder.operations);
        }
      } else if (q.kind === 'merge') {
        const builder = new lib.RequestBuilder(c);
        try {
          builder.merge(pointer(id), pointer(view[q.block - 1].id));
        } finally {
          ops.push(...builder.operations);
        }
        const removal = [
          { command: 'set', pointer: pointer(id), path: ['alive'], args: false },
          { command: 'listRemove', pointer: PAGE, path: ['content'], args: { id } },
        ];
        c.apply(removal);
        ops.push(...removal);
      } else if (q.kind === 'bold') {
        const selected = view[q.block].chars.slice(q.start, q.end);
        const add = !selected.every((ch) => ch.bold);
        const marks = c.prepareBold(pointer(id), q.start, q.end, add);
        c.apply(marks);
        ops.push(...marks);
        extra = { kind: 'bold', addresses: selected.map((ch) => ch.key), value: add };
      }
    }
  } catch (e) {
    x.client = newClient(x.session, before, x.client.clockOverrides);
    x.counter = counter;
    if (e instanceof RangeError) throw e;
    adapterStats.rejected++;
    if (adapterStats.rejections.length < 20) adapterStats.rejections.push({ request: q, message: e.message });
    throw new RangeError(`the production code rejected ${JSON.stringify(q)}: ${e.message}`);
  }
  const commands = decodeOps(ops, { pageId: PAGE.id, insertBold });
  if (extra) commands.push(extra);
  return { ops: copy(ops), commands };
}

export function makeAdapter(lib, { seed, sessions = DEFAULT_SESSIONS, newClient = clientFactory(lib), observe = null }) {
  const sessionOf = (id) => (id >= 1000 ? `F${id}` : sessions[id - 1] ?? `R${id}`);
  const fresh = (id) => ({ id, session: sessionOf(id), client: newClient(sessionOf(id), seed.snapshot), log: [], have: new Set(), held: new Map(), broken: new Set(), counter: 0, issued: 0 });

  const applyRecord = (x, rec) => {
    const before = x.client.snapshot();
    const stateBefore = observe && stateOf(x.client);
    try {
      x.client.apply(copy(rec.update.ops));
    } catch (e) {
      x.client = newClient(x.session, before, x.client.clockOverrides);
      if (observe) observe({ phase: 'apply', replica: x.id, record: rec, ok: false, message: e.message, before: stateBefore, after: stateBefore });
      x.broken.add(rec.update.key);
      adapterStats.applyFailures++;
      if (adapterStats.applyFailureMessages.length < 20) adapterStats.applyFailureMessages.push({ record: rec.update.key, kind: rec.kind, message: e.message });
      return;
    }
    x.have.add(rec.update.key);
    x.log.push(rec);
    if (observe) observe({ phase: 'apply', replica: x.id, record: rec, ok: true, before: stateBefore, after: stateOf(x.client) });
  };
  const drain = (x) => {
    let progress = true;
    while (progress) {
      progress = false;
      for (const [key, rec] of x.held) {
        if (x.have.has(key) || x.broken.has(key)) x.held.delete(key);
        else if (rec.update.prior.every((k) => x.have.has(k))) {
          x.held.delete(key);
          applyRecord(x, rec);
        } else continue;
        progress = true;
      }
    }
  };
  const take = (x, rec) => {
    const key = rec.update.key;
    if (!x.have.has(key) && !x.held.has(key) && !x.broken.has(key)) x.held.set(key, rec);
    drain(x);
  };

  return {
    createReplica: (id) => fresh(id),
    loadInto(x, source) {
      x.client = newClient(x.session, source.client.snapshot());
      x.log = [...source.log];
      x.have = new Set(source.have);
      x.held = new Map(source.held);
      x.broken = new Set(source.broken);
    },
    validRequest: (x, q) => validOn(viewOf(x.client), q),
    issue(x, q) {
      const stateBefore = observe && stateOf(x.client);
      const { ops, commands } = issueOn(lib, x, q, newClient);
      const key = `${x.session}:${++x.issued}`;
      const rec = { replica: x.id, kind: q.kind, request: q, update: { key, ops, prior: [...x.have].sort() }, specOps: [{ key, commands }] };
      x.have.add(key);
      x.log.push(rec);
      if (observe) observe({ phase: 'issue', replica: x.id, record: rec, ok: true, before: stateBefore, after: stateOf(x.client) });
      return rec;
    },
    deliver(x, rec) {
      take(x, rec);
      return { pending: x.held.size > 0 || x.broken.size > 0, emitted: [] };
    },
    sync(to, from) {
      for (const rec of from.log) take(to, rec);
      for (const rec of from.held.values()) take(to, rec);
      drain(to);
      return { pending: to.held.size > 0 || to.broken.size > 0, emitted: [] };
    },
    view: (x) => viewOf(x.client),
    stateVector: (x) => ({ records: [...x.have].sort() }),
    integrated: (x, records) => new Set(records.filter((r) => x.have.has(r.update.key)).map((r) => r.key)),
    hasPending: (x) => x.held.size > 0 || x.broken.size > 0,
    inserted: (rec) => [...seed.inserted, ...insertedOf(rec.update.ops)],
    deleted: () => [],
    present: (x) => viewOf(x.client).flatMap((b) => b.chars.map((ch) => `${ch.text}@${ch.key}`)),
    snapshot: (x) => (x.broken.size ? { rejectedRecords: [...x.broken].sort() } : {}),
    traceRecord: (rec) => ({ record: rec.update.key, operations: rec.update.ops.map((o) => o.command), siblingMoves: siblingMoves(rec.update.ops), commands: rec.specOps[0].commands.map((c) => c.kind) }),
  };
}

export { blocksOf };
