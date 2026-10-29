/**
 * removed-anchor. A new block is listed after a given block by `listAfter`,
 * which appends at the end of the list when that block is no longer in it
 * (929891, placement by 75332); `moveTextSliceIntoBlock` moves a split's
 * block after the block holding the moved text only when that block is
 * alive (971340). Blocks
 * created or split off after a concurrently merged block therefore go to
 * the end of the page.
 *
 * Seed `ab | cd`. A splits cd at 0 and merges the empty block into ab
 * (`ab | cd`). B splits cd at 0 and creates a block after its block 1 (the
 * original cd block). Both new blocks of B are empty and belong before cd:
 * every order of the requests gives `ab | empty | empty | cd`. A shows
 * `ab | empty | cd | empty`. Control: A does not merge.
 *
 *   NOTION_PRODUCTION_LIBRARY=<export> node removed-anchor.mjs
 */
// ---- harness (identical in every script of this directory) ----------------
// Loads only the exported production library. Blocks are records under one
// page, created and removed by the same record commands as the library's
// ReplayReplica; split and merge requests run the original request builders
// (module 701590); every operation is applied by the shipped record handlers
// (module 971340). Trees are parsed as the editor's record store parses them
// (module 266858 with the per-instance clock holders of module 997076), one
// clock map per client. A record a client cannot apply is reported, and the
// client is restored to its state before it.
import { createHash } from 'node:crypto';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';

const dir = process.env.NOTION_PRODUCTION_LIBRARY;
if (!dir) throw new Error('Set NOTION_PRODUCTION_LIBRARY to the exported production library');
const { createClient, RequestBuilder } = await import(pathToFileURL(join(dir, 'index.mjs')).href);

const uuid = (label) => {
  const h = createHash('sha256').update(label).digest('hex');
  return `${h.slice(0, 8)}-${h.slice(8, 12)}-4${h.slice(13, 16)}-8${h.slice(17, 20)}-${h.slice(20, 32)}`;
};
const SPACE = uuid('repro-space');
const PAGE = { table: 'block', id: uuid('repro-page'), spaceId: SPACE };
const ptr = (id) => ({ table: 'block', id, spaceId: SPACE });
const copy = (v) => JSON.parse(JSON.stringify(v));

function client(session, snapshot, overrides = new Map()) {
  const c = createClient(session, snapshot);
  const W = c.runtime.require('997076').W;
  const parse = c.runtime.require('266858').r;
  c.clockOverrides = overrides;
  c.tree = function (p) {
    W.overrides = overrides;
    return parse(this.recordMap.getValue(p).crdt_data.title, ({ value, textInstanceId }) => new W(value, textInstanceId), this.session);
  };
  return c;
}

class Replica {
  constructor(session, snapshot) {
    this.session = session;
    this.c = client(session, snapshot);
    this.n = 0;
    this.rejected = [];
  }
  view() {
    return (this.c.value(PAGE).content ?? []).filter((id) => this.c.value(ptr(id)).alive).map((id) => ({ id, text: this.c.text(ptr(id)), rich: this.c.rich(ptr(id)) }));
  }
  show() {
    return this.view().map((b) => b.rich.map(([t, a = []]) => (a.some((x) => x[0] === 'b') ? [...t].map((ch) => `[${ch}]`).join('') : t)).join('') || 'empty').join(' | ');
  }
  id(block) {
    return this.view()[block].id;
  }
  create(after, ops = []) {
    const id = uuid(`${this.session}:block:${++this.n}`);
    this.c.createBlock(ptr(id));
    const own = [
      { command: 'set', pointer: ptr(id), path: [], args: { ...this.c.value(ptr(id)), parent_table: 'block', parent_id: PAGE.id } },
      { command: 'listAfter', pointer: PAGE, path: ['content'], args: { id, ...(after ? { after } : {}) } },
    ];
    this.c.apply(own);
    ops.push(...own);
    return { id, ops };
  }
  createAfter(block) {
    return this.create(this.id(block)).ops;
  }
  insert(block, index, text) {
    const ops = this.c.prepareInsert(ptr(this.id(block)), index, text);
    this.c.apply(ops);
    return ops;
  }
  split(block, index) {
    const source = this.id(block);
    const { id, ops } = this.create(source);
    const b = new RequestBuilder(this.c);
    b.split(ptr(source), ptr(id), index);
    return [...ops, ...b.operations];
  }
  merge(block) {
    const source = this.id(block);
    const b = new RequestBuilder(this.c);
    b.merge(ptr(source), ptr(this.id(block - 1)));
    const removal = [
      { command: 'set', pointer: ptr(source), path: ['alive'], args: false },
      { command: 'listRemove', pointer: PAGE, path: ['content'], args: { id: source } },
    ];
    this.c.apply(removal);
    return [...b.operations, ...removal];
  }
  bold(block, start, end) {
    const rich = this.view()[block].rich.flatMap(([t, a = []]) => [...t].map(() => a.some((x) => x[0] === 'b')));
    const ops = this.c.prepareBold(ptr(this.id(block)), start, end, !rich.slice(start, end).every(Boolean));
    this.c.apply(ops);
    return ops;
  }
  receive(name, ops) {
    const before = this.c.snapshot();
    try {
      this.c.apply(copy(ops));
    } catch (e) {
      this.c = client(this.session, before, this.c.clockOverrides);
      this.rejected.push(`${name}: ${e.message}`);
    }
  }
}

/** Replicas A, B, ... from a seed page whose blocks hold `texts`. */
function document(texts, ...sessions) {
  const s = new Replica('seed');
  s.c.createBlock(PAGE);
  s.c.apply([
    { command: 'set', pointer: PAGE, path: ['type'], args: 'page' },
    { command: 'set', pointer: PAGE, path: ['content'], args: [] },
  ]);
  let previous;
  for (const t of texts) {
    previous = s.create(previous).id;
    if (t) s.c.apply(s.c.prepareInsert(ptr(previous), 0, t));
  }
  const snapshot = s.c.snapshot();
  return sessions.map((x) => new Replica(x, snapshot));
}

/** Prints a verdict line and returns whether `observed` equals `expected` (or lies in it). */
function report(label, observed, expected) {
  const ok = Array.isArray(expected) ? expected.includes(observed) : observed === expected;
  console.log(`${label}: ${observed}${ok ? '' : `  (expected ${Array.isArray(expected) ? expected.join(' or ') : expected})`}`);
  return ok;
}
// ---- end of harness ---------------------------------------------------------

function run(control) {
  const [A, B] = document(['ab', 'cd'], 'A', 'B');
  const a1 = A.split(1, 0);
  const a2 = control ? null : A.merge(1);
  const b1 = B.split(1, 0);
  const b2 = B.createAfter(1);
  A.receive('B split', b1);
  A.receive('B create', b2);
  console.log(`${control ? 'control' : 'defect '}  rejected at A: ${A.rejected.join('; ') || 'none'}`);
  return report('  A', A.show(), control ? 'ab | empty | empty | empty | cd' : 'ab | empty | empty | cd');
}
const defect = run(false);
const control = run(true);
console.log(!defect && control ? 'reproduced: the blocks go to the end of the page; the control keeps them before cd' : 'not reproduced');
process.exit(!defect && control ? 0 : 1);
