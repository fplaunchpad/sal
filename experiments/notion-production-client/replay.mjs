import { createHash } from 'node:crypto';
import { ProductionClient } from './client.mjs';
import { RequestBuilder } from './requests.mjs';
import { request as sequentialRequest } from '../notion-oracle/positional-spec.mjs';

const copy = value => JSON.parse(JSON.stringify(value));
const uuid = label => {
  const h = createHash('sha256').update(label).digest('hex');
  return `${h.slice(0,8)}-${h.slice(8,12)}-4${h.slice(13,16)}-8${h.slice(17,20)}-${h.slice(20,32)}`;
};
const spaceId = uuid('production-replay-space');
const parent = { table: 'block', id: uuid('production-replay-page'), spaceId };
const pointer = id => ({ table: 'block', id, spaceId });
export const observedCharacters = view => view.map(block => block.rich.flatMap(([text, annotations = []]) =>
  [...text].map(text => ({ text, bold: annotations.some(a => a[0] === 'b') }))));
const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);

// A request/record-handler experiment. Transport and fixture block creation
// are ours; split/merge payloads come from the unmodified production builder.
// Receiving a packet runs the shared record handlers, not Notion's sync client.
export class ReplayReplica {
  constructor(extracted, session, initial, sessions = {}) {
    this.extracted = extracted;
    this.session = session;
    this.sessions = sessions;
    this.sourceSession = sessions[session] ?? session;
    this.counter = 0;
    this.clock = initial?.clock ?? 0;
    this.packets = copy(initial?.packets ?? []);
    this.client = new ProductionClient(extracted, this.sourceSession, initial?.snapshot);
    this.actions = [];
    if (!initial) {
      this.client.createBlock(parent);
      this.client.apply([{ command: 'set', pointer: parent, path: ['type'], args: 'page' },
        { command: 'set', pointer: parent, path: ['content'], args: [] }]);
    }
  }
  fork(session) {
    return new ReplayReplica(this.extracted, session, {
      clock: this.clock, packets: this.packets, snapshot: this.client.snapshot(),
    }, this.sessions);
  }
  state() { return { snapshot: this.client.snapshot(), clock: this.clock, packets: copy(this.packets) }; }
  view() {
    return (this.client.value(parent).content ?? []).filter(id => this.client.value(pointer(id))?.alive)
      .map(id => ({ id, text: this.client.text(pointer(id)), rich: this.client.rich(pointer(id)) }));
  }
  idAt(index) {
    const item = this.view()[index];
    if (!item) throw new Error(`No live block at index ${index}: ${JSON.stringify(this.view())}`);
    return item.id;
  }
  apply(operations) { this.client.apply(operations); return operations; }
  issue(request, perform) {
    const before = this.state(), beforeView = this.view(), past = this.packets.map(p => p.id);
    const operations = [];
    try {
      const result = perform(operations);
      const packet = { id: `${this.session}:${++this.clock}`, clock: this.clock,
        session: this.session, request, past, operations: copy(operations) };
      this.packets.push(packet);
      const after = this.view();
      const expected = request.kind === 'create' ? undefined : sequentialRequest(observedCharacters(beforeView),
        { ...request, block: beforeView.findIndex(b => b.id === request.block) });
      this.actions.push({ kind: 'issue', request, packet: copy(packet), before: beforeView, after,
        ...(expected ? { expected, localContract: same(observedCharacters(after), expected) } : {}) });
      return { ...result, packet };
    } catch (error) {
      this.client = new ProductionClient(this.extracted, this.sourceSession, before.snapshot);
      this.clock = before.clock; this.packets = before.packets;
      error.replayContext = { kind: 'issue', request, before: beforeView, operations: copy(operations) };
      throw error;
    }
  }
  create(operations, after) {
    const id = uuid(`${this.session}:block:${++this.counter}`), p = pointer(id);
    this.client.createBlock(p);
    const value = { ...this.client.value(p), parent_table: 'block', parent_id: parent.id };
    const ops = [{ command: 'set', pointer: p, path: [], args: value },
      { command: 'listAfter', pointer: parent, path: ['content'], args: { id, ...(after ? { after } : {}) } }];
    operations.push(...ops); this.apply(ops);
    return id;
  }
  createBlock(text = '', after) {
    return this.issue({ kind: 'create', text, after }, operations => {
      const newBlockId = this.create(operations, after);
      if (text) { const ops = this.client.prepareInsert(pointer(newBlockId), 0, text); operations.push(...ops); this.apply(ops); }
      return { newBlockId };
    });
  }
  insert(block, index, text) {
    return this.issue({ kind: 'insert', block, index, text }, operations => {
      const ops = this.client.prepareInsert(pointer(block), index, text); operations.push(...ops); this.apply(ops);
    });
  }
  split(block, index) {
    if (!this.view().some(b => b.id === block)) throw new Error('Split source must be live');
    return this.issue({ kind: 'split', block, index }, operations => {
      const newBlockId = this.create(operations, block);
      const builder = new RequestBuilder(this.client);
      try { builder.split(pointer(block), pointer(newBlockId), index); }
      finally { operations.push(...builder.operations); }
      return { newBlockId };
    });
  }
  merge(block) {
    const index = this.view().findIndex(b => b.id === block);
    if (index <= 0) throw new Error('Merge requires a live predecessor');
    const previous = this.idAt(index - 1);
    return this.issue({ kind: 'merge', block, previous }, operations => {
      const builder = new RequestBuilder(this.client);
      try { builder.merge(pointer(block), pointer(previous)); }
      finally { operations.push(...builder.operations); }
      const removed = [{ command: 'set', pointer: pointer(block), path: ['alive'], args: false },
        { command: 'listRemove', pointer: parent, path: ['content'], args: { id: block } }];
      operations.push(...removed); this.apply(removed);
    });
  }
  bold(block, start, end) {
    return this.issue({ kind: 'bold', block, start, end }, operations => {
      const selected = this.client.rich(pointer(block));
      const flags = selected.flatMap(([text, annotations = []]) =>
        [...text].map(() => annotations.some(a => a[0] === 'b'))).slice(start, end);
      const add = !flags.every(Boolean);
      const ops = this.client.prepareBold(pointer(block), start, end, add); operations.push(...ops); this.apply(ops);
    });
  }
  receive(packet) {
    if (this.packets.some(p => p.id === packet.id)) return;
    const known = new Set(this.packets.map(p => p.id));
    if (!packet.past.every(id => known.has(id))) throw new Error(`Delivery lacks causal past for ${packet.id}`);
    const before = this.client.snapshot(), beforeView = this.view();
    try { this.apply(packet.operations); }
    catch (error) {
      this.client = new ProductionClient(this.extracted, this.sourceSession, before);
      error.replayContext = { kind: 'receive', packet: copy(packet), before: beforeView };
      throw error;
    }
    this.packets.push(copy(packet)); this.clock = Math.max(this.clock, packet.clock);
    this.actions.push({ kind: 'receive', packetId: packet.id, before: beforeView, after: this.view() });
  }
}

export function replayCases(extracted, sessions = {}) {
  const records = [];
  const demoLayouts = { 'N-001': ['', 'aX'], 'N-002': ['', 'ba'], 'N-003': ['ac', 'b'],
    'N-004': ['', 'abc'], 'N-005': ['', '', 'x'] };
  function run(id, execute) {
    const tracked = [];
    const track = r => { tracked.push(r); return r; };
    try {
      const result = execute(track);
      const localFailures = tracked.flatMap(r => r.actions.filter(a => a.localContract === false));
      records.push({ id, ...result,
        status: localFailures.length || result.conservation === false ? 'handler-contract-failure' : 'not-reproduced',
        demoBefore: demoLayouts[id], demoLayoutReached: same(result.before.map(b => b.text), demoLayouts[id]),
        localFailures, replicas: tracked.map(r => ({ session: r.session, view: r.view(), actions: r.actions })) });
    }
    catch (error) { records.push({ id, status: 'trace-rejected', message: error.message,
      context: error.replayContext, replicas: tracked.map(r => ({ session: r.session, view: r.view(), actions: r.actions })) }); }
  }
  const seed = (texts, track) => {
    const s = track(new ReplayReplica(extracted, 'seed', undefined, sessions)); let previous;
    for (const text of texts) previous = s.createBlock(text, previous).newBlockId;
    return s;
  };
  const flags = view => view.map(b => b.rich.flatMap(([text, annotations = []]) =>
    [...text].map(() => annotations.some(a => a[0] === 'b'))));
  run('N-002', track => {
    const s = seed(['ab'], track), block = s.idAt(0), a = track(s.fork('A')), b = track(s.fork('B'));
    const left = a.split(block, 0), right = b.split(block, 1); a.receive(right.packet);
    a.merge(left.newBlockId); const before = a.view();
    a.bold(right.newBlockId, 0, a.client.text(pointer(right.newBlockId)).length);
    const actual = flags(a.view());
    return { before, actual };
  });
  run('N-003', track => {
    const s = seed(['abc'], track), block = s.idAt(0), a = track(s.fork('A')), b = track(s.fork('B'));
    a.split(block, 1); const right = b.split(block, 2); a.receive(right.packet);
    a.merge(right.newBlockId); const before = a.view();
    a.bold(block, 0, a.client.text(pointer(block)).length);
    const actual = flags(a.view());
    return { before, actual };
  });
  run('N-001', track => {
    const s = seed(['a'], track), block = s.idAt(0), setup = track(s.fork('S'));
    const first = setup.split(block, 0); setup.insert(block, 0, 'X');
    const a = track(setup.fork('A')), b = track(setup.fork('B'));
    a.merge(first.newBlockId); const mb = b.merge(first.newBlockId); a.receive(mb.packet);
    const c = track(a.fork('C')), d = track(a.fork('D'));
    const sc = c.split(block, 0), sd = d.split(block, 1); c.receive(sd.packet);
    c.merge(sc.newBlockId); const before = c.view(), at = before.findIndex(x => x.id === sd.newBlockId);
    const expected = before.map(x => x.text); expected.splice(at, 1, '', expected[at]);
    c.split(sd.newBlockId, 0); const actual = c.view().map(x => x.text);
    return { before, expected, actual };
  });
  run('N-004', track => {
    const s = seed(['a','b','c'], track), a = track(s.fork('A')), b = track(s.fork('B'));
    const a0 = a.merge(a.idAt(2)), a1 = a.split(a.idAt(1),0), a2 = a.merge(a.idAt(2));
    const b0 = b.merge(b.idAt(1)); b.receive(a0.packet); b.receive(a1.packet);
    const before = b.view(), b1 = b.merge(b.idAt(1)); b.receive(a2.packet);
    a.receive(b0.packet); a.receive(b1.packet);
    const actual = [a.view(), b.view()].map(v => v.map(x => x.text).join('').split('').sort().join(''));
    return { conservation: actual.every(v => v === 'abc'), before, expected: 'abc', actual };
  });
  run('N-005', track => {
    const s = seed(['x'], track), a = track(s.fork('A')), b = track(s.fork('B'));
    const a0 = a.split(a.idAt(0),0), b0 = b.split(b.idAt(0),1), b1 = b.merge(b.idAt(1));
    a.receive(b0.packet); const before = a.view(), a1 = a.merge(a.idAt(2));
    a.receive(b1.packet); b.receive(a0.packet); b.receive(a1.packet);
    const actual = [a.view(), b.view()].map(v => v.map(x => x.text).join(''));
    return { conservation: actual.every(v => v === 'x'), before, expected: 'x', actual };
  });
  return records;
}
