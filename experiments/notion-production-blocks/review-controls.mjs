// Independent review controls. No downloaded module bodies are copied here.
// Run: NOTION_PRODUCTION_LIBRARY=<pinned export> node --test review-controls.mjs
import assert from 'node:assert/strict';
import test, { after } from 'node:test';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { loadLibrary, verifySources, productionBlocksInstance, renderBlocks } from '../../ra-pbt/instances/notion-production-blocks/index.js';
import { Execution, eventsAt, allFinalViews, findWitness } from '../../ra-pbt/src/index.js';
import { ReplayReplica } from '../notion-production-client/replay.mjs';

const lib = await loadLibrary();
after(() => verifySources(lib.directory));

// Use the verbatim BlockStore getter and native per-runtime clock map.
// The only dependency injection is the fixture's session ID. The two record
// accessors expose fixture data; the production getter chooses the parser
// and clock holders. No assignment to W.overrides and no replacement parser.
export function nativeEditorLibrary(library) {
  return { ...library, createClient(session, snapshot) {
    const c = library.createClient(session, snapshot);
    const B = c.runtime.instantiate('970831', { '727114': { t: session } }).B;
    c.tree = function (pointer) {
      const value = this.recordMap.getValue(pointer);
      const store = Object.create(B.prototype);
      Object.defineProperties(store, {
        getVersion: { value: () => value.version },
        getSerializedTextSliceTreeStore: { value: () => ({ getValue: () => value.crdt_data.title }) },
      });
      return store.getBlockTitleTextSliceTree();
    };
    return c;
  } };
}
const native = nativeEditorLibrary(lib);
const extracted = JSON.parse(readFileSync(join(lib.directory, 'modules.json'), 'utf8'));
const edit = (replica, kind, block, more = {}) => ({ type: 'edit', replica, kind, block, ...more });
const split = (r, b, index) => edit(r, 'split', b, { index });
const merge = (r, b) => edit(r, 'merge', b);
const insert = (r, b, index, text) => edit(r, 'insert', b, { index, text });
const bold = (r, b, start, end) => edit(r, 'bold', b, { start, end });
const create = (r, after) => edit(r, 'create', undefined, { after });
const send = (from, to, op) => ({ type: 'send', from, to, op });
const deliver = (from, to) => ({ type: 'deliver', from, to });

function run(texts, steps, { profile = 'blocks', sessions = ['A', 'B'], replicas = 2, recordModel = false } = {}) {
  const inst = productionBlocksInstance(recordModel ? lib : native, {
    texts, profile, sessions, isolated: true, liveClock: false,
  });
  const ex = new Execution(inst, replicas, { checks: ['conservation'] });
  for (const step of steps) ex.apply(step);
  ex.finish();
  return { ex, inst, shown: Array.from({ length: replicas }, (_, i) => renderBlocks(ex.adapter.view(ex.replica(i + 1)))) };
}
function complete({ ex }) {
  for (const r of Object.keys(ex.replicas)) {
    const x = ex.replica(Number(r));
    assert.equal(x.broken.size, 0);
    assert.equal(ex.adapter.hasPending(x), false);
    assert.equal(x.have.size, ex.ops.length);
    assert.equal(eventsAt(ex, Number(r)).gaps, 0);
  }
}
function rejectedReady({ ex }, r, kind, message) {
  const x = ex.replica(r);
  assert.equal(x.broken.size, 1);
  const rec = ex.ops.find(o => x.broken.has(o.update.key));
  assert.equal(rec.kind, kind);
  assert(rec.update.prior.every(k => x.have.has(k)), 'rejected record lacks causal predecessors');
  assert.equal(x.have.size, ex.ops.length - 1);
  // Retry on a fresh copy, avoiding partial mutation from a thrown handler.
  const retry = native.createClient(x.session, x.client.snapshot());
  assert.throws(() => retry.apply(rec.update.ops), message);
  assert.equal(eventsAt(ex, r).gaps, 0);
}

test('native editor clocks avoid the record-model duplicate-marker counterexample', () => {
  const steps = [split(1, 0, 2), split(1, 1, 0), split(1, 0, 1), merge(1, 3)];
  const good = run(['abc'], steps, { replicas: 1 });
  const bad = run(['abc'], steps, { replicas: 1, recordModel: true });
  complete(good);
  assert.deepEqual(good.shown, ['a | b | c']);
  assert.deepEqual(bad.shown, ['ac | b | empty']);
  assert.notDeepEqual(good.shown, bad.shown);
});

for (const [name, text, left, right, before, rejects] of [
  ['N-002', 'ab', 0, 1, ['a', 'b'], true],
  ['N-003', 'abc', 1, 2, ['a', 'bc'], false],
]) test(`${name}: original replay selection and full-exchange result differ from the native-clock fixture`, () => {
    const seed = new ReplayReplica(extracted, 'seed');
    const block = seed.createBlock(text).newBlockId;
    const a = seed.fork('A'), b = seed.fork('B');
    const aSplit = a.split(block, left), bSplit = b.split(block, right);
    a.receive(bSplit.packet);
    a.merge(name === 'N-002' ? aSplit.newBlockId : bSplit.newBlockId);
    assert.deepEqual(a.view().map(x => x.text), before);
    const target = name === 'N-002' ? bSplit.newBlockId : block;
    // This is the original replay's contract: select the entire actual target
    // block. It is NOT the native-clock fixture's two-character selection.
    const length = a.view().find(x => x.id === target).text.length;
    assert.equal(length, 1);
    assert.notEqual(length, 2);
    a.bold(target, 0, length);
    assert(a.actions.filter(x => x.localContract !== undefined).every(x => x.localContract));
    assert.deepEqual(a.view().map(x => x.rich), name === 'N-002'
      ? [[['a']], [['b', [['b']]]]] : [[['a', [['b']]]], [['bc']]]);
    let rejected;
    for (const packet of a.packets) {
      try { b.receive(packet); } catch (error) { rejected = { packet, error }; break; }
    }
    if (rejects) {
      assert.equal(rejected?.packet.request.kind, 'bold');
      assert.match(rejected.error.message, /Unable to apply annotation operation due to start missing/);
      assert.notDeepEqual(a.view().map(x => x.rich), b.view().map(x => x.rich));
    } else {
      assert.equal(rejected, undefined);
      assert.deepEqual(a.view().map(x => x.rich), b.view().map(x => x.rich));
      assert(a.packets.every(p => b.packets.some(q => p.id === q.id)));
    }
    assert.deepEqual(a.view().map(x => x.text), b.view().map(x => x.text));
  });

for (const sessions of [['A', 'B'], ['B', 'A']]) {
  const order = sessions.join(',');
  test(`native editor getter: label rejection is causally ready, sessions ${order}`, () => {
    const r = run(['abc'], [split(1, 0, 1), split(2, 0, 2), insert(1, 1, 0, 'X')], { sessions });
    assert.deepEqual(r.shown, ['a | Xb | c', 'a | b | c']);
    rejectedReady(r, 2, 'insert', /Cannot backfill prev item that is not a text item/);
    const ctl = run(['abc'], [split(1, 0, 1), deliver(1, 2), split(2, 1, 1), insert(1, 1, 0, 'X')], { sessions });
    complete(ctl);
    assert.deepEqual(ctl.shown, ['a | Xb | c', 'a | Xb | c']);
    assert.notDeepEqual(r.shown, ctl.shown);
  });
  for (const [name, texts, steps, expected] of [
    ['N-002', ['ab'], [split(1, 0, 0), split(2, 0, 1), send(2, 1, 0), merge(1, 2), bold(1, 1, 0, 2)], ['empty | [a][b]', 'empty | ab']],
    ['N-003', ['abc'], [split(1, 0, 1), split(2, 0, 2), send(2, 1, 0), merge(1, 1), bold(1, 0, 0, 2)], ['[a][b] | c', 'ab | c']],
  ]) test(`${name}: full exchange rejects only bold, preserves characters, sessions ${order}`, () => {
    const r = run(texts, steps, { sessions, profile: 'format' });
    assert.deepEqual(r.shown, expected);
    rejectedReady(r, 2, 'bold', /Unable to apply annotation operation due to start missing/);
    const failures = r.ex.checkState.results().conservation.details.failures;
    assert.equal(failures.length, 1);
    assert.deepEqual(failures[0].expected, failures[0].actual);
    assert.equal(failures[0].pending, true);
    assert.equal(failures[0].notIntegrated.length, 1);
    assert.notEqual(r.shown[0], r.shown[1]);
  });
  test(`native editor getter: past-boundary rejection, sessions ${order}`, () => {
    const r = run(['a', 'b', 'c'], [split(1, 1, 0), split(1, 1, 0), merge(2, 1)], { sessions });
    assert.deepEqual(r.shown, ['a | empty | b | c', 'a | b | c']);
    rejectedReady(r, 2, 'split', /splitTextSliceResult must exist/);
    const ctl = run(['a', 'b', 'c'], [split(1, 1, 0), merge(2, 1)], { sessions });
    complete(ctl);
    assert.deepEqual(ctl.shown, ['a | b | c', 'a | b | c']);
  });
  test(`native editor getter: concurrent move diverges with all records integrated, sessions ${order}`, () => {
    const steps = [merge(2, 1), send(2, 1, 0), split(2, 0, 1), merge(2, 1), split(1, 0, 1)];
    const r = run(['a', 'b', 'c'], steps, { sessions });
    complete(r);
    assert.deepEqual(r.shown, ['ab | empty | c', 'a | b | c']);
    assert.notEqual(r.shown[0], r.shown[1]);
    const ctl = run(['a', 'b', 'c'], [...steps.slice(0, 4), deliver(2, 1), steps[4]], { sessions });
    complete(ctl);
    assert.deepEqual(ctl.shown, ['a | b | c', 'a | b | c']);
  });
}

for (const [name, texts, steps, replica, actual, allOrdersReject] of [
  ['stale-merge', ['a', 'b', 'c'], [merge(1, 2), merge(2, 2), split(2, 1, 1)], 2, 'a | bc | empty', true],
  ['removed-anchor', ['ab', 'cd'], [split(1, 1, 0), merge(1, 1), split(2, 1, 0), create(2, 1)], 1, 'ab | empty | cd | empty', false],
  ['order-mismatch', ['a'], [create(1, 0), insert(1, 0, 0, 'Y'), split(2, 0, 0)], 2, 'empty | empty | Ya', false],
]) test(`${name}: distinguish causal witness failure from completely relaxed order`, () => {
  const r = run(texts, steps);
  complete(r);
  const target = r.ex.adapter.view(r.ex.replica(replica));
  assert.equal(renderBlocks(target), actual);
  const { events, gaps } = eventsAt(r.ex, replica);
  assert.equal(gaps, 0);
  assert.equal(findWitness(r.inst.spec, events, target).found, false);
  const relaxed = events.map(e => ({ ...e, deps: [] }));
  const admitted = allFinalViews(r.inst.spec, relaxed);
  assert.notEqual(admitted.truncated, true);
  assert(admitted.length > 0, 'specification has no admitted execution');
  assert.equal(findWitness(r.inst.spec, relaxed, target).found, !allOrdersReject);
  assert.equal(admitted.some(v => r.inst.spec.viewKey(v) === r.inst.spec.viewKey(target)), !allOrdersReject);
  if (allOrdersReject) {
    assert.deepEqual(admitted.map(renderBlocks), ['a | b | c']);
    assert(!admitted.map(renderBlocks).includes(actual));
  } else assert(admitted.map(renderBlocks).includes(actual));
});
