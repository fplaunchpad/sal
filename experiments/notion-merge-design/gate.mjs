// Recorded demo bugs N-001 to N-005, reissued as client requests against
// whichever modules sit beside this file (the demo, the design or a control
// variant). Nothing is asserted: each case reports its contract, the expected
// outcome, the observed outcome, and whether the precondition of the recorded
// failure was reached. Expected outcomes are hand-derived or come from the
// independent positional specification, never from the code under test.
// Run with `node --import ./ra-hook.mjs gate.mjs`.
import {Replica} from './replica.js';
import {request} from './positional-spec.mjs';
import {initial, replay as replayRounds, probe, texts} from './campaign-lib.mjs';
import {IdentitySpec} from './identity-spec.mjs';
import {compare, displayOf} from './ra-check.mjs';

const view = r => r.document().aliveBlocks().map(b => ({id: b.id, text: r.document().blockText(b.id),
  characters: r.document().blockCharacters(b.id).map(c => ({text: c.text, bold: !!c.bold}))}));
const observable = v => v.map(b => b.characters);
const shown = r => view(r).map(b => b.text);
const visible = r => shown(r).join('').split('').sort().join('');
const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const seedBlocks = list => { const r = new Replica('seed', 'seed', []); let p;
  for (const t of list) { p = r.createBlock(p).newBlockId; r.insertText(p, 0, t); } return r.transactions(); };
const idAt = (r, i) => r.document().aliveBlocks()[i].id;
const issue = (r, f) => { const prior = new Set(r.transactions().map(t => JSON.stringify(t.id))); f();
  return r.transactions().filter(t => !prior.has(JSON.stringify(t.id))); };
const deliver = (r, txs) => { for (const t of txs) r.receive(t); };
const merge = (r, i) => issue(r, () => r.mergeBlock(idAt(r, i)));
const split = (r, i, k) => issue(r, () => r.splitBlock(idAt(r, i), k));

const cases = [];
const record = (c) => { cases.push(c); };
const guard = (name, f) => { try { f(); } catch (e) { record({name, exception: e.message}); } };

// N-002 (selected bold) and its passing control.
for (const which of ['left', 'right']) guard(which === 'left' ? 'N-002 bold selection misses selected characters' : 'N-002 control', () => {
  const seed = new Replica('seed', 'seed', []), {newBlockId: block} = seed.createBlock(); seed.insertText(block, 0, 'ab');
  const a = new Replica('A', 'A', seed.transactions()), b = new Replica('B', 'B', seed.transactions());
  const left = a.splitBlock(block, 0), right = b.splitBlock(block, 1);
  a.receive(right.transaction); a.receive(left.transaction);
  if (which === 'left') a.mergeBlock(left.newBlockId); else a.mergeBlock(right.newBlockId);
  const before = view(a), target = which === 'left' ? right.newBlockId : block;
  const bi = before.findIndex(x => x.id === target), n = before[bi].characters.length;
  const expected = request(observable(before), {kind: 'bold', block: bi, start: 0, end: n});
  a.toggleBold(target, 0, n);
  const actual = observable(view(a));
  record({name: which === 'left' ? 'N-002 bold selection misses selected characters' : 'N-002 control',
    contract: 'positional bold', before: before.map(x => x.text), demoPrecondition: which === 'left' ? ['', 'ba'] : ['b', 'a'],
    preconditionReached: same(before.map(x => x.text), which === 'left' ? ['', 'ba'] : ['b', 'a']),
    expected, actual, contractHolds: same(actual, expected)});
});

// N-003 (bold outside the selection).
guard('N-003 bold selection changes an unselected character', () => {
  const seed = new Replica('seed', 'seed', []), {newBlockId: block} = seed.createBlock(); seed.insertText(block, 0, 'abc');
  const a = new Replica('A', 'A', seed.transactions()), b = new Replica('B', 'B', seed.transactions());
  a.splitBlock(block, 1); const right = b.splitBlock(block, 2); a.receive(right.transaction);
  a.mergeBlock(right.newBlockId);
  const before = view(a), expected = request(observable(before), {kind: 'bold', block: 0, start: 0, end: 2});
  a.toggleBold(block, 0, 2);
  const actual = observable(view(a));
  record({name: 'N-003 bold selection changes an unselected character', contract: 'positional bold',
    before: before.map(x => x.text), demoPrecondition: ['ac', 'b'], preconditionReached: same(before.map(x => x.text), ['ac', 'b']),
    expected, actual, contractHolds: same(actual, expected)});
});

// N-001 (split at zero moves only part of the suffix), oracle history.
guard('N-001 split at zero', () => {
  const seed = new Replica('seed', 'seed', []), {newBlockId: block} = seed.createBlock(); seed.insertText(block, 0, 'a');
  const setup = new Replica('S', 'S', seed.transactions()), first = setup.splitBlock(block, 0); setup.insertText(block, 0, 'X');
  const a = new Replica('A', 'A', setup.transactions()), b = new Replica('B', 'B', setup.transactions());
  a.mergeBlock(first.newBlockId); const mb = b.mergeBlock(first.newBlockId); a.receive(mb.transaction);
  const c = new Replica('C', 'C', a.transactions()), d = new Replica('D', 'D', a.transactions());
  const sc = c.splitBlock(block, 0), sd = d.splitBlock(block, 1); c.receive(sd.transaction);
  c.mergeBlock(sc.newBlockId);
  const before = view(c), bi = before.findIndex(x => x.id === sd.newBlockId);
  if (bi < 0) { record({name: 'N-001 split at zero', contract: 'positional split', before: before.map(x => x.text),
    demoPrecondition: ['', 'aX'], preconditionReached: false, note: 'the block split by D is not displayed, so the recorded split request does not exist'}); return; }
  const expected = request(observable(before), {kind: 'split', block: bi, index: 0});
  c.splitBlock(sd.newBlockId, 0);
  const actual = observable(view(c));
  record({name: 'N-001 split at zero', contract: 'positional split', before: before.map(x => x.text),
    demoPrecondition: ['', 'aX'], preconditionReached: same(before.map(x => x.text), ['', 'aX']),
    expected: texts(expected), actual: texts(actual), contractHolds: same(actual, expected)});
});

// N-001, six structural requests (experiments/notion-correctness/regressions.mjs).
guard('N-001 six-request variant', () => {
  const s = (block, index) => ({kind: 'split', block, index}), m = block => ({kind: 'merge', block});
  const trace = {text: 'ab', rounds: [
    {branches: [{session: 'S', requests: [s(0, 0), s(0, 0)]}]},
    {branches: [{session: 'A', requests: [s(2, 1), m(2)]}, {session: 'B', requests: [m(2)]}]},
    {branches: [{session: 'C', requests: [m(2)]}]}]};
  let p;
  try { p = probe(replayRounds(trace), s(1, 0)); }
  catch (e) { record({name: 'N-001 six-request variant', contract: 'positional split', preconditionReached: false, note: 'history invalid here: ' + e.message}); return; }
  const before = texts(p.before.map(b => b.chars));
  record({name: 'N-001 six-request variant', contract: 'positional split', before, demoPrecondition: ['', 'ab'],
    preconditionReached: same(before, ['', 'ab']), expected: p.expected && texts(p.expected), actual: p.actual && texts(p.actual),
    contractHolds: p.valid && !p.signature});
});

// N-004: merge into a removed block. Split and merge never delete text.
const lose = ({firstMerge = true, lastEarly = false} = {}) => {
  const init = seedBlocks(['a', 'b', 'c']), a = new Replica('A', 'A', init), b = new Replica('B', 'B', init);
  const a0 = merge(a, 2), a1 = split(a, 1, 0), a2 = merge(a, 2);
  const b0 = firstMerge ? merge(b, 1) : []; deliver(b, a0); deliver(b, a1);
  if (lastEarly) deliver(b, a2);
  const before = shown(b), b1 = lastEarly ? [] : merge(b, 1);
  if (!lastEarly) deliver(b, a2);
  deliver(a, b0); deliver(a, b1);
  return {before, actual: shown(b), visible: visible(b), converged: same(shown(a), shown(b))};
};
guard('N-004 merge into a removed block hides the document', () => {
  const r = lose(), controls = {noFirstMerge: lose({firstMerge: false}), lastMergeDeliveredEarly: lose({lastEarly: true})};
  record({name: 'N-004 merge into a removed block hides the document', contract: 'conservation: visible multiset abc',
    before: r.before, demoPrecondition: ['', 'abc'], preconditionReached: same(r.before, ['', 'abc']),
    expected: 'abc', actual: r.actual, visible: r.visible, converged: r.converged, contractHolds: r.visible === 'abc',
    controls: Object.fromEntries(Object.entries(controls).map(([k, c]) => [k, {actual: c.actual, holds: c.visible === 'abc'}]))});
});

// N-005: a delayed merge hides a character (oracle history).
const hide = ({held = true, localMerge = true, early = false} = {}) => {
  const init = seedBlocks(['x']), a = new Replica('A', 'A', init), b = new Replica('B', 'B', init);
  const a0 = split(a, 0, 0), b0 = split(b, 0, 1), b1 = merge(b, 1);
  deliver(a, b0); if (early) deliver(a, b1);
  const before = shown(a);
  const a1 = localMerge ? merge(a, early ? 1 : 2) : [];
  if (held && !early) deliver(a, b1);
  deliver(b, a0); deliver(b, a1);
  return {before, actual: shown(a), visible: visible(a), converged: same(shown(a), shown(b))};
};
guard('N-005 delayed merge hides a character', () => {
  const r = hide(), controls = {notDelivered: hide({held: false}), noLocalMerge: hide({localMerge: false}), deliveredEarly: hide({early: true})};
  record({name: 'N-005 delayed merge hides a character', contract: 'conservation: visible multiset x',
    before: r.before, demoPrecondition: ['', '', 'x'], preconditionReached: same(r.before, ['', '', 'x']),
    expected: 'x', actual: r.actual, visible: r.visible, converged: r.converged, contractHolds: r.visible === 'x',
    controls: Object.fromEntries(Object.entries(controls).map(([k, c]) => [k, {actual: c.actual, holds: c.visible === 'x'}]))});
});

// N-005, persistent-client form with an extra split (offline-regression.mjs, padding 1).
guard('N-005 persistent-client form', () => {
  const txs = initial(['x']), a = new Replica('p0c1', 'A', txs), b = new Replica('p0c2', 'B', txs);
  const step = (r, f) => { const out = f(); return out.transaction ?? out; };
  const ownA = [step(a, () => a.splitBlock(idAt(a, 0), 0))];
  const remoteSplit = step(b, () => b.splitBlock(idAt(b, 0), 1)), held = step(b, () => b.mergeBlock(idAt(b, 1)));
  ownA.push(step(a, () => a.splitBlock(idAt(a, 0), 0)));
  a.receive(remoteSplit);
  const blocks = a.document().aliveBlocks().length, before = shown(a);
  if (blocks < 4) { record({name: 'N-005 persistent-client form', preconditionReached: false, before, note: 'the recorded merge of block 3 does not exist here'}); return; }
  ownA.push(step(a, () => a.mergeBlock(idAt(a, 3))));
  a.receive(held); for (const t of ownA) b.receive(t);
  record({name: 'N-005 persistent-client form', contract: 'conservation: visible multiset x', before,
    demoPrecondition: ['', '', '', 'x'], preconditionReached: same(before, ['', '', '', 'x']),
    expected: 'x', actual: shown(a), visible: visible(a), converged: same(shown(a), shown(b)), contractHolds: visible(a) === 'x'});
});

// Sensitivity of the RA comparison: specification mutants must disagree with
// the same archives on which the specification agrees (for the design).
class MergeNoOp extends IdentitySpec { step(c) { return c.kind === 'merge' ? this : super.step(c); } }
class MergeSourceFirst extends IdentitySpec {
  step(c) {
    if (c.kind !== 'merge') return super.step(c);
    const s = this.live(c.source), t = this.live(c.target);
    if (!s || !t || s === t) return this;
    t.slots.unshift(...s.slots); s.slots = []; s.alive = false; return this;
  }
}
const sensitivity = [];
{
  const one = new Replica('A', 'A', seedBlocks(['ab', 'cd'])); one.mergeBlock(idAt(one, 1));
  const init = seedBlocks(['a', 'b', 'c']), p = new Replica('P', 'P', init), q = new Replica('Q', 'Q', init);
  const mp = p.mergeBlock(idAt(p, 1)).transaction, mq = q.mergeBlock(idAt(q, 2)).transaction; p.receive(mq);
  for (const [name, r] of [['merge ab|cd', one], ['merge b into a || merge c into b', p]]) {
    const txs = r.transactions(), display = displayOf(r.document());
    sensitivity.push({history: name, display, spec: compare(txs, display).category,
      mutants: {...Object.fromEntries([MergeNoOp, MergeSourceFirst].map(M => [M.name, compare(txs, display, {}, M).category])),
        skipMeaning: compare(txs, display, {merge: 'skip'}).category}});
  }
}
console.log(JSON.stringify({cases, sensitivity}));
