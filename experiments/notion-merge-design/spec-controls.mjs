// Hand-derived checks of the identity specification and decoder. No demo code
// is imported. Each check pins the intended value and, with a companion,
// rejects the tempting degenerate behaviour.
import assert from 'node:assert/strict';
import {IdentitySpec, SpecStuck, decode, fold} from './identity-spec.mjs';

const ins = (instance, origin, ...cs) => ({kind: 'insert', instance, origin, characters: cs.map(([id, text]) => ({id, text}))});
const base = (options) => new IdentitySpec(options)
  .step({kind: 'create', block: 'T', instance: 't'})
  .step(ins('t', 'start', ['t1', 'a'], ['t2', 'b']))
  .step({kind: 'create', block: 'S', instance: 's', after: 'T'})
  .step(ins('s', 'start', ['s1', 'c'], ['s2', 'd']));
let checks = 0;
const eq = (a, b) => { assert.deepEqual(a, b); checks++; };
const ne = (a, b) => { assert.notDeepEqual(a, b); checks++; };

// Merge concatenates target then source and leaves a tombstone in place.
{
  const d = base().step({kind: 'merge', source: 'S', target: 'T'});
  eq(d.view(), [['T', 'abcd']]);
  ne(d.view(), [['T', 'cdab']]);             // not source first
  ne(d.view(), [['T', 'ab'], ['S', 'cd']]);   // not a no-op
  eq(d.blocks.map(b => [b.id, b.alive, b.slots.length]), [['T', true, 6], ['S', false, 0]]);
  // Addresses stay unique: the source root slot is retained, invisible.
  const addresses = d.blocks.flatMap(b => b.slots.map(s => s.address));
  eq(new Set(addresses).size, addresses.length);
  eq(d.blocks[0].slots[3], {address: 's/start', value: '', visible: false});
}
// A merge into a merged-away target joins the block that absorbed it.
{
  const chain = options => base(options).step({kind: 'create', block: 'U', instance: 'u', after: 'S'})
    .step(ins('u', 'start', ['u1', 'e']))
    .step({kind: 'merge', source: 'S', target: 'T'})
    .step({kind: 'merge', source: 'U', target: 'S'});
  eq(chain().view(), [['T', 'abcde']]);
  ne(chain().view(), [['T', 'abcd'], ['U', 'e']]);              // not the skip meaning
  eq(chain({merge: 'skip'}).view(), [['T', 'abcd'], ['U', 'e']]); // the skip meaning
  ne(chain({merge: 'skip'}).view(), [['T', 'abcde']]);
}
// No-op cases: dead source, holder equal to the source (the cycle case), equal blocks.
{
  const d = base().step({kind: 'merge', source: 'S', target: 'T'});
  eq(d.clone().step({kind: 'merge', source: 'S', target: 'T'}).view(), [['T', 'abcd']]);
  eq(d.clone().step({kind: 'merge', source: 'T', target: 'S'}).view(), [['T', 'abcd']]);
  ne(d.clone().step({kind: 'merge', source: 'T', target: 'S'}).view(), []);
  eq(base().step({kind: 'merge', source: 'T', target: 'T'}).view(), [['T', 'ab'], ['S', 'cd']]);
}
// Create after a tombstone lands at the tombstone's position.
{
  const d = base().step({kind: 'create', block: 'V', instance: 'v'})   // V first
    .step({kind: 'merge', source: 'S', target: 'T'})
    .step({kind: 'create', block: 'N', instance: 'n', after: 'S'});
  eq(d.view(), [['V', ''], ['T', 'abcd'], ['N', '']]);
  ne(d.view(), [['N', ''], ['V', ''], ['T', 'abcd']]);
  // The original reading (source leaves the list) gives this history no meaning.
  const r = base({removeMergedSource: true}).step({kind: 'merge', source: 'S', target: 'T'});
  assert.throws(() => r.step({kind: 'create', block: 'N', instance: 'n', after: 'S'}), SpecStuck); checks++;
}
// Split and insert after a merge address the absorbing block.
{
  const d = base().step({kind: 'merge', source: 'S', target: 'T'})
    .step({kind: 'create', block: 'N', instance: 'n', after: 'S'})
    .step({kind: 'split', instance: 's', origin: 's1', marker: 'm', target: 'N'})
    .step(ins('s', 'start', ['x', 'X']));
  eq(d.view(), [['T', 'abXc'], ['N', 'd']]);
  ne(d.view(), [['T', 'ab'], ['N', 'Xcd']]);
  // Deletion across the merged boundary hides exactly the targets.
  eq(base().step({kind: 'merge', source: 'S', target: 'T'})
    .step({kind: 'delete', instance: 't', ids: ['t2']}).step({kind: 'delete', instance: 's', ids: ['s1']}).view(), [['T', 'ad']]);
}
// Atomic groups leave the document unchanged when stuck.
{
  const d = base();
  assert.throws(() => d.group([{kind: 'create', block: 'W', instance: 'w', after: 'T'},
    {kind: 'split', instance: 'q', origin: 'nowhere', marker: 'm', target: 'W'}]), SpecStuck);
  eq(d.view(), [['T', 'ab'], ['S', 'cd']]);
}
// Decoder: the demo's three-operation merge, the design's single operation and
// the control's operation pair all mean `merge source target`.
{
  const id = {sessionId: 'A', counter: 9};
  const demo = {id, operations: [
    {command: 'splitText', args: {textInstanceId: 's', id, originId: 'start'}},
    {command: 'moveTextSlice', args: {textInstanceId: 's', textSliceStartItemId: id, targetBlockId: 'T'}},
    {command: 'removeBlock', args: {blockId: 'S'}}]};
  const design = {id, operations: [{command: 'mergeBlock', args: {sourceBlockId: 'S', targetBlockId: 'T'}}]};
  const both = {id, operations: [...design.operations, {command: 'removeBlock', args: {blockId: 'S'}}]};
  for (const t of [demo, design, both]) eq(decode(t), [{kind: 'merge', source: 'S', target: 'T'}]);
  const run = {id: {sessionId: 'B', counter: 4}, operations: [{command: 'insertText', args: {textInstanceId: 't', id: {sessionId: 'B', counter: 4}, originId: {sessionId: 'A', counter: 2}, content: 'xy'}}]};
  eq(decode(run), [{kind: 'insert', instance: 't', origin: 'A:2', characters: [{id: 'B:4', text: 'x'}, {id: 'B:5', text: 'y'}]}]);
  ne(decode(run)[0].characters.map(c => c.id), ['B:4', 'B:4']);
}
// Replay order: counter first, then session.
{
  const tx = (sessionId, counter, ops) => ({id: {sessionId, counter}, operations: ops});
  const create = (b, after) => ({command: 'createBlock', args: {blockId: b, titleTextInstanceId: b, afterBlockId: after}});
  const archive = [tx('B', 2, [create('Y', 'R')]), tx('A', 2, [create('X', 'R')]), tx('A', 1, [create('R')])];
  eq(fold(archive).view, [['R', ''], ['Y', ''], ['X', '']]);
  // Through the decoder and atomic groups: X joins R, then Y joins X's holder R.
  const mergeTx = (sessionId, counter, source, target) => tx(sessionId, counter, [{command: 'mergeBlock', args: {sourceBlockId: source, targetBlockId: target}}]);
  const merged = [...archive, mergeTx('A', 3, 'X', 'R'), mergeTx('A', 4, 'Y', 'X')];
  eq(fold(merged).view, [['R', '']]);
  ne(fold(merged).view, [['R', ''], ['Y', '']]);
  eq(fold(merged, {merge: 'skip'}).view, [['R', ''], ['Y', '']]);
  ne(fold(archive).view, [['R', ''], ['X', ''], ['Y', '']]);
}
// sliceFollow: the merge follows the anchor recorded at issue time.
{
  const SF = {merge: 'sliceFollow'}, SA = {merge: 'sliceFollow', placement: 'anchor'};
  const m = (source, target, instance, end) => ({kind: 'merge', source, target, anchor: {instance, end}});
  // An unsplit target is anchored at the end of its instance.
  eq(base(SF).step(m('S', 'T', 't', 'end')).view(), [['T', 'abcd']]);
  ne(base(SF).step(m('S', 'T', 't', 'end')).view(), [['T', 'ab'], ['S', 'cd']]);
  // End slots are invisible and addresses stay unique.
  const d = base(SF).step(m('S', 'T', 't', 'end'));
  eq(d.addresses(), ['t/start', 't/t1', 't/t2', 't/^end', 's/start', 's/s1', 's/s2', 's/^end']);
  ne(d.addresses(), ['t/start', 't/t1', 't/t2', 's/start', 's/s1', 's/s2']);
  // The review's case: split T after a, then the merge anchored at T's end. The
  // end of instance t now lies in the split-off block F, so S follows b.
  const review = options => base(options).step({kind: 'create', block: 'F', instance: 'f', after: 'T'})
    .step({kind: 'split', instance: 't', origin: 't1', marker: 'm', target: 'F'})
    .step(m('S', 'T', 't', 'end'));
  eq(review(SF).view(), [['T', 'a'], ['F', 'bcd']]);
  ne(review(SF).view(), [['T', 'acd'], ['F', 'b']]);   // the absorb meaning
  eq(review().view(), [['T', 'acd'], ['F', 'b']]);       // absorb ignores the anchor
  ne(review().view(), [['T', 'a'], ['F', 'bcd']]);
  // A marker anchor is the position before the marker, not the marker's slot:
  // abc split after a into F, then F merged back into T, anchored at m.
  const back = new IdentitySpec(SF).step({kind: 'create', block: 'T', instance: 't'})
    .step(ins('t', 'start', ['t1', 'a'], ['t2', 'b'], ['t3', 'c']))
    .step({kind: 'create', block: 'F', instance: 'f', after: 'T'})
    .step({kind: 'split', instance: 't', origin: 't1', marker: 'm', target: 'F'});
  eq(back.view(), [['T', 'a'], ['F', 'bc']]);
  eq(back.clone().step(m('F', 'T', 't', 'm')).view(), [['T', 'abc']]);
  ne(back.clone().step(m('F', 'T', 't', 'm')).view(), [['T', 'a'], ['F', 'bc']]);  // slot m is in F: a no-op
  // A holder that absorbed U after the anchor: both merges anchored at T's end.
  const two = options => base(options).step({kind: 'create', block: 'U', instance: 'u', after: 'T'})
    .step(ins('u', 'start', ['u1', 'Z']))
    .step(m('U', 'T', 't', 'end')).step(m('S', 'T', 't', 'end'));
  eq(two(SF).view(), [['T', 'abZcd']]);
  ne(two(SF).view(), [['T', 'abcdZ']]);
  eq(two(SA).view(), [['T', 'abcdZ']]);
  ne(two(SA).view(), [['T', 'abZcd']]);
  // A third merge anchored at U's end lands at the holder's end, or right
  // after U's slots, depending on the placement.
  const three = options => two(options).step({kind: 'create', block: 'V', instance: 'v', after: 'T'})
    .step(ins('v', 'start', ['v1', 'W'])).step(m('V', 'T', 'u', 'end'));
  eq(three(SF).view(), [['T', 'abZcdW']]);
  ne(three(SF).view(), [['T', 'abZWcd']]);
  eq(three(SA).view(), [['T', 'abcdZW']]);
  ne(three(SA).view(), [['T', 'abcdWZ']]);
  // No-ops: the anchor held by the source (the cycle case) and a dead source.
  const merged = base(SF).step(m('S', 'T', 't', 'end'));
  eq(merged.clone().step(m('T', 'S', 's', 'end')).view(), [['T', 'abcd']]);
  ne(merged.clone().step(m('T', 'S', 's', 'end')).view(), []);
  eq(merged.clone().step(m('S', 'T', 't', 'end')).view(), [['T', 'abcd']]);
  ne(merged.clone().step(m('S', 'T', 't', 'end')).view(), [['T', 'abcdcd']]);
  // Without an anchor the mode gives the merge no meaning.
  assert.throws(() => base(SF).step({kind: 'merge', source: 'S', target: 'T'}), SpecStuck); checks++;
  // Decoder: the anchor is carried when the transaction records it.
  const id = {sessionId: 'A', counter: 9}, args = {sourceBlockId: 'S', targetBlockId: 'T', targetTextInstanceId: 't'};
  eq(decode({id, operations: [{command: 'mergeBlock', args: {...args, targetTextSliceEndItemId: 'end'}}]}),
    [{kind: 'merge', source: 'S', target: 'T', anchor: {instance: 't', end: 'end'}}]);
  eq(decode({id, operations: [{command: 'mergeBlock', args: {...args, targetTextSliceEndItemId: {sessionId: 'B', counter: 5}}}]})[0].anchor,
    {instance: 't', end: 'B:5'});
  ne(decode({id, operations: [{command: 'mergeBlock', args: {...args, targetTextSliceEndItemId: 'end'}}]}),
    [{kind: 'merge', source: 'S', target: 'T'}]);
}
console.log(JSON.stringify({specControls: 'passed', checks}));
