/**
 * Hand-derived tests of the specification (spec.js) and the decoder
 * (decode.js). No Notion code is loaded: the commands and operations below
 * are literals in the formats the specification and the production wire
 * protocol define. Every expected view is derived by hand from the command
 * rules in spec.js; each equality has a companion inequality against the
 * tempting wrong answer.
 *
 *   node --test ra-pbt/instances/notion-production-blocks/spec.test.js
 */
import assert from 'node:assert/strict';
import { test } from 'node:test';
import { foldGroups, specFor, localEdit, textsOf, blocksOf } from './spec.js';
import { decodeOps } from './decode.js';

const texts = (state) => textsOf(specFor({ seedGroups: [] }).view(state));
const bolds = (state) => blocksOf(specFor({ seedGroups: [], format: true }).view(state)).map((cs) => cs.map((c) => (c.bold ? `[${c.text}]` : c.text)).join(''));
const chars = (s, ...ids) => [...s].map((text, i) => ({ id: ids[i], text }));

// Block b1 (instance I) holding abc, as a seed creates it.
const seedAbc = [
  [{ kind: 'create', block: 'b1', instance: 'I' }],
  [{ kind: 'insert', instance: 'I', origin: 'start', characters: chars('abc', 's:1', 's:2', 's:3') }],
];
// Split of b1 after a into b2 (instance J): the builder's create then split.
const splitAfterA = [
  { kind: 'create', block: 'b2', instance: 'J', after: 'b1' },
  { kind: 'split', instance: 'I', origin: 's:1', marker: 'A:4', target: 'b2' },
];

test('insertion places the run after its origin', () => {
  const s = foldGroups(seedAbc);
  assert.deepEqual(texts(s), ['abc']);
  assert.notDeepEqual(texts(s), ['']);
  assert.notDeepEqual(texts(s), ['cba']);
});

test('split moves exactly the suffix into the new following block', () => {
  const s = foldGroups([...seedAbc, splitAfterA]);
  assert.deepEqual(texts(s), ['a', 'bc']);
  assert.notDeepEqual(texts(s), ['abc', '']);
  assert.notDeepEqual(texts(s), ['a', 'b']);
  assert.notDeepEqual(texts(s), ['bc', 'a']);
});

test('merge appends the source to the holder of its anchor and removes the source', () => {
  const merge = [
    { kind: 'mark', instance: 'J', origin: 'start', marker: 'A:30' },
    { kind: 'merge', source: 'b2', target: 'b1', anchor: { instance: 'I', end: 'A:4' } },
  ];
  const s = foldGroups([...seedAbc, splitAfterA, merge]);
  assert.deepEqual(texts(s), ['abc']);
  assert.notDeepEqual(texts(s), ['a']);
  assert.notDeepEqual(texts(s), ['a', 'bc']);
  assert.notDeepEqual(texts(s), ['bca']);
  // A second merge of the removed source changes nothing (no duplicated text).
  const again = foldGroups([...seedAbc, splitAfterA, merge, merge]);
  assert.deepEqual(texts(again), ['abc']);
  assert.notDeepEqual(texts(again), ['abcbc']);
});

test('a merge whose anchor lies in the source is a no-op that keeps the source', () => {
  // After the split, I/^end is in b2: merging b2 anchored at (I, end) targets itself.
  const s = foldGroups([...seedAbc, splitAfterA, [{ kind: 'merge', source: 'b2', target: 'b1', anchor: { instance: 'I', end: 'end' } }]]);
  assert.deepEqual(texts(s), ['a', 'bc']);
  assert.notDeepEqual(texts(s), ['a']);
  assert.notDeepEqual(texts(s), ['abc']);
});

test('splitAt moves the slots from an existing marker to the end of its holder', () => {
  const s = foldGroups([...seedAbc, splitAfterA, [{ kind: 'create', block: 'b3', instance: 'K', after: 'b2' }, { kind: 'splitAt', instance: 'I', start: 'A:4', target: 'b3' }]]);
  assert.deepEqual(texts(s), ['a', '', 'bc']);
  assert.notDeepEqual(texts(s), ['a', 'bc', '']);
  assert.notDeepEqual(texts(s), ['a', '', '']);
});

test('split placement: after the holder of the split point, or after the issuer source', () => {
  // b1 = a (I), b2 = b (J), b4 = z (Z). Merge b2 into b1 (ab), create b5 after b1,
  // then a split of b before its first character issued on b2 (now a tombstone).
  const groups = [
    [{ kind: 'create', block: 'b1', instance: 'I' }],
    [{ kind: 'insert', instance: 'I', origin: 'start', characters: chars('a', 's:1') }],
    [{ kind: 'create', block: 'b2', instance: 'J', after: 'b1' }],
    [{ kind: 'insert', instance: 'J', origin: 'start', characters: chars('b', 't:1') }],
    [{ kind: 'create', block: 'b4', instance: 'Z', after: 'b2' }],
    [{ kind: 'insert', instance: 'Z', origin: 'start', characters: chars('z', 'u:1') }],
    [{ kind: 'merge', source: 'b2', target: 'b1', anchor: { instance: 'I', end: 'end' } }],
    [{ kind: 'create', block: 'b5', instance: 'Y', after: 'b1' }],
    [{ kind: 'create', block: 'b3', instance: 'K', after: 'b2' }, { kind: 'split', instance: 'J', origin: 'start', marker: 'C:9', target: 'b3' }],
  ];
  const holder = foldGroups(groups, { splitPlacement: 'holder' });
  const source = foldGroups(groups, { splitPlacement: 'source' });
  assert.deepEqual(texts(holder), ['a', 'b', '', 'z']);
  assert.deepEqual(texts(source), ['a', '', 'b', 'z']);
  assert.notDeepEqual(texts(holder), texts(source));
});

test('inserted characters inherit bold from the left neighbour in the applied state, or as issued', () => {
  const groups = [...seedAbc, [{ kind: 'bold', addresses: ['I/s:1'], value: true }], [{ kind: 'insert', instance: 'I', origin: 's:1', characters: chars('X', 'B:7'), bold: false }]];
  assert.deepEqual(bolds(foldGroups(groups, { inherit: 'apply' })), ['[a][X]bc']);
  assert.deepEqual(bolds(foldGroups(groups, { inherit: 'issue' })), ['[a]Xbc']);
  // At the block start there is no left neighbour: plain under either reading.
  const atStart = [...seedAbc, [{ kind: 'bold', addresses: ['I/s:1'], value: true }], [{ kind: 'insert', instance: 'I', origin: 'start', characters: chars('Y', 'B:8') }]];
  assert.deepEqual(bolds(foldGroups(atStart)), ['Y[a]bc']);
  assert.notDeepEqual(bolds(foldGroups(atStart)), ['[Y][a]bc']);
});

test('bold sets exactly the addressed characters', () => {
  const s = foldGroups([...seedAbc, splitAfterA, [{ kind: 'bold', addresses: ['I/s:1', 'I/s:3'], value: true }]]);
  assert.deepEqual(bolds(s), ['[a]', 'b[c]']);
  assert.notDeepEqual(bolds(s), ['[a]', '[b][c]']);
  assert.notDeepEqual(bolds(s), ['a', 'bc']);
});

test('commands without meaning make the history stuck', () => {
  const spec = specFor({ seedGroups: seedAbc });
  // Split into a block that does not exist.
  assert.equal(spec.apply(spec.init(), { commands: [{ kind: 'split', instance: 'I', origin: 's:1', marker: 'A:4', target: 'nowhere' }] }), null);
  // Insert after an origin nobody holds.
  assert.equal(spec.apply(spec.init(), { commands: [{ kind: 'insert', instance: 'I', origin: 'Q:9', characters: chars('X', 'B:1') }] }), null);
  // A meaningful group is not stuck.
  assert.notEqual(spec.apply(spec.init(), { commands: splitAfterA }), null);
});

test('a command group is atomic', () => {
  const spec = specFor({ seedGroups: seedAbc });
  const next = spec.apply(spec.init(), { commands: [{ kind: 'create', block: 'b2', instance: 'J', after: 'b1' }, { kind: 'split', instance: 'I', origin: 'Q:9', marker: 'A:4', target: 'b2' }] });
  assert.equal(next, null);
  assert.deepEqual(texts(spec.init()), ['abc']);
});

test('local meaning of create, insert with inheritance, split, merge and bold', () => {
  const v = [[{ text: 'a', bold: true }, { text: 'b', bold: false }], []];
  assert.deepEqual(textsOf(localEdit(v, { kind: 'create', after: 0 })), ['ab', '', '']);
  assert.notDeepEqual(textsOf(localEdit(v, { kind: 'create', after: 0 })), ['ab', '']);
  const ins = localEdit(v, { kind: 'insert', block: 0, index: 1, text: 'X' });
  assert.deepEqual(ins[0].map((c) => c.bold), [true, true, false]);
  assert.notDeepEqual(ins[0].map((c) => c.bold), [true, false, false]);
  const ins0 = localEdit(v, { kind: 'insert', block: 0, index: 0, text: 'Y' });
  assert.deepEqual(ins0[0].map((c) => c.bold), [false, true, false]);
  assert.deepEqual(textsOf(localEdit(v, { kind: 'split', block: 0, index: 1 })), ['a', 'b', '']);
  assert.notDeepEqual(textsOf(localEdit(v, { kind: 'split', block: 0, index: 1 })), ['ab', '', '']);
  assert.deepEqual(textsOf(localEdit(v, { kind: 'merge', block: 1 })), ['ab']);
  assert.notDeepEqual(textsOf(localEdit(v, { kind: 'merge', block: 1 })), ['ab', '']);
  // Bold toggles: remove when every selected character is bold, otherwise add.
  assert.deepEqual(localEdit(v, { kind: 'bold', block: 0, start: 0, end: 1 })[0].map((c) => c.bold), [false, false]);
  assert.deepEqual(localEdit(v, { kind: 'bold', block: 0, start: 0, end: 2 })[0].map((c) => c.bold), [true, true]);
});

// Production wire operations, in the formats the shipped builders emit.
const P = (id) => ({ table: 'block', id, spaceId: 'sp' });
const value = (id, instance) => ({ id, alive: true, crdt_data: { title: { r: 'root', n: { root: { s: { x: instance, i: [{ t: 's' }, { t: 'e' }], l: '' }, c: [] } } } } });

test('decoding a split: create, sibling moves ignored, split into the new block', () => {
  const ops = [
    { command: 'set', pointer: P('b2'), path: [], args: value('b2', 'J') },
    { command: 'listAfter', pointer: P('page'), path: ['content'], args: { id: 'b2', after: 'b1' } },
    { command: 'moveTextSlice', pointer: P('b1'), path: [], args: { textInstanceId: 'I', sourceSearchLabel: 'l', textSliceStartItemId: ['B', 9], targetBlockId: 'b1', targetTextInstanceId: 'I', targetSearchLabel: 'L', targetTextSliceEndItemId: ['B', 9] } },
    { command: 'splitText', pointer: P('b1'), path: [], args: { textInstanceId: 'I', searchLabel: '', id: ['A', 4], originId: ['s', 1] } },
    { command: 'moveTextSliceIntoBlock', pointer: P('b1'), path: [], args: { textInstanceId: 'I', textSliceStartItemId: ['A', 4], sourceSearchLabel: '', targetBlockId: 'b2' } },
  ];
  assert.deepEqual(decodeOps(ops, { pageId: 'page' }), [
    { kind: 'create', block: 'b2', instance: 'J', after: 'b1' },
    { kind: 'split', instance: 'I', origin: 's:1', marker: 'A:4', target: 'b2' },
  ]);
});

test('decoding a split at the end of a slice-tree node gives splitAt', () => {
  const ops = [
    { command: 'set', pointer: P('b3'), path: [], args: value('b3', 'K') },
    { command: 'listAfter', pointer: P('page'), path: ['content'], args: { id: 'b3', after: 'b2' } },
    { command: 'moveTextSliceIntoBlock', pointer: P('b2'), path: [], args: { textInstanceId: 'I', textSliceStartItemId: ['A', 4], sourceSearchLabel: 'l', targetBlockId: 'b3' } },
  ];
  const out = decodeOps(ops, { pageId: 'page' });
  assert.deepEqual(out[1], { kind: 'splitAt', instance: 'I', start: 'A:4', target: 'b3' });
  assert.notEqual(out[1].kind, 'split');
});

test('decoding a merge: mark, then merge with the anchor; removal belongs to the merge', () => {
  const ops = [
    { command: 'splitText', pointer: P('b2'), path: [], args: { textInstanceId: 'J', searchLabel: '', id: ['A', 30], originId: 'start' } },
    { command: 'moveTextSlice', pointer: P('b2'), path: [], args: { textInstanceId: 'J', textSliceStartItemId: ['A', 30], sourceSearchLabel: '', targetBlockId: 'b1', targetTextInstanceId: 'I', targetSearchLabel: 'L', targetTextSliceEndItemId: ['A', 4], isMerge: true } },
    { command: 'set', pointer: P('b2'), path: ['alive'], args: false },
    { command: 'listRemove', pointer: P('page'), path: ['content'], args: { id: 'b2' } },
  ];
  assert.deepEqual(decodeOps(ops, { pageId: 'page' }), [
    { kind: 'mark', instance: 'J', origin: 'start', marker: 'A:30' },
    { kind: 'merge', source: 'b2', target: 'b1', anchor: { instance: 'I', end: 'A:4' } },
  ]);
  // A removal without a merge has no meaning in the specification.
  assert.throws(() => decodeOps(ops.slice(2), { pageId: 'page' }), /removal without a merge/);
});

test('decoding an insertion keys each character of the run', () => {
  const ops = [{ command: 'insertText', pointer: P('b1'), path: [], args: { textInstanceId: 'I', searchLabel: 'l', id: ['B', 7], originId: ['A', 4], content: 'XY' } }];
  const [c] = decodeOps(ops, { pageId: 'page', insertBold: true });
  assert.deepEqual(c.characters, [{ id: 'B:7', text: 'X' }, { id: 'B:8', text: 'Y' }]);
  assert.notDeepEqual(c.characters, [{ id: 'B:7', text: 'X' }, { id: 'B:7', text: 'Y' }]);
  assert.equal(c.origin, 'A:4');
  assert.equal(c.bold, true);
});
