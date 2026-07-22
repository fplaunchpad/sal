// Rich-text binding tests (task #107): editor gestures -> peritext ops, applied
// through the BATCHED path (peritext.applyBatch, proven == folding apply) and
// through a real DistributedReplica.
//
// Expected values are HAND-DERIVED from the datatype's documented semantics
// (peritext.test.js Ex1/Ex2/Ex7 and the LWW-by-mid rule), NOT read back from the
// binding under test. Char ids come from the test's own monotonic mint (100..),
// so reading-order = insertion-order for a single author is asserted, not
// assumed. Each PASS carries a FAIL companion pinning the tempting degenerate
// (empty/reversed read, a constant all-set, the non-growing gravity, a silent
// add-wins, a mark lost across a delete).

import test from 'node:test';
import assert from 'node:assert/strict';
import { peritext } from '../../runtime/src/datatypes/peritext.js';
import { DistributedReplica } from '../../runtime/src/replica.js';
import {
  textEditOps, formatOps, commitOps, typeEdit, format, selectionHas, coveringMarkTypes, markSpan, specRead,
} from '../src/peritextbind.js';

const batch = (s, ops) => peritext.applyBatch(s, ops); // the batched apply a gesture seals
const txt = (s) => peritext.read(s).map((e) => e.char).join('');
const ids = (s) => peritext.read(s).map((e) => e.id);
const flags = (s, mt) => peritext.flags(s, mt);
const counter = (start) => { let n = start; return () => n++; };

test('typeEdit into an empty doc: reading order reproduces the text', () => {
  const mint = counter(100);
  const s = batch(peritext.init(), textEditOps([], '', 'hello', mint));
  assert.equal(txt(s), 'hello');
  assert.deepEqual(ids(s), [100, 101, 102, 103, 104], 'single-author order = insertion order');
  // FAIL companions: not the empty read, not reversed.
  assert.notEqual(txt(s), '');
  assert.notEqual(txt(s), 'olleh');
});

test('bold a middle selection: only the selected chars carry bold', () => {
  const mint = counter(100);
  let s = batch(peritext.init(), textEditOps([], '', 'abcd', mint)); // ids 100..103
  s = batch(s, formatOps([100, 101, 102, 103], 1, 3, 'bold', mint)); // mid 104, covers b,c
  assert.deepEqual(flags(s, 'bold'), [['a', false], ['b', true], ['c', true], ['d', false]]);
  // FAIL companions: not a constant all-set, not the wrong span.
  assert.notDeepEqual(flags(s, 'bold'), [['a', true], ['b', true], ['c', true], ['d', true]]);
  assert.notDeepEqual(flags(s, 'bold'), [['a', true], ['b', false], ['c', false], ['d', false]]);
});

test('bold grows at its end over text typed after it (Ex7 via the binding)', () => {
  const mint = counter(100);
  let s = batch(peritext.init(), textEditOps([], '', 'ab', mint)); // 100 a, 101 b
  s = batch(s, formatOps([100, 101], 0, 2, 'bold', mint));         // mid 102, ts 102
  s = batch(s, textEditOps([100, 101], 'ab', 'abX', mint));        // X id 103 > ts 102 -> newer
  assert.equal(txt(s), 'abX');
  assert.deepEqual(flags(s, 'bold'), [['a', true], ['b', true], ['X', true]], 'X newer than mark: grabbed');
  // FAIL companion: growth is real, not the non-growing degenerate.
  assert.notDeepEqual(flags(s, 'bold'), [['a', true], ['b', true], ['X', false]]);
});

test('removeMark un-bolds, wins by higher mid, and is directed', () => {
  const mint = counter(100);
  let s = batch(peritext.init(), textEditOps([], '', 'ab', mint));            // 100 a, 101 b
  s = batch(s, formatOps([100, 101], 0, 2, 'bold', mint));                    // add, mid 102
  s = batch(s, formatOps([100, 101], 0, 2, 'bold', mint, { remove: true }));  // remove, mid 103 > 102
  assert.deepEqual(flags(s, 'bold'), [['a', false], ['b', false]], 'higher-mid remove wins');
  // FAIL companion: the earlier add did NOT silently win.
  assert.notDeepEqual(flags(s, 'bold'), [['a', true], ['b', true]]);

  // directed: removing only [1,2) leaves a bold (not a constant clear).
  const m2 = counter(100);
  let t = batch(peritext.init(), textEditOps([], '', 'ab', m2));              // 100 a, 101 b
  t = batch(t, formatOps([100, 101], 0, 2, 'bold', m2));                      // add, mid 102
  t = batch(t, formatOps([100, 101], 1, 2, 'bold', m2, { remove: true }));    // remove b only, mid 103
  assert.deepEqual(flags(t, 'bold'), [['a', true], ['b', false]]);
  assert.notEqual(JSON.stringify(flags(t, 'bold')), JSON.stringify(flags(s, 'bold')));
});

test('delete-in-the-middle: text reconciles and surviving chars keep their mark', () => {
  const mint = counter(100);
  let s = batch(peritext.init(), textEditOps([], '', 'hello', mint));        // ids 100..104
  s = batch(s, formatOps([100, 101, 102, 103, 104], 0, 5, 'bold', mint));    // mid 105, covers h..o
  s = batch(s, textEditOps([100, 101, 102, 103, 104], 'hello', 'heo', mint)); // del the two l's
  assert.equal(txt(s), 'heo');
  assert.deepEqual(flags(s, 'bold'), [['h', true], ['e', true], ['o', true]], 'survivors stay bold');
  // FAIL companions: the edit applied, and the mark was not lost.
  assert.notEqual(txt(s), 'hello');
  assert.notDeepEqual(flags(s, 'bold'), [['h', false], ['e', false], ['o', false]]);
});

test('through a real DistributedReplica: gestures drive the live document', () => {
  const node = new DistributedReplica(peritext, 'A');
  const mint = counter(1000);
  typeEdit(node, 'hello', mint);
  assert.equal(node.read().map((e) => e.char).join(''), 'hello');

  format(node, 0, 5, 'bold', mint);
  assert.equal(selectionHas(node.read(), 0, 5, 'bold'), true, 'the selection is bold');
  // FAIL companion: only bold was applied, not a constant-true over every mtype.
  assert.equal(selectionHas(node.read(), 0, 5, 'italic'), false);

  format(node, 0, 5, 'bold', mint, { remove: true });
  assert.equal(selectionHas(node.read(), 0, 5, 'bold'), false, 'toggle off clears it');
});

test('link and comments: exclusive-end gravity and the unique-mtype encoding', () => {
  const mint = counter(100);
  let s = batch(peritext.init(), textEditOps([], '', 'abcd', mint)); // ids 100..103
  // link over [1,3) = b,c: exclusive end anchors BEFORE 'd' (ids[3]=103)
  s = batch(s, formatOps(ids(s), 1, 3, 'link', mint, { value: 'http://x', endSide: 'before' }));
  assert.deepEqual(flags(s, 'link'),
    [['a', false], ['b', true], ['c', true], ['d', false]], 'the selection, exactly');
  // the exclusive end does NOT grow: type 'e' after 'd', then even INSIDE the
  // window nothing new is grabbed at the end boundary
  s = batch(s, textEditOps(ids(s), 'abcd', 'abcde', mint));
  assert.deepEqual(flags(s, 'link'),
    [['a', false], ['b', true], ['c', true], ['d', false], ['e', false]],
    'a link never grows (Ex8 gravity through the binding)');

  // two OVERLAPPING comments as unique mtypes: both live on the overlap
  const i0 = ids(s);
  s = batch(s, formatOps(i0, 0, 3, 'comment:x1', mint, { value: 'note one', endSide: 'before' }));
  s = batch(s, formatOps(ids(s), 1, 5, 'comment:x2', mint, { value: 'note two', endSide: 'before' }));
  const doc = peritext.read(s);
  assert.deepEqual(coveringMarkTypes(doc, 1, 3, 'comment:'), ['comment:x1', 'comment:x2'],
    'the overlap [1,3) is covered by BOTH comments');
  assert.deepEqual(markSpan(doc, 'comment:x1'), [0, 3], 'x1 spans a..c');
  assert.deepEqual(markSpan(doc, 'comment:x2'), [1, 5], 'x2 spans b..e');
  // FAIL companions: no comment covers ALL of [0,5); a span query for a
  // never-minted comment is null, not [0,0].
  assert.deepEqual(coveringMarkTypes(doc, 0, 5, 'comment:'), []);
  assert.equal(markSpan(doc, 'comment:zzz'), null);
});

test('debounce buffer: specRead shows the run, ONE flush commit reproduces it', () => {
  const mint = counter(100);
  const node = new DistributedReplica(peritext, 'E');
  const dagBefore = node.dag.size;

  // a typing run buffered keystroke by keystroke, each diffed against specRead
  const pending = [];
  for (const text of ['h', 'he', 'hel', 'hell', 'hello']) {
    const doc = specRead(node, pending);
    pending.push(...textEditOps(doc.map((e) => e.id), doc.map((e) => e.char).join(''), text, mint));
  }

  // FAIL companion (the speculation): the display sees the run, the DAG does not
  assert.equal(specRead(node, pending).map((e) => e.char).join(''), 'hello', 'spec shows the run');
  assert.equal(node.read().map((e) => e.char).join(''), '', 'nothing committed yet');
  assert.equal(node.dag.size, dagBefore, 'no commits while buffering');

  // flush: the WHOLE run is ONE commit, and the doc is exactly the spec
  commitOps(node, pending.splice(0));
  assert.equal(node.dag.size, dagBefore + 1, 'one commit for the run');
  assert.equal(node.read().map((e) => e.char).join(''), 'hello', 'flush reproduces the spec');

  // and it equals the per-keystroke twin (same ops, one commit each)
  const twinMint = counter(100);
  const twin = new DistributedReplica(peritext, 'E'); // same name -> same seq/ids
  for (const text of ['h', 'he', 'hel', 'hell', 'hello']) {
    const doc = twin.read();
    for (const op of textEditOps(doc.map((e) => e.id), doc.map((e) => e.char).join(''), text, twinMint)) {
      twin.commit(op);
    }
  }
  assert.deepEqual(node.read(), twin.read(), 'batched run == per-keystroke fold');
  assert.equal(twin.dag.size, dagBefore + 5, 'the twin paid five commits for it');
});
