// Directed fixtures transcribed from the independently validated Python read
// model. These gate the benchmark's Peritext observable before timing it.

import assert from 'node:assert/strict';
import { peritext } from '../../runtime/src/datatypes/peritext.js';

const ins = (id, el, anchorId) => ({ type: 'ins', id, el, anchorId });
const del = (id) => ({ type: 'del', id });
const mark = (mid, mtype, startId, endId, startSide = 'before', endSide = 'after') =>
  ({ type: 'addMark', mid, mtype, startId, endId, startSide, endSide });
const build = (ops) => ops.reduce((s, op) => peritext.apply(s, op), peritext.init());

const bold = build([ins(1, 'a', null), ins(2, 'b', 1), ins(3, 'z', 2),
  mark(4, 'bold', 1, 2, 'before', 'after'), ins(5, 'x', 2)]);
const link = build([ins(1, 'a', null), ins(2, 'b', 1), ins(3, 'z', 2),
  mark(4, 'link', 1, 3, 'before', 'before'), ins(5, 'x', 2)]);
assert.deepEqual(peritext.flags(bold, 'bold'),
  [['a', true], ['b', true], ['x', true], ['z', false]]);
assert.deepEqual(peritext.flags(link, 'link'),
  [['a', true], ['b', true], ['x', false], ['z', false]]);
assert.notDeepEqual(peritext.flags(bold, 'bold'), peritext.flags(link, 'link'),
  'FAIL control: gravity modes must remain distinguishable');

const rehome = build([ins(1, 'W', null), ins(2, 'A', 1), ins(3, 'B', 2), ins(4, 'C', 3),
  mark(100, 'bold', 2, 3), del(2)]);
assert.deepEqual(peritext.flags(rehome, 'bold'),
  [['W', false], ['B', true], ['C', false]]);
assert.notDeepEqual(peritext.flags(rehome, 'bold'),
  [['W', true], ['B', true], ['C', false]],
  'FAIL control: deleting the start must not leak the mark backward');
console.log('Peritext semantic PASS/FAIL fixtures validated');
