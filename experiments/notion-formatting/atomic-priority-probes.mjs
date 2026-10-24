import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {idKey} from './ids.js';
import {atomicToggle, view, nonemptyView, byIdentity, identity} from './atomic-priority-adapter.mjs';

const rows = [];
const block = (replica, at = 0) => replica.document().aliveBlocks()[at].id;
function fresh(text = 'abc') {
  const replica = new Replica('S', 'S', []), root = replica.createBlock().newBlockId;
  replica.insertText(root, 0, text);
  return replica;
}
function check(name, replica, expected, rejected, extra = {}) {
  const actual = view(replica);
  assert.deepEqual(actual, expected, name);
  assert.notDeepEqual(actual, rejected, `${name}: negative control`);
  rows.push({name, expected, rejected, actual, controlsHold: true, ...extra});
}
function receiver(base, archives) {
  const replica = new Replica('R', 'R', base);
  for (const archive of archives) for (const transaction of archive) replica.receive(transaction);
  return replica;
}

// Existing fracture: public edits establish the gapped selection and normal
// source clocks. Expected repaired result is the atomic A-before-B assignment.
{
  const seed = fresh('abcde'), root = block(seed);
  seed.toggleBold(root, 1, 4);
  const base = seed.transactions(), A = new Replica('A', 'A', base),
    B = new Replica('B', 'B', base), C = new Replica('C', 'C', base);
  const splitA = A.splitBlock(root, 2), splitC = C.splitBlock(root, 3);
  A.receive(splitC.transaction);
  A.mergeBlock(splitC.newBlockId);
  A.createBlock();
  for (let i = 0; i < 3; i++) B.createBlock();
  const add = atomicToggle(A, root, 0, 4), remove = atomicToggle(B, root, 1, 4);
  assert.equal(add.selectedText, 'abde'); assert.equal(remove.selectedText, 'bcd');
  assert.equal(add.value, true); assert.equal(remove.value, false);
  assert.deepEqual(add.segmentIds.map(idKey), ['A:11','A:12']);
  assert.deepEqual(remove.segmentIds.map(idKey), ['B:11']);
  const originalOrder = seed.document().blockCharacters(root).map(identity);
  for (const order of ['A-B','B-A']) {
    const final = receiver([], order === 'A-B' ? [A.transactions(),B.transactions()] : [B.transactions(),A.transactions()]);
    const flags = new Map(byIdentity(final));
    const bits = originalOrder.map(address => +flags.get(address)).join('');
    assert.equal(bits, '10001');
    assert.notEqual(bits, '10011', 'old per-segment fracture is rejected');
    assert.notEqual(bits, '11011', 'wrong whole-transaction winner is rejected');
    assert.deepEqual(nonemptyView(final), [['abde','1001'],['c','0']]);
    rows.push({name: `known fracture repaired ${order}`, expected: '10001', rejected: '10011', actual: bits,
      controlsHold: true, nonemptyView: nonemptyView(final), add, remove,
      transactions: final.transactions()});
  }
}

for (const [name, at, expected, rejected] of [
  ['left boundary excludes insertion',1,[['aXbc','0010']],[['aXbc','0110']]],
  ['right boundary includes insertion',2,[['abXc','0110']],[['abXc','0100']]],
]) {
  const replica = fresh(), preparation = atomicToggle(replica, block(replica), 1, 2);
  replica.insertText(block(replica), at, 'X');
  check(name, replica, expected, rejected, {preparation});
}
{
  const replica = fresh('abcd'), preparation = atomicToggle(replica, block(replica), 1, 3);
  replica.insertText(block(replica), 2, 'X');
  check('interior inherits', replica, [['abXcd','01110']], [['abXcd','01010']], {preparation});
}
{
  const replica = fresh(), preparation = atomicToggle(replica, block(replica), 2, 3);
  replica.insertText(block(replica), 3, 'X');
  check('END inherits', replica, [['abcX','0011']], [['abcX','0010']], {preparation});
}
for (const target of ['start','successor']) {
  const replica = fresh(), preparation = atomicToggle(replica, block(replica), 1, 2);
  if (target === 'start') {
    replica.deleteText(block(replica), 1, 2); replica.insertText(block(replica), 1, 'X');
    check('deleted start retains boundary', replica, [['aXc','000']], [['aXc','010']], {preparation});
  } else {
    replica.deleteText(block(replica), 2, 3); replica.insertText(block(replica), 2, 'X');
    check('deleted successor retains boundary', replica, [['abX','011']], [['abX','010']], {preparation});
  }
}
{
  const replica = fresh('ab'), root = block(replica), preparation = atomicToggle(replica, root, 0, 2);
  const split = replica.splitBlock(root, 1);
  check('split keeps both marks', replica, [['a','1'],['b','1']], [['a','1'],['b','0']], {preparation});
  replica.mergeBlock(split.newBlockId);
  check('corrected merge keeps marks', replica, [['ab','11']], [['a','1'],['b','1']], {preparation});
}

// Independent atomic writes oracle: one prepared value is assigned over each
// complete selected identity set, in transaction-priority order. No source
// interval evaluator or implementation output computes the expected bits.
function atomicWrites(initial, writes) {
  const flags = [...initial];
  for (const write of writes) for (const at of write.targets) flags[at] = write.value;
  return flags.map(Number).join('');
}
for (const initialBits of ['00000','01110','11111']) {
  for (const [a0,a1,b0,b1] of [[0,3,1,5],[1,4,2,5],[0,5,1,4],[1,3,1,3]]) {
    const seed = fresh('abcde'), root = block(seed);
    if (initialBits === '01110') seed.toggleBold(root, 1, 4);
    if (initialBits === '11111') seed.toggleBold(root, 0, 5);
    const A = new Replica('A','A',seed.transactions()), B = new Replica('B','B',seed.transactions());
    const add = atomicToggle(A,root,a0,a1), later = atomicToggle(B,root,b0,b1);
    const initial = [...initialBits].map(bit => bit === '1');
    const firstValue = !initial.slice(a0,a1).every(Boolean);
    const laterValue = !initial.slice(b0,b1).every(Boolean);
    assert.equal(add.value,firstValue,'first issuer Boolean from independent initial marks');
    assert.equal(later.value,laterValue,'later issuer Boolean from independent initial marks');
    const expected = atomicWrites(initial,[
      {targets: Array.from({length:a1-a0},(_,i)=>a0+i),value:firstValue},
      {targets: Array.from({length:b1-b0},(_,i)=>b0+i),value:laterValue},
    ]);
    const reversed = atomicWrites(initial,[
      {targets: Array.from({length:b1-b0},(_,i)=>b0+i),value:laterValue},
      {targets: Array.from({length:a1-a0},(_,i)=>a0+i),value:firstValue},
    ]);
    for (const order of ['A-B','B-A']) {
      const final = receiver(seed.transactions(), order === 'A-B' ? [A.transactions(),B.transactions()] : [B.transactions(),A.transactions()]);
      const actual = view(final)[0][1];
      assert.equal(actual,expected);
      const rejected = expected[0] === '1' ? `0${expected.slice(1)}` : `1${expected.slice(1)}`;
      assert.notEqual(actual,rejected);
      if (reversed !== expected) assert.notEqual(actual,reversed, 'transaction tie-break cannot reverse');
      rows.push({name:`concurrent overlap ${initialBits}/${a0}-${a1}/${b0}-${b1}/${order}`,
        expected,rejected,actual,controlsHold:true,add,later,reversed});
    }
  }
}

for (const scenario of ['insert','delete','split','merge']) {
  for (const first of ['format','structure']) {
    const seed = fresh(scenario === 'merge' ? 'ab' : 'abcd');
    let selectedBlock = block(seed);
    if (scenario === 'merge') {
      selectedBlock = seed.createBlock(block(seed)).newBlockId;
      seed.insertText(selectedBlock,0,'cd');
    }
    const A = new Replica('A','A',seed.transactions()), B = new Replica('B','B',seed.transactions());
    const preparation = atomicToggle(A,selectedBlock,scenario === 'merge' ? 0 : 1,scenario === 'merge' ? 1 : 3);
    const structural = scenario === 'insert' ? B.insertText(block(B),2,'X')
      : scenario === 'delete' ? B.deleteText(block(B),1,2)
      : scenario === 'split' ? B.splitBlock(block(B),2).transaction : B.mergeBlock(selectedBlock).transaction;
    const final = receiver(seed.transactions(),first === 'format' ? [[preparation.transaction],[structural]]
      : [[structural],[preparation.transaction]]);
    const expected = scenario === 'insert' ? [['abXcd','01110']]
      : scenario === 'delete' ? [['acd','010']] : scenario === 'split' ? [['ab','01'],['cd','10']]
        : [['abcd','0010']];
    const rejected = scenario === 'insert' ? [['abXcd','01010']]
      : scenario === 'delete' ? [['acd','000']] : scenario === 'split' ? [['ab','01'],['cd','00']]
        : [['abcd','0000']];
    check(`concurrent ${scenario}/${first}`,final,expected,rejected,{preparation});
  }
}

{
  const replica = fresh('ab'), other = replica.createBlock(block(replica)).newBlockId;
  replica.insertText(other,0,'cd'); replica.mergeBlock(other);
  const add = atomicToggle(replica,block(replica),0,4);
  assert.equal(add.segments,2);
  check('multi-instance atomic add',replica,[['abcd','1111']],[['abcd','1100']],{preparation:add});
  const remove = atomicToggle(replica,block(replica),0,4);
  check('multi-instance atomic remove',replica,[['abcd','0000']],[['abcd','0011']],{preparation:remove});
}

console.log(JSON.stringify({schema:'notion-formatting-atomic-priority-v1',
  evidence:'finite patched-source execution with independent atomic assignment oracle',
  sourcePolicy:'only temporary document dispatcher/rich comparator changed; original toggle body and candidate planner unchanged',
  cases:rows,summary:{cases:rows.length,positiveAndNegativeControls:rows.length,
    fractureRepaired:true,sharedTransactionPriority:true,distinctSegmentIds:true,
    coversConcurrentOverlap:true,preservesBoundaryInheritance:true}}));
