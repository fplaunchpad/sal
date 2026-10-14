import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {TransactionSet} from './transaction-set.mjs';
import {plain, request, textView, splitDelete} from './positional-spec.mjs';

const view = r => r.document().aliveBlocks().map(b => ({id: b.id,
  text: r.document().blockText(b.id),
  bold: r.document().blockCharacters(b.id).map(c => !!c.bold)}));
const texts = r => view(r).map(b => b.text);
const observable = r => view(r).map(({text, bold}) => ({text, bold}));
const specView = blocks => blocks.map(b => ({text: b.map(c => c.text).join(''), bold: b.map(c => c.bold)}));
const seed = new Replica('seed', 'seed', []);
const {newBlockId: block} = seed.createBlock(); seed.insertText(block, 0, 'abcd');
const initial = seed.transactions();
let cases = 0, failures = 0;
function log(row) { cases++; if (row.error || row.specAgreement === false) failures++; console.log(JSON.stringify(row)); }
const txOf = result => result?.transaction ?? result;
function call(r, op, target = block) {
  if (op.kind === 'split') return r.splitBlock(target, op.index);
  if (op.kind === 'insert') return r.insertText(target, op.index, op.text ?? 'X');
  if (op.kind === 'delete') return r.deleteText(target, op.start, op.end);
  if (op.kind === 'bold') return r.toggleBold(target, op.start, op.end);
  if (op.kind === 'merge') return r.mergeBlock(target);
  throw Error('unknown request');
}
function pair(name, leftRequest, rightRequest, {sessions = ['A','B'], clocks = [0,0], base = initial, leftTarget = block, rightTarget = block} = {}) {
  try {
    const a = new Replica(sessions[0], 'left', base), b = new Replica(sessions[1], 'right', base);
    // Reserve unused clocks, preserving valid client issuance without inventing
    // a causally preceding document edit. Gaps in Lamport allocation are legal.
    if (clocks[0]) a.clock.reserve(clocks[0]); if (clocks[1]) b.clock.reserve(clocks[1]);
    const left = txOf(call(a, leftRequest, leftTarget)), right = txOf(call(b, rightRequest, rightTarget));
    const local = [view(a), view(b)];
    const orders = [[left,right], [right,left], [left,right,left,right]];
    const delivered = orders.map((order, i) => {
      const r = new Replica(`receiver${i}`, 'receiver', base);
      for (const tx of order) if (tx) r.receive(tx);
      return view(r);
    });
    const baseState = new TransactionSet(base), ls = new TransactionSet(a.transactions()), rs = new TransactionSet(b.transactions());
    const merged = TransactionSet.merge(baseState, ls, rs);
    const nested = TransactionSet.merge(baseState, merged, ls);
    assert.deepEqual(view(merged.replica()), delivered[0]);
    assert.deepEqual(view(nested.replica()), delivered[0]);
    assert(delivered.every(v => JSON.stringify(v) === JSON.stringify(delivered[0])));
    const row = {name, requests: [leftRequest,rightRequest], sessions, clocks, base, transactions: [left,right], local,
      delivered, adapter: view(merged.replica()), nestedMergeAgreement: true};
    if (leftRequest.kind === 'split' && rightRequest.kind === 'delete' && base === initial) {
      row.specExpected = splitDelete('abcd',leftRequest.index,rightRequest.start,rightRequest.end);
      row.specAgreement = JSON.stringify(row.specExpected) === JSON.stringify(delivered[0].map(b => b.text));
    }
    log(row);
  } catch (e) { log({name, requests:[leftRequest,rightRequest], sessions, clocks, base, error:e.message, stack:e.stack}); }
}

// Independent ordinary request-effect checks. Each expected result is computed
// from a separate positional state, never from demo transaction interpretation.
for (const op of [
  ...[0,1,2,3,4].map(index => ({kind:'split',index})),
  ...[0,1,2,3,4].map(index => ({kind:'insert',index,text:'X'})),
  ...[0,1,2,3].flatMap(start => Array.from({length:4-start},(_,n)=>({kind:'delete',start,end:start+n+1}))),
  ...[0,1,2,3].flatMap(start => Array.from({length:4-start},(_,n)=>({kind:'bold',start,end:start+n+1})))]) {
  const r = new Replica('local','local',initial); const result = call(r,op);
  const expected = specView(request([plain('abcd')],op));
  log({name:'local-request',request:op,base:initial,transaction:txOf(result),actual:view(r),specExpected:expected,
    specAgreement:JSON.stringify(observable(r)) === JSON.stringify(expected)});
}

for (const sessions of [['A','B'],['B','A']]) for (const clocks of [[0,0],[2,0],[0,2]]) {
  for (const split of [0,1,2,3,4]) {
    for (const index of [0,1,2,3,4]) pair('split-insert',{kind:'split',index:split},{kind:'insert',index,text:'X'},{sessions,clocks});
    for (let start=0;start<4;start++) for (let end=start+1;end<=4;end++)
      pair('split-delete',{kind:'split',index:split},{kind:'delete',start,end},{sessions,clocks});
  }
}
for (const sessions of [['A','B'],['B','A']]) for (const left of [0,1,2,3,4]) for (const right of [0,1,2,3,4])
  pair('concurrent-splits',{kind:'split',index:left},{kind:'split',index:right},{sessions});
for (const sessions of [['A','B'],['B','A']]) for (const start of [0,1,2,3]) for (let end=start+1;end<=4;end++)
  pair('split-bold',{kind:'split',index:2},{kind:'bold',start,end},{sessions});

// Causal operations address the actual local block selected after split.
for (const kind of ['insert','delete','bold']) for (const which of [0,1]) {
  const r = new Replica('causal','causal',initial), split = r.splitBlock(block,2);
  const target = which ? split.newBlockId : block;
  const op = kind === 'insert' ? {kind,index:0,text:'X'} : {kind,start:0,end:1};
  const tx = txOf(call(r,op,target));
  const expected = specView(request(request([plain('abcd')],{kind:'split',index:2}),{...op,block:which}));
  log({name:'causal-split-edit',request:op,which,base:initial,transactions:[split.transaction,tx],actual:view(r),
    specExpected:expected,specAgreement:JSON.stringify(observable(r)) === JSON.stringify(expected)});
}
for (const op of [{kind:'insert',index:2,text:'X'},{kind:'delete',start:1,end:3},{kind:'bold',start:1,end:3}]) {
  const r=new Replica('edit-first','edit-first',initial),edit=txOf(call(r,op)),split=r.splitBlock(block,1);
  const expected=specView(request(request([plain('abcd')],op),{kind:'split',index:1}));
  log({name:'causal-edit-split',request:op,base:initial,transactions:[edit,split.transaction],actual:view(r),specExpected:expected,
    specAgreement:JSON.stringify(observable(r))===JSON.stringify(expected)});
}

// Merge performs slice movement; the public Replica has no arbitrary block-move
// preparation method. Do not forge low-level movements and call them requests.
const mergeSeed = new Replica('setup','setup',initial);
const second = mergeSeed.splitBlock(block,2).newBlockId;
for (const sessions of [['A','B'],['B','A']]) for (const target of [block,second]) {
  for (const op of [{kind:'split',index:1},{kind:'insert',index:1,text:'X'},{kind:'delete',start:0,end:2},{kind:'bold',start:0,end:2}])
    pair('merge-edit',{kind:'merge'},op,{sessions,base:mergeSeed.transactions(),leftTarget:second,rightTarget:target});
}
console.error(JSON.stringify({cases,failures,note:'Agreement is finite evidence; adapter uses the same pinned document interpreter.'}));
if (failures) process.exitCode = 1;
