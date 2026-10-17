import assert from 'node:assert/strict';
import {Network,replay,keys} from './network-lib.mjs';
import {view,obs,texts} from './campaign-lib.mjs';
// Hand-derived: two offline requests choose positions in distinct visible
// lists. Deleting b and inserting X after a jointly leave aX.
const n=new Network('ab',['A','B','C']);
n.edit('A',{kind:'insert',block:0,index:1,text:'X'},'a');
assert.deepEqual(texts(obs(view(n.replicas.get('A')))),['aXb']);
assert.notDeepEqual(texts(obs(view(n.replicas.get('B')))),['aXb']);
n.edit('B',{kind:'delete',block:0,start:1,end:2},'b');
assert.deepEqual(texts(obs(view(n.replicas.get('B')))),['a']);
assert.notDeepEqual(texts(obs(view(n.replicas.get('B')))),['ab']);
n.deliver('C','a');n.deliver('C','b');
assert.deepEqual(texts(obs(view(n.replicas.get('C')))),['aX']);
n.edit('C',{kind:'insert',block:0,index:2,text:'Y'},'c');
assert.throws(()=>n.deliver('A','c'),/causal dependency absent/);
assert.notDeepEqual(keys(n.replicas.get('A')),keys(n.replicas.get('C')));
const end=n.sync();assert.deepEqual(texts(end.display),['aXY']);assert.notDeepEqual(texts(end.display),['ab']);
assert.equal(n.failures.length,0);
const trace={text:'ab',sessions:['A','B','C'],events:n.events};
assert.deepEqual(replay(trace).sync().display,end.display);
const forged=structuredClone(trace);forged.events[0].dependencies=[];
assert.throws(()=>replay(forged),/recorded issuer knowledge differs/);
const bad=structuredClone(trace);bad.events.find(e=>e.kind==='edit').request.index=3;
assert.throws(()=>replay(bad),/invalid request/);
// Formatting positive and no-op negative share hand-derived flags.
const f=new Network('ab',['D','E']);f.edit('D',{kind:'bold',block:0,start:0,end:1},'d');
const wanted=[[{text:'a',bold:true},{text:'b',bold:false}]];
assert.deepEqual(obs(view(f.replicas.get('D'))),wanted);
assert.notDeepEqual(obs(view(f.replicas.get('E'))),wanted);
assert.deepEqual(f.sync().display,wanted);assert.equal(f.failures.length,0);
f.edit('D',{kind:'insert',block:0,index:0,text:'X'},'x');
const afterInsert=obs(view(f.replicas.get('D')));
assert.deepEqual(afterInsert[0].slice(1),wanted[0]);
assert.notDeepEqual(afterInsert[0].slice(1),[{text:'a',bold:false},{text:'b',bold:false}]);
assert.equal(f.failures.length,0);
// Calibrate this exact persistent-session harness on the known split defect.
// Six structural setup requests are followed by an ordinary split at zero.
const broken=new Network('ab',['S','A','B','C']);
const split=(block,index)=>({kind:'split',block,index}),merge=block=>({kind:'merge',block});
broken.edit('S',split(0,0),'s0');broken.edit('S',split(0,0),'s1');
for(const to of ['A','B','C']){broken.deliver(to,'s0');broken.deliver(to,'s1');}
broken.edit('A',split(2,1),'a0');broken.edit('A',merge(2),'a1');
broken.edit('B',merge(2),'b0');
for(const id of ['a0','a1','b0'])broken.deliver('C',id);
broken.edit('C',merge(2),'c0');broken.edit('C',split(1,0),'c1');
const failure=broken.failures.at(-1);
assert.equal(failure.signature,'split:placement');assert.equal(failure.classification,'known:split-subtree');
assert.deepEqual(texts(failure.expected),['','','ab']);
assert.deepEqual(texts(failure.actual),['','b','a']);
assert.notDeepEqual(failure.actual,failure.expected);
const nearby=new Network(['','ab'],['P','Q']);nearby.edit('P',split(1,0),'p0');
assert.deepEqual(texts(obs(view(nearby.replicas.get('P')))),['','','ab']);
assert.notDeepEqual(texts(obs(view(nearby.replicas.get('P')))),['','b','a']);
assert.equal(nearby.failures.length,0);
// Independent conservation control: split and merge never delete text.
// The tempting degenerate explanation is deletion or noncausal delivery;
// neither occurs here, yet all blocks become dead after synchronization.
const lost=new Network(['a','b','c'],['A','B']);
lost.edit('A',merge(2),'a0');lost.edit('A',split(1,0),'a1');lost.edit('A',merge(2),'a2');
lost.edit('B',merge(1),'b0');lost.deliver('B','a0');lost.deliver('B','a1');
assert.deepEqual(texts(obs(view(lost.replicas.get('B')))),['','abc']);
lost.edit('B',merge(1),'b1');lost.deliver('B','a2');
assert.deepEqual(lost.sync().display,[]);
assert.notDeepEqual(lost.sync().display,[[{text:'a',bold:false},{text:'b',bold:false},{text:'c',bold:false}]]);
assert.notEqual(lost.sync().display.flat().map(c=>c.text).sort().join(''),'abc');
assert(lost.failures.some(f=>f.signature==='structure:empty'));
console.log('Persistent-session, independent local effect, causal rejection, replay and convergence controls passed.');
