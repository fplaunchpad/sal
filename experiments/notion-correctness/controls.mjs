import assert from 'node:assert/strict';
import {request,plain} from './positional-spec.mjs';
import {initial,probe,replay,view,obs,texts,equal} from './campaign-lib.mjs';
// Hand-derived ordinary-list expectations, independent of the demo.
const plainDoc=['ab','c'].map(plain);
const cases=[
 [{kind:'insert',block:0,index:1,text:'X'},['aXb','c']],
 [{kind:'delete',block:0,start:0,end:1},['b','c']],
 [{kind:'split',block:0,index:1},['a','b','c']],
 [{kind:'merge',block:1},['abc']]
];
for(const [q,wanted]of cases){
 const expected=request(plainDoc,q);assert.deepEqual(texts(expected),wanted);
 assert.notDeepEqual(texts(expected),texts(plainDoc)); // rejects no-op implementations
 const got=probe(initial(['ab','c']),q);assert.equal(got.signature,null);assert.deepEqual(texts(got.actual),wanted);
}
const bold={kind:'bold',block:0,start:0,end:1};
assert.deepEqual(request(plainDoc,bold),[[{text:'a',bold:true},{text:'b',bold:false}],[{text:'c',bold:false}]]);
assert.notDeepEqual(request(plainDoc,bold),plainDoc);
const r=probe(initial(['ab','c']),bold);assert.equal(r.signature,null);
// Existing bold marks: split/delete/merge preserve untouched flags; toggling off works.
const trace={text:['ab','cd'],rounds:[{branches:[{session:'A',requests:[{kind:'bold',block:0,start:0,end:2}]}]}]};
const archive=replay(trace);
for(const q of [{kind:'split',block:0,index:1},{kind:'delete',block:0,start:0,end:1},{kind:'merge',block:1},{kind:'bold',block:0,start:0,end:2}])assert.equal(probe(archive,q).signature,null);
const off=probe(archive,{kind:'bold',block:0,start:0,end:2});assert.deepEqual(off.actual, ['ab','cd'].map(plain));assert.notDeepEqual(off.actual,obs(off.before));
// Out-of-bounds requests are not silently converted to valid histories.
assert.equal(probe(initial('a'),{kind:'split',block:0,index:2}).valid,false);
assert.equal(probe(initial('a'),{kind:'delete',block:0,start:1,end:0}).valid,false);
console.log('Independent oracle controls and source passing controls passed.');
