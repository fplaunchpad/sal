// New small variants of the known split root cause, not additional bugs.
import assert from 'node:assert/strict';
import {initial,replay,probe,texts} from './campaign-lib.mjs';
const split=(block,index)=>({kind:'split',block,index}),merge=block=>({kind:'merge',block});
// Six setup requests after initial text; only split and merge thereafter.
const trace={text:'ab',rounds:[
 {branches:[{session:'S',requests:[split(0,0),split(0,0)]}]},
 {branches:[{session:'A',requests:[split(2,1),merge(2)]},{session:'B',requests:[merge(2)]}]},
 {branches:[{session:'C',requests:[merge(2)]}]}
]};
const p=probe(replay(trace),split(1,0));
assert.deepEqual(texts(p.before.map(b=>b.chars)),['','ab']);
// Ordinary split at zero must leave its old block empty and move all of ab.
assert.deepEqual(texts(p.expected),['','','ab']);
assert.deepEqual(texts(p.actual),['','b','a']);
assert.notDeepEqual(p.actual,p.expected);
assert.equal(p.signature,'split:placement');
// Nearby sequential control: same displayed text, no concurrent restructuring.
const control=probe(initial(['','ab']),split(1,0));
assert.equal(control.signature,null);assert.deepEqual(texts(control.actual),['','','ab']);
assert.notDeepEqual(texts(control.actual),['','b','a']);
console.log(JSON.stringify({name:'split-zero-after-six-structural-requests',classification:'N-001 variant',trace,probe:split(1,0),result:p,control:{expected:control.expected,actual:control.actual}}));
