// Independently justified regression: split/merge alone must preserve original x.
// Every request is validated on its own persistent client's current display.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {initial,view,valid,apply} from './campaign-lib.mjs';
const bag=r=>view(r).flatMap(b=>b.chars.map(c=>c.text)).sort().join('');
function run({receiveHeld=true,mergeLeft=true,receiveEarly=false,padding=0}={}){
 const txs=initial(['x']),a=new Replica('p0c1','A',txs),b=new Replica('p0c2','B',txs),ownA=[],ownB=[];
 function local(r,q,archive){assert(valid(view(r),q));const out=apply(r,q),tx=out.transaction??out;archive.push(tx);return tx;}
 local(a,{kind:'split',block:0,index:0},ownA);
 const remoteSplit=local(b,{kind:'split',block:0,index:1},ownB);
 const heldMerge=local(b,{kind:'merge',block:1},ownB);
 if(padding>0)local(a,{kind:'split',block:0,index:0},ownA);
 a.receive(remoteSplit); // Only this transaction's actual predecessor is the seed.
 if(receiveEarly)a.receive(heldMerge);
 for(let k=1;k<padding;k++)local(a,{kind:'split',block:0,index:0},ownA);
 const beforeLocal=bag(a);
 if(mergeLeft)local(a,{kind:'merge',block:receiveEarly?padding+1:padding+2},ownA);
 const afterLocal=bag(a);
 if(receiveHeld)a.receive(heldMerge); // Its split predecessor is already known.
 const afterReceive=bag(a);
 // Deliver all A transactions in issuer order: each causal predecessor is known
 // by B (its own split/merge and the seed), then check equal transaction sets.
 for(const tx of ownA)b.receive(tx);
 if(receiveHeld)assert.deepEqual(view(a),view(b));
 const deadOwners=[...a.document().blocks.values()].filter(block=>!block.alive&&a.document().blockText(block.id).includes('x')).map(block=>block.id);
 return {beforeLocal,afterLocal,afterReceive,deadOwners};
}
const failure=run();assert.equal(failure.beforeLocal,'x');assert.equal(failure.afterLocal,'x');assert.equal(failure.afterReceive,'');assert.notEqual(failure.afterReceive,'x');assert(failure.deadOwners.length>0);
const controls={noHeldReceive:run({receiveHeld:false}),noLocalMerge:run({mergeLeft:false}),earlyReceive:run({receiveEarly:true})};
for(const c of Object.values(controls)){assert.equal(c.afterReceive,'x');assert.notEqual(c.afterReceive,'');}
const cycleFailure=run({padding:1});assert.equal(cycleFailure.afterReceive,'');assert(cycleFailure.deadOwners.length>0);
console.log(JSON.stringify({failure,cycleFailure,controls,claim:'measured visible-character conservation violation after delayed causal atomic receive; same transaction sets still converge'}));
