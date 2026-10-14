import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {IdentityDocument} from './identity-spec.mjs';
const key=id=>typeof id==='string'?id:`${id.sessionId}:${id.counter}`;
// Decode generated messages into semantic commands. This boundary is audited
// separately; the independent machine does not inspect the demo or its state.
function commands(tx) {
  const out=[];
  for (const op of tx.operations) {
    const a=op.args;
    if(op.command==='createBlock') out.push({kind:'create',block:a.blockId,after:a.afterBlockId,instance:a.titleTextInstanceId});
    else if(op.command==='insertText') out.push({kind:'insert',instance:a.textInstanceId,origin:key(a.originId),
      characters:[...a.content].map((text,i)=>({id:key({...a.id,counter:a.id.counter+i}),text}))});
    else if(op.command==='deleteText') out.push({kind:'delete',instance:a.textInstanceId,
      ids:a.idRanges.flatMap(([id,n])=>Array.from({length:n},(_,i)=>key({...id,counter:id.counter+i})))});
    else if(op.command==='splitText') {
      const move=tx.operations.find(x=>x.command==='moveTextSliceIntoBlock');
      if(!move) throw Error('outside split-only fragment');
      out.push({kind:'split',instance:a.textInstanceId,origin:key(a.originId),id:key(a.id),target:move.args.targetBlockId});
    } else if(op.command!=='moveTextSliceIntoBlock') throw Error('outside split-only fragment');
  }
  return out;
}
const view=r=>{const d=r.document();return d.aliveBlocks().map(b=>[b.id,d.blockText(b.id)]);};
function witness(transactions, SpecClass = IdentityDocument) {
  // A candidate witness, not a definition of the independent specification.
  const ordered=[...transactions].sort((a,b)=>a.id.counter-b.id.counter ||
    (a.id.sessionId<b.id.sessionId?-1:a.id.sessionId>b.id.sessionId?1:0));
  const spec=new SpecClass();
  for(const tx of ordered) for(const cmd of commands(tx)) spec.step(cmd);
  return spec.view();
}
// Hand-derived machine controls: these run without the demo.
const s=new IdentityDocument();
s.step({kind:'create',block:'old',instance:'text'}).step({kind:'insert',instance:'text',origin:'start',characters:[{id:'a',text:'a'},{id:'b',text:'b'}]})
 .step({kind:'create',block:'new',instance:'new',after:'old'}).step({kind:'split',instance:'text',origin:'a',id:'cut',target:'new'})
 .step({kind:'delete',instance:'text',ids:['b']});
assert.deepEqual(s.view(),[['old','a'],['new','']]);
assert.notDeepEqual(s.view(),[['old','ab'],['new','']]);
// Exercise the same message decoder and witness comparison against known-broken
// implementations. Mutation stays in the harness, outside the specification.
class DeleteNoOp extends IdentityDocument {
  step(command) { return command.kind==='delete'?this:super.step(command); }
}
class SplitLeavesSuffix extends IdentityDocument {
  step(command) { return command.kind==='split'?this:super.step(command); }
}
const mutationControls=[];
for(const [name,SpecClass,prepare] of [
  ['delete-no-op',DeleteNoOp,(r,b)=>r.deleteText(b,0,1)],
  ['split-leaves-suffix',SplitLeavesSuffix,(r,b)=>r.splitBlock(b,1)]]) {
  const r=new Replica('control','control',[]),{newBlockId:block}=r.createBlock();
  r.insertText(block,0,'ab');prepare(r,block);
  const actual=view(r),normal=witness(r.transactions()),mutant=witness(r.transactions(),SpecClass);
  assert.deepEqual(normal,actual);
  assert.notDeepEqual(mutant,actual,`${name} must be caught by the same comparison`);
  mutationControls.push({name,detected:true,normal,mutant,actual,comparisonChecks:2});
}
let checks=0;
for(const seedValue of [0x134ab912,0x514a2d19,0xabcdef01]) {
  let rng=seedValue;
  const random=n=>{rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return(rng>>>0)%n;};
  for(let trial=0;trial<50;trial++) {
    const seed=new Replica('seed','seed',[]);const {newBlockId}=seed.createBlock();seed.insertText(newBlockId,0,'abc');
    let transactions=seed.transactions();const history=[];
    for(let round=0;round<6;round++) {
      const branches=[];
      for(let branch=0;branch<2;branch++) {
        const r=new Replica(`t${trial}r${round}b${branch}`,'branch',transactions);
        for(let k=0;k<2;k++) {
          const blocks=view(r),[block,text]=blocks[random(blocks.length)],index=random([...text].length+1),kind=random(3);
          const request={kind:['insert','delete','split'][kind],block,index};
          if(kind===0)r.insertText(block,index,'X');
          if(kind===1)r.deleteText(block,index,Math.min(index+1,[...text].length));
          if(kind===2)r.splitBlock(block,index);
          history.push({round,branch,request});
          const expected=witness(r.transactions()),actual=view(r);checks++;
          if(JSON.stringify(expected)!==JSON.stringify(actual)){
            console.log(JSON.stringify({name:'identity-spec-counterexample',seed:seedValue,trial,history,transactions:r.transactions(),expected,actual}));process.exit(1);
          }
        }
        branches.push(r.transactions());
      }
      const collector=new Replica('collector','collector',transactions);
      for(const tx of branches.flat())collector.receive(tx);
      transactions=collector.transactions();const expected=witness(transactions),actual=view(collector);checks++;
      if(JSON.stringify(expected)!==JSON.stringify(actual)){
        console.log(JSON.stringify({name:'identity-spec-counterexample',seed:seedValue,trial,history,transactions,expected,actual}));process.exit(1);
      }
    }
  }
}
console.log(JSON.stringify({name:'identity-spec-differential',seeds:['0x134ab912','0x514a2d19','0xabcdef01'],trialsPerSeed:50,rounds:6,checks,discarded:0,mutationControls,result:'pass',scope:'generated split/insert/delete histories; candidate sorted witness, no general refinement theorem'}));
