import fs from 'node:fs';
import {Replica} from './replica.js';
import {request} from './positional-spec.mjs';
import {TransactionSet} from './transaction-set.mjs';
const finding=JSON.parse(fs.readFileSync(new URL('./reachable-observations.jsonl',import.meta.url),'utf8').trim());
const view=r=>r.document().aliveBlocks().map(b=>({id:b.id,text:r.document().blockText(b.id),characters:r.document().blockCharacters(b.id).map(c=>({text:c.text,bold:!!c.bold}))}));
const steps=finding.history.flatMap((h,hi)=>h.requests.map((r,ri)=>({hi,ri,...r})));
let tests=0;
function replay(keep) {
  tests++;
  let transactions=finding.initial, aliases=new Map([['seed-block-1','seed-block-1']]),trace=[];
  try {
    for(let round=0;round<finding.history.length/2;round++) {
      const branches=[];
      for(let branch=0;branch<2;branch++) {
        const hi=round*2+branch,h=finding.history[hi],session=`t${h.trial}r${h.round}b${h.branch}`;
        const r=new Replica(session,session,transactions),issued=[];
        for(let ri=0;ri<h.requests.length;ri++) {
          const si=hi*2+ri;if(!keep.has(si))continue;
          const old=h.requests[ri],op=old.request,target=aliases.get(op.block),v=view(r),block=v.find(b=>b.id===target);
          if(!block)return undefined;
          const n=block.characters.length;
          if(op.kind!=='merge'&&(op.index<0||op.index>n))return undefined;
          if(op.kind==='delete'&&(op.start<0||op.end>n))return undefined;
          let result;
          if(op.kind==='split')result=r.splitBlock(target,op.index);
          if(op.kind==='insert')result=r.insertText(target,op.index,'X');
          if(op.kind==='delete')result=r.deleteText(target,op.start,op.end);
          if(op.kind==='merge')result=r.mergeBlock(target);
          if(result?.newBlockId)aliases.set(old.transaction.operations[0].args.blockId,result.newBlockId);
          issued.push({request:{...op,block:target},transaction:result?.transaction??result,after:view(r)});
        }
        branches.push(r.transactions());trace.push({round,branch,session,issued});
      }
      transactions=TransactionSet.merge(new TransactionSet(transactions),...branches.map(t=>new TransactionSet(t))).transactions();
    }
    const target=aliases.get(finding.before[finding.request.block].id),r=new Replica('check','check',transactions),before=view(r),bi=before.findIndex(b=>b.id===target);
    if(bi<0)return undefined;
    const op={...finding.request,block:bi},expected=request(before.map(b=>b.characters),op),result=r.splitBlock(target,op.index),actual=view(r);
    if(JSON.stringify(actual.map(b=>b.characters))===JSON.stringify(expected))return undefined;
    return {name:'minimized-reachable-local-counterexample',initial:finding.initial,trace,transactions,before,request:op,
      generated:result.transaction,expected,actual};
  }catch{return undefined;}
}
let keep=new Set(steps.map((_,i)=>i)),changed=true;
if(!replay(keep))throw Error('original failing request history does not replay');
while(changed){changed=false;for(const i of keep){const candidate=new Set(keep);candidate.delete(i);if(replay(candidate)){keep=candidate;changed=true;break;}}}
// Shrink seed text while preserving valid regenerated client issuance.
for(const content of ['a','ab','abc']) {
  const old=finding.initial[1].operations[0].args.content;
  finding.initial[1].operations[0].args.content=content;
  if(replay(keep))break;
  finding.initial[1].operations[0].args.content=old;
}
// Text shrinking can make formerly necessary requests redundant. Establish
// deletion minimality again on the final seed, rather than inheriting it.
changed=true;
while(changed){changed=false;for(const i of keep){const candidate=new Set(keep);candidate.delete(i);if(replay(candidate)){keep=candidate;changed=true;break;}}}
const result=replay(keep);result.minimization={algorithm:'greedy request removal with fresh valid client issuance',tests,retainedSteps:[...keep],oneMinimal:true};
console.log(JSON.stringify(result));
