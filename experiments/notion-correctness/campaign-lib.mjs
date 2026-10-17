import {Replica} from './replica.js';
import {request} from './positional-spec.mjs';
export const view = r => r.document().aliveBlocks().map(b => ({id:b.id,
  chars:r.document().blockCharacters(b.id).map(c=>({text:c.text,bold:!!c.bold}))}));
export const obs = v => v.map(b=>b.chars);
export const texts = blocks => blocks.map(b=>b.map(c=>c.text).join(''));
export const equal = (a,b) => JSON.stringify(a)===JSON.stringify(b);
export function valid(v,q) {
 const b=v[q.block];if(!b)return false;const n=b.chars.length;
 if(q.kind==='merge')return q.block>0;
 if(q.kind==='insert'||q.kind==='split')return Number.isInteger(q.index)&&0<=q.index&&q.index<=n;
 return Number.isInteger(q.start)&&Number.isInteger(q.end)&&0<=q.start&&q.start<q.end&&q.end<=n;
}
export function apply(r,q) {
 const v=view(r);if(!valid(v,q))throw Error('invalid request');const id=v[q.block].id;
 if(q.kind==='insert')return r.insertText(id,q.index,q.text);
 if(q.kind==='delete')return r.deleteText(id,q.start,q.end);
 if(q.kind==='bold')return r.toggleBold(id,q.start,q.end);
 if(q.kind==='split')return r.splitBlock(id,q.index);
 if(q.kind==='merge')return r.mergeBlock(id);
 throw Error('invalid kind');
}
export function initial(text) {
 const r=new Replica('seed','seed',[]);let previous;
 for(const part of Array.isArray(text)?text:[text]){
  previous=r.createBlock(previous).newBlockId;r.insertText(previous,0,part);
 }return r.transactions();
}
export function join(archives) {
 const r=new Replica('collector','collector',[]);
 for(const txs of archives)for(const tx of txs)r.receive(tx);
 return r.transactions();
}
export function replay(trace) {
 let txs=initial(trace.text);const used=new Set(['seed','collector','probe']);
 for(const round of trace.rounds){
  const branches=[];
  for(const b of round.branches){
   if(used.has(b.session))throw Error('reused session');used.add(b.session);
   const r=new Replica(b.session,b.session,txs);
   for(const q of b.requests)apply(r,q);
   branches.push(r.transactions());
  }
  txs=join([txs,...branches]);
 }
 return txs;
}
function bag(blocks) {return blocks.flat().map(c=>c.text).sort().join('');}
export function probe(txs,q) {
 const r=new Replica('probe','probe',txs),before=view(r);
 if(!valid(before,q))return {valid:false};
 const expected=request(obs(before),q);let after,generated;
 try{generated=apply(r,q);after=view(r);}catch(e){return {valid:true,signature:q.kind+':exception',error:e.message,before,expected};}
 const actual=obs(after),textOK=equal(texts(actual),texts(expected));
 const ok=q.kind==='insert'?textOK:equal(actual,expected);
 let signature=null;
 if(!ok){
  if(!textOK){
   signature=q.kind+(bag(actual)!==bag(expected)?':content':':placement');
  }else if(q.kind==='bold'){
   let missing=0,extra=0;
   for(let b=0;b<actual.length;b++)for(let i=0;i<actual[b].length;i++){
    if(actual[b][i].bold===expected[b][i].bold)continue;
    if(b===q.block&&q.start<=i&&i<q.end)missing++;else extra++;
   }
   signature='bold:'+(missing&&extra?'both':missing?'missed':'outside');
  }else signature=q.kind+':format';
 }
 return {valid:true,signature,before,request:q,expected,actual,generated};
}
export function queries(v){
 const out=[];
 for(let block=0;block<v.length;block++){
  const n=v[block].chars.length;
  if(block>0)out.push({kind:'merge',block});
  for(let index=0;index<=n;index++){
   out.push({kind:'insert',block,index,text:'X'},{kind:'split',block,index});
  }
  for(let start=0;start<n;start++)for(let end=start+1;end<=n;end++)
   out.push({kind:'delete',block,start,end},{kind:'bold',block,start,end});
 }
 return out;
}
export function minimize(trace,q,signature){
 let best=structuredClone(trace),query=structuredClone(q),attempts=0,rejected=0;
 const fails=(t,p=query)=>{attempts++;try{return probe(replay(t),p).signature===signature;}catch{rejected++;return false;}};
 let changed=true;
 while(changed){changed=false;
  outer:for(let i=0;i<best.rounds.length;i++)for(let j=0;j<best.rounds[i].branches.length;j++)for(let k=0;k<best.rounds[i].branches[j].requests.length;k++){
   const t=structuredClone(best);t.rounds[i].branches[j].requests.splice(k,1);
   if(fails(t)){best=t;changed=true;break outer;}
  }
  if(changed)continue;
  // Reduce numeric parameters; replay rejects invalid requests rather than clamping.
  const locations=[];
  for(let i=0;i<best.rounds.length;i++)for(let j=0;j<best.rounds[i].branches.length;j++)for(let k=0;k<best.rounds[i].branches[j].requests.length;k++)locations.push([i,j,k]);
  locations.push(null);
  simplify:for(const loc of locations){
   const orig=loc?best.rounds[loc[0]].branches[loc[1]].requests[loc[2]]:query;
   for(const key of ['block','index','start','end'])if(orig[key]>0)for(const val of [...new Set([0,orig[key]-1])]){
    const t=structuredClone(best),p=structuredClone(query),op=loc?t.rounds[loc[0]].branches[loc[1]].requests[loc[2]]:p;
    op[key]=val;if(fails(t,p)){best=t;query=p;changed=true;break simplify;}
   }
  }
  if(changed)continue;
  if(Array.isArray(best.text)&&best.text.length>1){
   for(let i=0;i<best.text.length;i++){
    const t=structuredClone(best);t.text.splice(i,1);
    if(fails(t)){best=t;changed=true;break;}
   }
  }
  if(changed)continue;
  const parts=Array.isArray(best.text)?best.text:[best.text];
  shrinkText:for(let i=0;i<parts.length;i++)for(let j=0;j<parts[i].length;j++){
   const t=structuredClone(best),xs=[...parts];xs[i]=xs[i].slice(0,j)+xs[i].slice(j+1);
   t.text=Array.isArray(best.text)?xs:xs[0];
   if(fails(t)){best=t;changed=true;break shrinkText;}
  }
 }
 best.rounds=best.rounds.map(r=>({branches:r.branches.filter(b=>b.requests.length)})).filter(r=>r.branches.length);
 const result=probe(replay(best),query);
 if(result.signature!==signature)throw Error('minimizer lost failure');
 return {trace:best,probe:query,result,shrink:{attempts,rejected,criterion:'fixed point: delete one setup request/seed block/seed character or reduce one block/position; preserve symptom; no global minimality claim'}};
}
