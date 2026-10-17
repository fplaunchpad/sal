// Persistent sessions and explicit causal delivery. The positional oracle is
// independent; the source-state root predictions below are diagnostics only.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {idKey} from './ids.js';
import {iterateTextSliceTree,itemsInTextSlice} from './text-slice-tree.js';
import {request} from './positional-spec.mjs';
import {initial,view,obs,texts,equal,valid,apply} from './campaign-lib.mjs';
export const keys = r => r.transactions().map(t=>idKey(t.id)).sort();
const bag = bs => bs.flat().map(c=>c.text).sort().join('');
export function signature(q,before,expected,actual) {
 let comparable=actual;
 if(q.kind==='insert'&&equal(texts(actual),texts(expected))){
  comparable=structuredClone(actual);
  // Only new characters' inheritance is unspecified. Existing marks survive.
  for(let i=q.index;i<q.index+[...q.text].length;i++)comparable[q.block][i].bold=false;
 }
 if(equal(comparable,expected))return null;
 if(!equal(texts(actual),texts(expected)))return q.kind+(bag(actual)===bag(expected)?':placement':':content');
 if(q.kind!=='bold')return q.kind+':format';
 let missing=0,extra=0;
 for(let b=0;b<actual.length;b++)for(let i=0;i<actual[b].length;i++)if(actual[b][i].bold!==expected[b][i].bold){
  if(b===q.block&&q.start<=i&&i<q.end)missing++;else extra++;
 }
 return 'bold:'+(missing&&extra?'both':missing?'missed':'outside');
}
export function predict(r,q,before){
 const d=r.document(),blocks=d.aliveBlocks();
 if(q.kind==='split'){
  const loc=d.locateInsertion(blocks[q.block].id,q.index),nodes=[...iterateTextSliceTree(blocks[q.block].title)],at=nodes.indexOf(loc.node);
  const nodeTexts=nodes.map(n=>itemsInTextSlice(n.textSlice,d.instances.get(n.textSlice.textInstanceId).rga).map(x=>x.content));
  const subtree=[...iterateTextSliceTree(loc.node)],offset=q.index-nodeTexts.slice(0,at).flat().length;
  if(offset<0||offset>nodeTexts[at].length)return null;
  const wanted=texts(obs(before));wanted.splice(q.block,1,[...nodeTexts.slice(0,at).flat(),...nodeTexts[at].slice(0,offset),...nodeTexts.slice(at+subtree.length).flat()].join(''),[...nodeTexts[at].slice(offset),...subtree.slice(1).flatMap(n=>nodeTexts[nodes.indexOf(n)])].join(''));
  return {root:'known:split-subtree',text:wanted};
 }
 if(q.kind==='bold'){
  const chars=blocks.map(b=>d.blockCharacters(b.id)),selected=chars[q.block].slice(q.start,q.end),remove=selected.every(c=>c.bold),segments=[];
  for(const c of selected){const last=segments.at(-1);if(last?.[0].textInstanceId===c.textInstanceId)last.push(c);else segments.push([c]);}
  const targets=new Set();
  for(const seg of segments){const inst=seg[0].textInstanceId,order=d.instances.get(inst).rga.visibleItems();
   const first=order.findIndex(x=>idKey(x.id)===idKey(seg[0].item.id)),last=order.findIndex(x=>idKey(x.id)===idKey(seg.at(-1).item.id));
   for(let i=first;i<=last;i++)targets.add(inst+'/'+idKey(order[i].id));
  }
  return {root:'known:format-interval',actual:chars.map(xs=>xs.map(c=>({text:c.text,bold:targets.has(c.textInstanceId+'/'+idKey(c.item.id))?!remove:!!c.bold})))};
 }
 return null;
}
export class Network {
 constructor(text,sessions){
  assert.equal(new Set(sessions).size,sessions.length);assert(!sessions.includes('seed'));
  this.seed=initial(text);this.replicas=new Map(sessions.map(s=>[s,new Replica(s,s,this.seed)]));
  this.issued=new Map();this.events=[];this.failures=[];this.stats={edits:0,deliveries:0,deliveredTransactions:0,causalChecks:0,duplicateChecks:0,continuedDifferentViewEdits:0,partiallyDeliveredEdits:0};
 }
 eligible(to){const have=new Set(keys(this.replicas.get(to)));return [...this.issued.values()].filter(e=>!e.ids.every(id=>have.has(id))&&e.dependencies.every(id=>have.has(id)));}
 edit(session,q,id,record=null){
  const r=this.replicas.get(session);assert(r,'unknown session');const before=view(r);assert(valid(before,q),'invalid request');
  assert(!this.issued.has(id),'duplicate edit label');
  const dependencies=keys(r),expected=request(obs(before),q),prediction=predict(r,q,before),prior=new Set(dependencies);
  if(record)assert.deepEqual(dependencies,record.dependencies,'recorded issuer knowledge differs');
  const distinct=new Set([...this.replicas.values()].map(x=>JSON.stringify(obs(view(x))))).size>1;
  let error=null;try{apply(r,q);}catch(e){error=e.message;}
  const transactions=r.transactions().filter(t=>!prior.has(idKey(t.id))),ids=transactions.map(t=>idKey(t.id));
  if(record)assert.deepEqual(ids,record.ids,'recorded issued IDs differ');
  assert(ids.length>0||error,'nonempty valid request emitted no transactions');
  const event={kind:'edit',id,session,request:structuredClone(q),dependencies,ids};
  this.events.push(event);this.issued.set(id,{...event,transactions});this.stats.edits++;
  if(distinct)this.stats.continuedDifferentViewEdits++;
  const remote=[...this.issued.values()].filter(e=>e.session!==session);
  if(remote.some(e=>e.ids.every(k=>prior.has(k)))&&remote.some(e=>e.ids.some(k=>!prior.has(k))))this.stats.partiallyDeliveredEdits++;
  let actual=null,readError=null;try{actual=obs(view(r));}catch(e){readError=e.message;}
  const sig=error||readError?q.kind+':exception':signature(q,before,expected,actual);
  if(sig){
   const classified=!error&&!readError&&actual!==null&&prediction&&(prediction.actual?equal(prediction.actual,actual):equal(prediction.text,texts(actual)))?prediction.root:'unexplained';
   this.failures.push({step:this.events.length-1,eventId:id,signature:sig,classification:classified,before,expected,actual,error:error||readError});
  }
  return event;
 }
 deliver(to,id){
  const r=this.replicas.get(to),e=this.issued.get(id);assert(r&&e,'unknown delivery endpoint or edit');
  const have=new Set(keys(r));assert(e.dependencies.every(k=>have.has(k)),'causal dependency absent');
  assert(!e.ids.some(k=>have.has(k))||e.ids.every(k=>have.has(k)),'partial request delivery');
  this.stats.causalChecks++;
  // A client request is indivisible even if a future API emits several txs.
  for(const t of e.transactions)r.receive(t);
  for(const t of e.transactions)assert.equal(r.receive(t),false,'duplicate receipt changed archive');
  this.stats.duplicateChecks+=e.transactions.length;this.stats.deliveries++;this.stats.deliveredTransactions+=e.transactions.length;
  this.events.push({kind:'deliver',to,edit:id});
  try{
   const actual=obs(view(r));
   // Every permitted local request preserves at least one block. A delivery
   // losing all blocks violates the candidate concurrent availability contract.
   if(actual.length===0)this.failures.push({step:this.events.length-1,eventId:id,signature:'structure:empty',classification:'unexplained',to,actual,contract:'At least one visible block remains after valid split/merge/text/bold requests from a nonempty seed.'});
  }catch(error){this.failures.push({step:this.events.length-1,eventId:id,signature:'delivery:exception',classification:'unexplained',to,error:error.message});}
 }
 sync(pick=n=>0){
  while(true){const eligible=[];for(const to of this.replicas.keys())for(const e of this.eligible(to))eligible.push({to,id:e.id});
   if(!eligible.length)break;const e=eligible[pick(eligible.length)];this.deliver(e.to,e.id);
  }
  const reps=[...this.replicas.values()],archive=keys(reps[0]),display=obs(view(reps[0]));
  for(const r of reps){assert.deepEqual(keys(r),archive,'eventual archive inequality');assert.deepEqual(obs(view(r)),display,'equal archives display differently');}
  const all=[...new Set([...this.seed,...[...this.issued.values()].flatMap(e=>e.transactions)].map(t=>idKey(t.id)))].sort();assert.deepEqual(archive,all,'sync omitted transactions');
  return {archiveSize:archive.length,display};
 }
}
export function replay(trace,{verify=true,finish=false}={}){
 const n=new Network(trace.text,trace.sessions);
 for(const event of trace.events){
  if(event.kind==='edit')n.edit(event.session,event.request,event.id,verify?event:null);
  else {assert.equal(event.kind,'deliver');n.deliver(event.to,event.edit);}
 }
 if(finish)n.sync();return n;
}
// Remove an edit and all its deliveries. Every candidate is reissued in the
// same persistent sessions and validates bounds and actual causal knowledge.
export function minimize(trace,targetSignature){
 let best=structuredClone(trace),attempts=0,rejected=0;
 const tryTrace=t=>{attempts++;try{const n=replay(t,{verify:false}),f=n.failures.find(f=>f.signature===targetSignature&&f.classification==='unexplained');
   if(!f)return null;return {text:t.text,sessions:t.sessions,events:n.events.slice(0,f.step+1)};
  }catch{rejected++;return null;}};
 let changed=true;while(changed){changed=false;
  for(let i=0;i<best.events.length;i++){
   const ev=best.events[i],candidate=structuredClone(best);candidate.events.splice(i,1);
   if(ev.kind==='edit')candidate.events=candidate.events.filter(x=>x.kind!=='deliver'||x.edit!==ev.id);
   const accepted=tryTrace(candidate);if(accepted){best=accepted;changed=true;break;}
  }
 }
 const n=replay(best),failure=n.failures.find(f=>f.signature===targetSignature&&f.classification==='unexplained');assert(failure);
 return {trace:best,failure,shrink:{attempts,rejected,criterion:'fixed point under removing one edit plus its deliveries, or one delivery; reissue IDs and dependencies, reject invalid requests or causal deliveries; no global minimality claim'}};
}
