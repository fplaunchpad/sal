// Diagnose recorded failures from inspected source state, separately from the oracle.
// Matching these predictions is measured evidence for a root cause, not a proof.
import fs from 'node:fs';
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {idKey} from './ids.js';
import {iterateTextSliceTree,itemsInTextSlice} from './text-slice-tree.js';
import {replay,probe,view,obs,texts,equal} from './campaign-lib.mjs';
const saved=JSON.parse(fs.readFileSync('input.json','utf8')),counts={},unexplained=[];
assert(Array.isArray(saved.failureStates),'Input must retain all failing states');
for(const state of saved.failureStates){
 const txs=replay(state.trace);
 for(const record of state.probes){
  const q=record.request,p=probe(txs,q);assert.equal(p.signature,record.signature);
  const r=new Replica('diagnostic','diagnostic',txs),d=r.document(),blocks=d.aliveBlocks();let explained=false;
  if(q.kind==='split'){
   const block=blocks[q.block],loc=d.locateInsertion(block.id,q.index);
   const nodes=[...iterateTextSliceTree(block.title)],at=nodes.indexOf(loc.node);
   const nodeText=n=>itemsInTextSlice(n.textSlice,d.instances.get(n.textSlice.textInstanceId).rga).map(x=>x.content).join('');
   const nodeTexts=nodes.map(nodeText),subtree=[...iterateTextSliceTree(loc.node)];
   const offset=q.index-nodeTexts.slice(0,at).join('').length;
   if(offset>=0&&offset<=nodeTexts[at].length){
    const old=nodeTexts.slice(0,at).join('')+nodeTexts[at].slice(0,offset)+nodeTexts.slice(at+subtree.length).join('');
    const moved=nodeTexts[at].slice(offset)+subtree.slice(1).map(nodeText).join('');
    const predicted=texts(obs(p.before));predicted.splice(q.block,1,old,moved);
    explained=equal(predicted,texts(p.actual));
   }
  }else if(q.kind==='bold'){
   const chars=blocks.map(b=>d.blockCharacters(b.id));
   const selected=chars[q.block].slice(q.start,q.end),remove=selected.every(c=>c.bold),segments=[];
   for(const c of selected){const last=segments.at(-1);if(last?.[0].textInstanceId===c.textInstanceId)last.push(c);else segments.push([c]);}
   const targets=new Set();
   for(const seg of segments){
    const inst=seg[0].textInstanceId,order=d.instances.get(inst).rga.visibleItems();
    const first=order.findIndex(x=>idKey(x.id)===idKey(seg[0].item.id)),last=order.findIndex(x=>idKey(x.id)===idKey(seg.at(-1).item.id));
    for(let i=first;i<=last;i++)targets.add(inst+'/'+idKey(order[i].id));
   }
   const predicted=chars.map(xs=>xs.map(c=>({text:c.text,bold:targets.has(c.textInstanceId+'/'+idKey(c.item.id))?!remove:!!c.bold})));
   explained=equal(predicted,p.actual);
  }
  counts[record.signature]=(counts[record.signature]??0)+1;
  if(!explained)unexplained.push({trace:state.trace,probe:q,result:p});
 }
}
assert.deepEqual(counts,saved.counts.failures,'Every recorded failure must be classified');
console.log(JSON.stringify({mode:'classify',counts,findings:unexplained,scope:'Measured match to interval/subtree explanation; source inspection is not a correctness oracle.'}));
