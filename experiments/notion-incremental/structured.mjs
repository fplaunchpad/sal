// Research executable adapter. Independently maintained indexes, not extraction
// of the typed Lean model and not a production Notion implementation.
import {compareOpIds, compareItemIds, idKey, nextId, expandIdRanges, START} from './ids.js';
const clone = x => JSON.parse(JSON.stringify(x));
function sortedInsert(list, value, compare) {
 let lo=0,hi=list.length;while(lo<hi){const mid=(lo+hi)>>>1;if(compare(list[mid],value)<0)lo=mid+1;else hi=mid;}list.splice(lo,0,value);
}
export class Structured {
 constructor(transactions=[]) {
  this.transactions=new Map();this.instances=new Map();this.blocks=new Map();this.blockChildren=new Map();
  this.counts={transactionsIntegrated:0,rowsIntegrated:0,deleteTargets:0,queries:0,rowsVisited:0,merges:0,mergeRowsExamined:0};
  for(const tx of transactions)this.receive(tx);
 }
 instance(id) {
  if(!this.instances.has(id))this.instances.set(id,{rows:new Map(),children:new Map(),deleted:new Set(),cuts:new Map()});
  return this.instances.get(id);
 }
 row(instance,row) {
  const key=idKey(row.id),prior=instance.rows.get(key);
  if(prior){if(JSON.stringify(prior)!==JSON.stringify(row))throw Error('conflicting row');return;}
  instance.rows.set(key,row);const origin=idKey(row.originId);
  if(!instance.children.has(origin))instance.children.set(origin,[]);
  sortedInsert(instance.children.get(origin),row,(a,b)=>-compareItemIds(a.id,b.id));this.counts.rowsIntegrated++;
 }
 receive(tx) {
  const key=idKey(tx.id),existing=this.transactions.get(key);
  if(existing){if(JSON.stringify(existing)!==JSON.stringify(tx))throw Error('conflicting transaction identity');return false;}
  // Honest core transactions are complete immutable groups, applied synchronously
  // with no observable intermediate query; malformed raw partial groups excluded.
  for(const op of tx.operations){const a=op.args;
   if(op.command==='createBlock') {
    if(this.blocks.has(a.blockId))throw Error('recreated block');
    this.instance(a.titleTextInstanceId);const block={id:a.blockId,origin:a.afterBlockId??START,txid:clone(tx.id)};
    this.blocks.set(block.id,block);if(!this.blockChildren.has(block.origin))this.blockChildren.set(block.origin,[]);
    sortedInsert(this.blockChildren.get(block.origin),block,(a,b)=>-compareOpIds(a.txid,b.txid));
   }else if(op.command==='insertText'){
    const inst=this.instance(a.textInstanceId);let origin=a.originId;
    for(const [offset,content] of [...a.content].entries()) {const id=nextId(a.id,offset);this.row(inst,{id,originId:origin,kind:'text',content});origin=id;}
   }else if(op.command==='deleteText'){
    const inst=this.instance(a.textInstanceId);for(const id of expandIdRanges(a.idRanges)){inst.deleted.add(idKey(id));this.counts.deleteTargets++;}
   }else if(op.command==='splitText')this.row(this.instance(a.textInstanceId),{id:clone(a.id),originId:clone(a.originId),kind:'split'});
   else if(op.command==='moveTextSliceIntoBlock')this.instance(a.textInstanceId).cuts.set(idKey(a.textSliceStartItemId),a.targetBlockId);
   else throw Error(`outside core: ${op.command}`);
  }
  this.transactions.set(key,clone(tx));this.counts.transactionsIntegrated++;return true;
 }
 merge(other) {
  // Direct join of materialized structural facts; no transaction interpreter.
  // Full payload archive is retained solely for identity checking/reference and
  // honest client reissuance, and is included in the explicit memory proxy.
  for(const [key,tx] of other.transactions){const old=this.transactions.get(key);if(old&&JSON.stringify(old)!==JSON.stringify(tx))throw Error('conflicting transaction identity');}
  for(const [id,source] of other.instances){const target=this.instance(id);
   for(const row of source.rows.values()){this.counts.mergeRowsExamined++;this.row(target,clone(row));}
   for(const key of source.deleted)target.deleted.add(key);
   for(const [key,owner] of source.cuts){if(target.cuts.has(key)&&target.cuts.get(key)!==owner)throw Error('conflicting cut');target.cuts.set(key,owner);}
  }
  for(const [id,block] of other.blocks){const old=this.blocks.get(id);
   if(old){if(JSON.stringify(old)!==JSON.stringify(block))throw Error('conflicting block');continue;}
   const retained=clone(block);this.blocks.set(id,retained);if(!this.blockChildren.has(block.origin))this.blockChildren.set(block.origin,[]);
   sortedInsert(this.blockChildren.get(block.origin),retained,(a,b)=>-compareOpIds(a.txid,b.txid));
  }
  for(const [key,tx] of other.transactions)if(!this.transactions.has(key))this.transactions.set(key,clone(tx));
  this.counts.merges++;return this;
 }
 query(display="fold") {
  this.counts.queries++;const texts=new Map([...this.blocks.keys()].map(id=>[id,[]]));
  for(const [instanceId,inst] of this.instances){let owner=instanceId;const stack=[...(inst.children.get(idKey(START))??[])].reverse();
   while(stack.length){const row=stack.pop();this.counts.rowsVisited++;
    if(row.kind==='split'){owner=inst.cuts.get(idKey(row.id));if(owner===undefined)throw Error('unowned marker');}
    else if(!inst.deleted.has(idKey(row.id))){if(!texts.has(owner))throw Error('unknown owner');texts.get(owner).push(row.content);}
    const children=inst.children.get(idKey(row.id))??[];for(let i=children.length-1;i>=0;i--)stack.push(children[i]);
   }
  }
  if(display==='fold') {
   // Matches the checked creator-link fold: fixed bootstrap identity A@1,
   // issued block creator IDs, ascending source order, immediate-after splice.
   const order=[];
   for(const block of [...this.blocks.values()].sort((a,b)=>compareOpIds(a.txid,b.txid))){
    if(order.includes(block.id))continue;
    order.splice((block.origin===START?-1:order.indexOf(block.origin))+1,0,block.id);
   }
   return order.map(id=>({id,text:texts.get(id).join('')}));
  }
  if(display!=='tree')throw Error('unknown display strategy');
  const result=[],stack=[...(this.blockChildren.get(START)??[])].reverse();
  while(stack.length){const block=stack.pop();result.push({id:block.id,text:texts.get(block.id).join('')});
   const children=this.blockChildren.get(block.id)??[];for(let i=children.length-1;i>=0;i--)stack.push(children[i]);}
  return result;
 }
 memoryProxy() {
  return {archiveTransactions:this.transactions.size,physicalRows:[...this.instances.values()].reduce((n,i)=>n+i.rows.size,0),
   originIndexEntries:[...this.instances.values()].reduce((n,i)=>n+[...i.children.values()].reduce((s,c)=>s+c.length,0),0),
   deletedIds:[...this.instances.values()].reduce((n,i)=>n+i.deleted.size,0),cuts:[...this.instances.values()].reduce((n,i)=>n+i.cuts.size,0),blocks:this.blocks.size,instances:this.instances.size,blockOriginIndexEntries:[...this.blockChildren.values()].reduce((n,c)=>n+c.length,0)};
 }
}
