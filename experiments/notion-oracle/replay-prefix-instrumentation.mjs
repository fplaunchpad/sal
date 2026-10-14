// Targeted honest-network structural replay checks. Patches observe actual
// pinned RGA entry points; they do not replace integration or traversal.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {CrdtDocument,createInitialTransactions} from './document.js';
import {RgaText} from './rga.js';
import {START,idKey,compareOpIds,nextId} from './ids.js';
const initial=createInitialTransactions('a😀b'),block='block-A';
const ledger=new Map(initial.map(tx=>[idKey(tx.id),{tx,dependencies:[],request:{kind:'bootstrap'}}]));
function issue(r,request,method,...args) {
 const dependencies=r.transactions().map(tx=>idKey(tx.id));
 const result=r[method](...args),tx=result?.transaction??result;
 if(tx) {assert(!ledger.has(idKey(tx.id)));ledger.set(idKey(tx.id),{tx,dependencies,request});}
 return tx;
}
const a=new Replica('A','A',initial),b=new Replica('\uE000','private-use',initial),c=new Replica('😀','emoji',initial);
const ax=issue(a,{kind:'insert-run',index:1,text:'XY'},'insertText',block,1,'XY');
const bs=issue(b,{kind:'split',index:1},'splitBlock',block,1);
const cr=issue(c,{kind:'insert-run',index:1,text:'pqrs'},'insertText',block,1,'pqrs');
const ai=issue(a,{kind:'insert-after-internal-run-origin',index:2,text:'!'},'insertText',block,2,'!');
const bnew=bs.operations[0].args.blockId;
issue(b,{kind:'insert-at-split-boundary',index:0,text:'Z'},'insertText',bnew,0,'Z');
c.receive(ax);c.receive(ax);
const deleted=issue(c,{kind:'delete-first',start:0,end:1},'deleteText',block,0,1);
issue(c,{kind:'insert-after-internal-bootstrap-atom',index:7,text:'#'},'insertText',block,7,'#');
a.receive(cr);a.receive(cr);
issue(a,{kind:'split-after-receiving-overlapping-clock-run',index:0},'splitBlock',block,0);
const clock=a.clock.counter,count=a.transactions().length;
assert.equal(a.insertText(block,0,''),undefined);assert.equal(a.deleteText(block,0,0),undefined);
assert.equal(a.clock.counter,clock);assert.equal(a.transactions().length,count);
const deleteDocument=c.document();
assert(c.transactions().some(tx=>idKey(tx.id)===idKey(deleted.id)));
assert([...deleteDocument.instances.values()].every(instance=>!instance.rga.items.has(idKey(deleted.id))),
  'delete transaction reservation must not count as a born RGA item');

let active,checks=0,dominanceChecks=0,internalOriginChecks=0,internalChildChecks=0,nonGlobalMax;
const originalRun=RgaText.prototype.insertRun,originalSplit=RgaText.prototype.insertSplit;
function observe(rga,id,origin,ids,kind) {
 if(!active)return;
 const owner=ledger.get(idKey(id));assert(owner,'RGA first key has no published owner');
 assert(origin===START||rga.items.has(idKey(origin)),'unknown origin in sorted replay prefix');
 const prior=[...rga.items.values()];
 for(const child of prior.filter(item=>idKey(item.originId)===idKey(origin))) {
  dominanceChecks++;assert(compareOpIds(child.id,id)<0,'fresh first key does not dominate old origin child');
  const runOwner=[...ledger.values()].find(entry=>entry.tx.operations.some(op=>op.command==='insertText'&&
    [...op.args.content].some((_,i)=>i>0&&idKey(nextId(op.args.id,i))===idKey(child.id))));
  if(runOwner) {
    assert(owner.dependencies.includes(idKey(runOwner.tx.id)),'issuer did not know complete internal-child run');
    internalChildChecks++;
  }
 }
 for(const itemId of ids) {
  assert(!active.items.has(idKey(itemId)),'source item identity reused across replay instances');
  active.items.add(idKey(itemId));
 }
 if(origin!==START) {
  const provenance=[...ledger.values()].find(entry=>entry.tx.operations.some(op=>op.command==='insertText'&&
   [...op.args.content].some((_,i)=>idKey(nextId(op.args.id,i))===idKey(origin))));
  assert(provenance||[...ledger.values()].some(entry=>entry.tx.operations.some(op=>op.command==='splitText'&&idKey(op.args.id)===idKey(origin))));
  if(provenance&&idKey(provenance.tx.id)!==idKey(origin))internalOriginChecks++;
 }
 const larger=prior.find(item=>compareOpIds(id,item.id)<0);
 if(larger&&!nonGlobalMax)nonGlobalMax={first:id,origin,largerStored:larger.id,
  note:'Dominance concerns children of this origin; not every previously replayed item.'};
 active.calls.push({first:id,origin,kind,itemCount:ids.length});checks++;
}
RgaText.prototype.insertRun=function(id,origin,text) {
 observe(this,id,origin,[...text].map((_,i)=>nextId(id,i)),'run');
 const result=originalRun.call(this,id,origin,text);
 if(active)assert.equal(this.orderedItems().length,this.items.size,'unreachable physical items after honest prefix');
 return result;
};
RgaText.prototype.insertSplit=function(id,origin) {
 observe(this,id,origin,[id],'split');const result=originalSplit.call(this,id,origin);
 if(active)assert.equal(this.orderedItems().length,this.items.size,'unreachable split after honest prefix');return result;
};
// Independent literal payload decoder: no source range helpers, RGA methods,
// traversal, or document selectors are used to derive expected stored fields.
function decodedTables(transactions) {
 const instances=new Map();
 const get=inst=>{if(!instances.has(inst))instances.set(inst,{rows:[],pending:new Set()});return instances.get(inst);};
 for(const tx of transactions)for(const op of tx.operations){const a=op.args;
  if(op.command==='createBlock')get(a.titleTextInstanceId);
  if(op.command==='insertText'){
   const target=get(a.textInstanceId);let origin=a.originId;
   for(const [offset,content] of [...a.content].entries()){
    const id={sessionId:a.id.sessionId,counter:a.id.counter+offset};
    target.rows.push({id,originId:origin,kind:'text',content,deleted:false});origin=id;
   }
  }
  if(op.command==='splitText')get(a.textInstanceId).rows.push({id:a.id,originId:a.originId,kind:'split',content:null,deleted:false});
  if(op.command==='deleteText')for(const [first,length] of a.idRanges)
   for(let offset=0;offset<length;offset++)get(a.textInstanceId).pending.add(`${first.sessionId}:${first.counter+offset}`);
 }
 return [...instances].map(([instance,{rows,pending}])=>({instance,rows:rows.map(row=>({...row,
  deleted:row.kind==='text'&&pending.has(`${row.id.sessionId}:${row.id.counter}`)})),pending:[...pending].sort()}));
}
function actualTables(doc){return [...doc.instances].map(([instance,value])=>({instance,
 rows:[...value.rga.items.values()].map(row=>({id:row.id,originId:row.originId,kind:row.kind,content:row.content??null,deleted:row.deleted})),
 pending:[...value.rga.deletedIds].sort()}));}
let tableChecks=0,rowChecks=0,tombstoneChecks=0,fullTable;
const events=[...ledger.values()];let closedSets=0,prefixes=0;
for(let mask=0;mask<2**events.length;mask++) {
 const selected=events.filter((_,i)=>mask&(2**i)),keys=new Set(selected.map(e=>idKey(e.tx.id)));
 if(selected.some(e=>e.dependencies.some(dep=>!keys.has(dep))))continue;
 closedSets++;
 const sorted=selected.map(e=>e.tx).sort((a,b)=>compareOpIds(a.id,b.id));
 for(let end=0;end<=sorted.length;end++) {
  const prefix=sorted.slice(0,end),past=new Set(prefix.map(tx=>idKey(tx.id)));
  assert(prefix.every(tx=>ledger.get(idKey(tx.id)).dependencies.every(dep=>past.has(dep))),'sorted prefix not dependency closed');
  active={items:new Set(),calls:[]};const document=new CrdtDocument(prefix);active=undefined;prefixes++;
  const expected=decodedTables(prefix),actual=actualTables(document);
  assert.deepEqual(actual,expected);tableChecks+=actual.length;
  rowChecks+=actual.reduce((n,instance)=>n+instance.rows.length,0);
  tombstoneChecks+=actual.reduce((n,instance)=>n+instance.rows.filter(row=>row.deleted).length,0);
  if(prefix.length===events.length)fullTable={transactions:prefix,expected,actual};
 }
}
assert(checks>0);assert(dominanceChecks>0);assert(internalOriginChecks>0);assert(internalChildChecks>0);
assert(nonGlobalMax,'must exercise overlapping atomic run clocks');
assert(fullTable);assert(tombstoneChecks>0);
const noOpDelete=fullTable.actual.map(instance=>({...instance,rows:instance.rows.map(row=>({...row,deleted:false}))}));
assert.notDeepEqual(noOpDelete,fullTable.expected,'full-field check must reject no-op deletion');
const wrongInstance=fullTable.actual.map((instance,i)=>({...instance,instance:i===0?'wrong-instance':instance.instance}));
assert.notDeepEqual(wrongInstance,fullTable.expected,'full-field check must reject wrong instance ownership');
// Fabricated future-target delete is outside honest causal closure. Its
// tombstone affects text birth, but never changes a split marker's kind/flag.
const pendingRaw=new RgaText(),pendingId={sessionId:'raw',counter:1},markerId={sessionId:'raw',counter:2};
pendingRaw.delete([pendingId,markerId]);pendingRaw.insertRun(pendingId,START,'Q');pendingRaw.insertSplit(markerId,pendingId);
const pendingActual=[...pendingRaw.items.values()].map(row=>({id:row.id,originId:row.originId,kind:row.kind,content:row.content??null,deleted:row.deleted}));
assert.deepEqual(pendingActual,[{id:pendingId,originId:START,kind:'text',content:'Q',deleted:true},
 {id:markerId,originId:pendingId,kind:'split',content:null,deleted:false}]);
assert.notEqual(pendingActual[1].deleted,true);
console.log(JSON.stringify({name:'fabricated-pending-before-birth-full-fields',pending:[pendingId,markerId],rows:pendingActual,
 scope:'Direct raw primitive boundary, not a dependency-closed honestly issued version.'}));
console.log(JSON.stringify({name:'honest-full-prefix-stored-field-comparison',tableChecks,rowChecks,tombstoneChecks,fullTable,
 controls:{noOpDeleteRejected:true,wrongInstanceRejected:true},scope:'Expected full fields and pending sets decoded independently from literal atomic transactions; Map order is chronological, not traversal order.'}));
const honestDominanceChecks=dominanceChecks;
// Known-broken environment: the public API alone does not serialize sessions.
const same1=new Replica('same','one',initial),same2=new Replica('same','two',initial);
const one=same1.insertText(block,0,'X'),two=same2.insertText(block,0,'Y');
assert.deepEqual(one.id,two.id);assert.notDeepEqual(one,two);
assert.throws(()=>same1.receive(two),/reused with a different payload/);
// Known-broken message set: omit bootstrap dependencies from an honest tx.
active={items:new Set(),calls:[]};let missingCaught=false;
try{new CrdtDocument([ai]);}catch(e){missingCaught=/unknown origin/.test(e.message);}finally{active=undefined;}
assert(missingCaught,'instrumentation must reject missing-origin fixture');
const wrongClock=new RgaText();wrongClock.insertRun({sessionId:'old',counter:100},START,'Q');
active={items:new Set(),calls:[]};let dominanceCaught=false;
try{wrongClock.insertRun(ax.id,START,'X');}catch(e){dominanceCaught=/does not dominate/.test(e.message);}finally{active=undefined;}
assert(dominanceCaught,'instrumentation must catch broken child dominance');
console.log(JSON.stringify({name:'replay-prefix-structural-instrumentation',events:events.length,closedSets,prefixes,
 rgaEntryChecks:checks,childDominanceChecks:honestDominanceChecks,internalOriginChecks,internalChildChecks,nonGlobalMax,
 controls:{emptyRequestsNoEvent:true,duplicateDelivery:true,deleteReservationIsNotRgaItem:true,
   sameSessionCollisionDetected:true,missingDependencyDetected:true,brokenDominanceDetected:true},
 ledger:events,scope:'All causal ideals of one nine-event directed honest network; observes actual pinned RGA entry points during sorted full-transaction replay. No claim every source receive enforces closure or session serialization.'}));
