// Reuse the published nine-event directed ledger without changing its runner.
// Suppress its output here; its existing assertions still execute.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {CrdtDocument,createInitialTransactions} from './document.js';
import {START} from './ids.js';
const collected=[],write=console.log;
try{console.log=line=>collected.push(JSON.parse(line));await import('./replay-prefix-instrumentation.mjs');}
finally{console.log=write;}
const ledger=collected.find(row=>row.name==='replay-prefix-structural-instrumentation').ledger;
const key=id=>`${id.sessionId}:${id.counter}`;
const ascending=(a,b)=>a.id.counter-b.id.counter||(a.id.sessionId<b.id.sessionId?-1:a.id.sessionId>b.id.sessionId?1:0);
function classify(transactions){
 const doc=new CrdtDocument(transactions),expected=new Set(),splitTitles=new Set(),leaves=[];
 for(const tx of transactions){const split=tx.operations.some(op=>op.command==='splitText');
  for(const op of tx.operations)if(op.command==='createBlock')
   (split?splitTitles:expected).add(op.args.titleTextInstanceId);}
 for(const block of doc.blocks.values()){
  const root=block.title;assert(root.children.length<=1);
  const leaf=root.children[0]??root;assert.equal(leaf.children.length,0);
  leaves.push({owner:block.id,instance:leaf.textSlice.textInstanceId,start:leaf.textSlice.startItemId});
 }
 const actual=new Set(leaves.map(leaf=>leaf.instance));
 assert.deepEqual([...actual].sort(),[...expected].sort());
 for(const title of splitTitles)assert(!actual.has(title));
 return {expected:[...expected].sort(),actual:[...actual].sort(),excludedSplitTitles:[...splitTitles].sort(),leaves,
  view:doc.aliveBlocks().map(block=>({id:block.id,text:doc.blockText(block.id)}))};
}
let closedSets=0,prefixes=0,activeMembershipChecks=0,excludedTitleChecks=0;
for(let mask=0;mask<2**ledger.length;mask++){
 const selected=ledger.filter((_,i)=>mask&(2**i)),keys=new Set(selected.map(entry=>key(entry.tx.id)));
 if(selected.some(entry=>entry.dependencies.some(dep=>!keys.has(dep))))continue;
 closedSets++;const sorted=selected.map(entry=>entry.tx).sort(ascending);
 for(let end=0;end<=sorted.length;end++){
  const result=classify(sorted.slice(0,end));prefixes++;
  activeMembershipChecks+=result.actual.length;excludedTitleChecks+=result.excludedSplitTitles.length;
 }
}
assert.equal(closedSets,40);assert.equal(prefixes,238);assert(excludedTitleChecks>0);
console.log(JSON.stringify({name:'active-instance-canonical-prefix-classification',events:ledger.length,closedSets,prefixes,
 activeMembershipChecks,excludedTitleChecks,
 scope:'All canonical atomic prefixes of the existing nine-event honest network. Expected set comes from literal bootstrap/standalone creates; actual set comes from structural leaves, regardless of visibility.'}));
const r=new Replica('S','S',createInitialTransactions('ab')),history=[];
function record(label){history.push({label,transactions:r.transactions(),classification:classify(r.transactions())});}
record('bootstrap');const first=r.splitBlock('block-A',1);record('split-destination');
assert.deepEqual(first.transaction.id,{sessionId:'S',counter:3});
const standalone=r.createBlock(first.newBlockId);assert.equal(standalone.newBlockId,'S-block-4');record('standalone-empty-create');
r.deleteText('block-A',0,1);r.deleteText(first.newBlockId,0,1);record('all-text-deleted');
r.splitBlock(first.newBlockId,0);record('repeat-empty-inherited-split');
r.splitBlock(standalone.newBlockId,0);record('split-empty-standalone-root');
assert.deepEqual(history.at(-1).classification.actual,['S-block-4','block-A']);
assert.notDeepEqual(history.at(-1).classification.actual,['S-block-3','S-block-4','block-A']);
assert(history.at(-1).classification.view.every(block=>block.text===''));
console.log(JSON.stringify({name:'hand-derived-empty-root-creator-classification',history,
 scope:'Bootstrap and standalone S@4 create stay active after deletion and empty repeated splits; destination title instances never join the leaf-instance set.'}));
const prefix=r.transactions(),honest=r.insertText(first.newBlockId,0,'X'),raw=structuredClone(honest);
assert.deepEqual(raw.id,{sessionId:'S',counter:9});raw.operations[0].args.textInstanceId=first.newBlockId;
raw.operations[0].args.originId=START;raw.operations[0].args.searchLabel='';
const rawDoc=new CrdtDocument([...prefix,raw]),rawClassification=classify([...prefix,raw]);
assert.equal(rawDoc.instances.get(first.newBlockId).rga.items.size,1);
assert(!rawClassification.actual.includes(first.newBlockId));
assert.deepEqual(rawClassification.actual,['S-block-4','block-A']);
assert.notEqual(rawDoc.instances.get(first.newBlockId).rga.items.size,0);
console.log(JSON.stringify({name:'raw-inactive-title-does-not-add-active-leaf-instance',raw,classification:rawClassification,
 populatedInactiveTitle:first.newBlockId,ownItems:[...rawDoc.instances.get(first.newBlockId).rga.items.values()],
 scope:'Fabricated raw choice violates physical inactive-title emptiness while the structural active-instance classification remains unchanged. Not an honest request or new demo bug.'}));
{
 const independent=new Replica('@','no-initial-receipt',[]),created=independent.createBlock();
 assert.deepEqual(created.transaction.id,{sessionId:'@',counter:1});
 const before=classify(independent.transactions());assert.deepEqual(before.actual,['@-block-1']);
 const bootstrap=createInitialTransactions('ab')[0];independent.receive(bootstrap);
 const joined=independent.document(),after=classify(independent.transactions());
 assert.deepEqual(joined.transactions.map(tx=>tx.id),[{sessionId:'@',counter:1},{sessionId:'A',counter:1}]);
 assert.notDeepEqual(joined.transactions.map(tx=>tx.id),[{sessionId:'A',counter:1},{sessionId:'@',counter:1}]);
 assert.deepEqual([...joined.blocks.keys()],['@-block-1','block-A']);
 assert.deepEqual(joined.aliveBlocks().map(block=>({id:block.id,text:joined.blockText(block.id)})),
  [{id:'block-A',text:'ab'},{id:'@-block-1',text:''}]);
 assert.deepEqual(after.actual,['@-block-1','block-A']);
 console.log(JSON.stringify({name:'honest-independent-create-before-bootstrap-canonical-key',transactions:independent.transactions(),
 canonical:joined.transactions,before,after,mapOrder:[...joined.blocks.keys()],
 scope:'Public empty-receipt create is valid at @1; later joining A1 bootstrap sorts it second. Refutes bootstrap-first replay assumption, not a demo bug.'}));
}
