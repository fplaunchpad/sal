// Honest client selection versus a separately fabricated raw payload. This
// is a domain countermodel, not a newly discovered valid-request failure.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {createInitialTransactions,CrdtDocument} from './document.js';
import {START,idKey} from './ids.js';
import {iterateTextSliceTree} from './text-slice-tree.js';
const initial=createInitialTransactions('ab'),author=new Replica('S','S',initial),cut=author.splitBlock('block-A',1),target=cut.newBlockId;
assert.deepEqual(cut.transaction.id,{sessionId:'S',counter:3});
const honest=new Replica('H','H',author.transactions()),issued=honest.insertText(target,0,'X');
assert.equal(issued.operations[0].args.textInstanceId,'block-A');
assert.deepEqual(issued.operations[0].args.originId,{sessionId:'S',counter:3});
const raw=structuredClone(issued);raw.id={sessionId:'R',counter:4};
raw.operations[0].args.id=raw.id;raw.operations[0].args.textInstanceId=target;
raw.operations[0].args.originId=START;raw.operations[0].args.searchLabel='';
const rawDoc=new CrdtDocument([...author.transactions(),raw]),honestDoc=honest.document();
function inspect(d){return {text:d.blockText(target),characters:d.blockCharacters(target).map(c=>({id:c.item.id,instance:c.textInstanceId,text:c.text})),
 nodes:[...iterateTextSliceTree(d.blocks.get(target).title)].map(n=>({instance:n.textSlice.textInstanceId,start:n.textSlice.startItemId,stop:n.textSlice.endItemId})),
 titleRows:[...d.instances.get(target).rga.items.values()]};}
const a=inspect(rawDoc),b=inspect(honestDoc);
assert.equal(a.text,'Xb');assert.equal(b.text,'Xb');assert.equal(a.nodes.length,2);assert.equal(b.nodes.length,2);
assert.deepEqual(a.characters.map(c=>c.instance),[target,'block-A']);
assert.deepEqual(b.characters.map(c=>c.instance),['block-A','block-A']);
assert.notDeepEqual(a.characters.map(c=>c.instance),b.characters.map(c=>c.instance));
assert.equal(a.titleRows.length,1);assert.equal(b.titleRows.length,0);
assert.equal(a.titleRows[0].originId,START);assert.notEqual(a.titleRows.length,0);
console.log(JSON.stringify({name:'inactive-title-raw-vs-honest-selection',initial,split:cut,raw,issued,rawState:a,honestState:b,
 scope:'Raw payload names an existing created block/instance and START, yet populates its inactive own title. Honest zero-gap preparation chooses the inherited marker. Tree node count and visible text alone do not imply EmptyInactive; no ordinary client failure claimed.'}));
