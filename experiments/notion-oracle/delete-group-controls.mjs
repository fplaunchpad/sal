// Focused honest core deletion: inherited instance, Unicode session order,
// source ID range sorting versus physical character selection.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {expandIdRanges,idKey} from './ids.js';
const seed=new Replica('seed','seed',[]),original=seed.createBlock().newBlockId;
seed.insertText(original,0,'abcd');const cut=seed.splitBlock(original,2),target=cut.newBlockId;
const emoji=new Replica('😀','emoji',seed.transactions()),privateUse=new Replica('\uE000','private',seed.transactions());
const txEmoji=emoji.insertText(target,0,'XY'),txPrivate=privateUse.insertText(target,0,'UV');
const merged=[...seed.transactions(),txEmoji,txPrivate];
const r=new Replica('delete','delete',merged),before=r.document(),chars=before.blockCharacters(target);
assert.equal(before.blockText(target),'UVXYcd');assert.notEqual(before.blockText(target),'XYUVcd');
const physicalSelection=chars.slice(1,99),expected=[
 {sessionId:'seed',counter:4},{sessionId:'seed',counter:5},
 {sessionId:'😀',counter:7},{sessionId:'😀',counter:8},
 {sessionId:'\uE000',counter:8}];
const tx=r.deleteText(target,1,99);assert.equal(tx.operations.length,1);
const op=tx.operations[0];assert.equal(op.args.textInstanceId,original);assert.notEqual(op.args.textInstanceId,target);
assert.deepEqual(op.args.idRanges,[[expected[0],2],[expected[2],2],[expected[4],1]]);
const expanded=expandIdRanges(op.args.idRanges);assert.deepEqual(expanded,expected);
assert.deepEqual(expanded.map(idKey).sort(),physicalSelection.map(c=>idKey(c.item.id)).sort());
assert.notDeepEqual(expanded.map(idKey),physicalSelection.map(c=>idKey(c.item.id)));
assert(!expanded.some(id=>idKey(id)===idKey(cut.transaction.id)));
assert.equal(r.document().blockText(target),'U');assert.notEqual(r.document().blockText(target),'UVXYcd');
console.log(JSON.stringify({name:'honest-inherited-delete-source-range-order',initial:seed.transactions(),concurrent:[txEmoji,txPrivate],
 before:{text:before.blockText(target),characters:chars.map(c=>({instance:c.textInstanceId,id:c.item.id,text:c.text}))},
 selected:physicalSelection.map(c=>({instance:c.textInstanceId,id:c.item.id})),transaction:tx,expanded,
 after:r.document().aliveBlocks().map(b=>({id:b.id,text:r.document().blockText(b.id)})),
 scope:'One honest core active instance; physical selection differs from wire ID-sort order but target sets agree; inherited split marker and empty title excluded.'}));
for(const [start,end] of [[0,0],[99,100],[3,1]]){
 const q=new Replica('bounds','bounds',merged),snapshot={clock:{...q.clock},transactions:q.transactions()};
 assert.equal(q.deleteText(target,start,end),undefined);assert.deepEqual({...q.clock},snapshot.clock);
 assert.deepEqual(q.transactions(),snapshot.transactions);
 const marker=q.document().instances.get(original).rga.items.get(idKey(cut.transaction.id));
 assert.equal(marker.kind,'split');assert.equal(marker.deleted,false);assert.notEqual(marker.deleted,true);
 console.log(JSON.stringify({name:'honest-empty-clamped-delete-no-event',start,end,snapshot,marker,
  scope:'Nonnegative JS clamping/reversed empty range selects no group and reserves no transaction; split marker remains unchanged.'}));
}
{
 const beforeSecond=r.document(),second=r.deleteText(target,0,99),ids=expandIdRanges(second.operations[0].args.idRanges);
 assert.deepEqual(ids,[{sessionId:'\uE000',counter:7}]);assert.notDeepEqual(ids,expected);
 assert.equal(second.operations[0].args.textInstanceId,original);
 assert.equal(r.document().blockText(target),'');
 const marker=r.document().instances.get(original).rga.items.get(idKey(cut.transaction.id));
 assert.equal(marker.deleted,false);
 console.log(JSON.stringify({name:'honest-delete-excludes-prior-tombstones',before:beforeSecond.blockText(target),transaction:second,expanded:ids,marker,
  scope:'A second clamped deletion targets only the remaining visible U, excluding previously tombstoned characters and inherited marker.'}));
}
