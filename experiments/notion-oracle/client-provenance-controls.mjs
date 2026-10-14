// Directed source API domain and preparation provenance, with fabricated raw
// payload control kept distinct from honestly issued histories.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {CrdtDocument} from './document.js';
import {iterateTextSliceTree,textSliceContainsItem} from './text-slice-tree.js';
const view=d=>d.aliveBlocks().map(b=>({id:b.id,text:d.blockText(b.id)}));
const seed=new Replica('seed','seed',[]),original=seed.createBlock().newBlockId;
seed.insertText(original,0,'abc');
{
 const r=new Replica('C','C',seed.transactions()),before={clock:{...r.clock},transactions:r.transactions()};
 assert.throws(()=>r.createBlock('missing'),/Cannot create a block after unknown block missing/);
 assert.deepEqual({...r.clock},before.clock);assert.deepEqual(r.transactions(),before.transactions);
 const valid=r.createBlock(original),raw=structuredClone(valid.transaction);
 raw.operations[0].args.afterBlockId='missing';
 const d=new CrdtDocument([...seed.transactions(),raw]);
 assert.deepEqual(d.aliveBlocks().map(b=>b.id),[valid.newBlockId,original]);
 assert.notDeepEqual(d.aliveBlocks().map(b=>b.id),[original,valid.newBlockId]);
 console.log(JSON.stringify({name:'public-create-rejects-raw-missing-predecessor-falls-front',before,valid,raw,rawView:view(d),
  scope:'Rejected ordinary request does not reserve; fabricated raw payload is accepted by document dispatch and inserted at front.'}));
}
{
 const r=new Replica('A','A',seed.transactions()),cut=r.splitBlock(original,1),target=cut.newBlockId;
 const chosen=[];
 for(const hidden of [false,true]){
  if(hidden)r.deleteText(target,0,r.document().blockCharacters(target).length);
  const d=r.document(),zero=d.locateInsertion(target,0);
  assert.equal(zero.textInstanceId,original);assert.deepEqual(zero.originId,cut.transaction.id);
  assert.notEqual(zero.textInstanceId,target);
  chosen.push({hidden,instance:zero.textInstanceId,origin:zero.originId,label:zero.searchLabel,view:view(d)});
 }
 const tx=r.insertText(target,0,'X');assert.equal(r.document().blockText(target),'X');
 console.log(JSON.stringify({name:'honest-zero-gap-active-selection',transactions:r.transactions(),target,chosen,inserted:tx,
  scope:'Both visible and all-deleted inherited intervals select their active marker boundary, excluding empty fresh title instance.'}));
}
{
 const A=new Replica('A','A',seed.transactions()),B=new Replica('B','B',seed.transactions());
 const cutA=A.splitBlock(original,1),local=B.document(),chosen=local.locateInsertion(original,2);
 const predecessor=local.blockCharacters(original)[1];
 assert.deepEqual(chosen.originId,predecessor.item.id);assert.equal(chosen.textInstanceId,predecessor.textInstanceId);
 const cutB=B.splitBlock(original,2),preReplay=new CrdtDocument([...seed.transactions(),cutA.transaction]);
 const owners=[];
 for(const block of preReplay.blocks.values())for(const node of iterateTextSliceTree(block.title)){
  const s=node.textSlice;
  if(s.textInstanceId===chosen.textInstanceId&&textSliceContainsItem(s,preReplay.instances.get(s.textInstanceId).rga,chosen.originId))owners.push(block.id);
 }
 assert.deepEqual(owners,[cutA.newBlockId]);assert.notDeepEqual(owners,[original]);
 const merged=new CrdtDocument([...seed.transactions(),cutA.transaction,cutB.transaction]);
 assert.deepEqual(view(merged).map(b=>b.text),['a','c','b']);assert.notDeepEqual(view(merged).map(b=>b.text),['a','bc','']);
 console.log(JSON.stringify({name:'honest-local-predecessor-replay-owner-changes',seed:seed.transactions(),cutA,cutB,
  selected:{instance:chosen.textInstanceId,origin:chosen.originId,predecessor:predecessor.item.id},ownersBeforeConsumer:owners,
  requestedBlock:original,merged:view(merged),scope:'Both requests are locally valid. Prior concurrent split moves the consumer origin to another block; requiring replay owner=requested block would reject honest transactions.'}));
}
