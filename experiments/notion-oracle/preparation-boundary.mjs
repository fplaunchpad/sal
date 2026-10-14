// Targeted source-boundary probes, not another broad differential campaign.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {createInitialTransactions} from './document.js';
const view=r=>{const d=r.document();return d.aliveBlocks().map(b=>({id:b.id,text:d.blockText(b.id),
  atomCount:d.blockCharacters(b.id).length}));};
const location=(r,block,index)=>{const {textInstanceId,originId,searchLabel}=r.document().locateInsertion(block,index);return {textInstanceId,originId,searchLabel};};
{
 const seed=createInitialTransactions('ab'),r=new Replica('next','next',seed);
 assert.equal(seed.length,1);assert.equal(seed[0].operations.length,2);
 assert.deepEqual(seed[0].id,seed[0].operations[1].args.id);
 const inserted=r.insertText('block-A',1,'X');assert.equal(inserted.id.counter,3);
 assert.notEqual(inserted.id.counter,2);
 console.log(JSON.stringify({name:'actual-demo-bootstrap-group',initial:seed,generated:inserted,after:view(r),
   note:'Bootstrap create and insertion share one atomic transaction and first item key.'}));
}
{
 const r=new Replica('S','S',[]),original=r.createBlock().newBlockId;r.insertText(original,0,'ab');
 const split=r.splitBlock(original,0),target=split.newBlockId,deleted=r.deleteText(target,0,2);
 const chosen=location(r,target,0);
 assert.equal(chosen.textInstanceId,original);assert.deepEqual(chosen.originId,split.transaction.id);
 assert.notEqual(chosen.textInstanceId,target);
 const inserted=r.insertText(target,0,'X');assert.equal(view(r)[1].text,'X');
 console.log(JSON.stringify({name:'all-deleted-attached-slice-preparation',transactions:r.transactions(),split:split.transaction,deleted,
   target,chosen,generated:inserted,after:view(r),note:'Fallback chooses the last leaf boundary, not the unused title root.'}));
}
{
 const r=new Replica('S','S',[]),block=r.createBlock().newBlockId;
 const high=r.insertText(block,0,'\uD83D'),low=r.insertText(block,1,'\uDE00'),before=view(r);
 assert.equal(before[0].text,'😀');assert.equal(before[0].atomCount,2);assert.equal([...before[0].text].length,1);
 const split=r.splitBlock(block,1),after=view(r);
 assert.equal(after[0].text,'\uD83D');assert.equal(after[1].text,'\uDE00');
 assert.notDeepEqual(after.map(b=>b.text),['😀','']);
 console.log(JSON.stringify({name:'lone-surrogates-cross-run-coalesce',transactions:r.transactions(),insertions:[high,low],before,
   split:split.transaction,after,note:'Source accepts lone UTF16 surrogates; displayed concatenation can coalesce two editing atoms into one Unicode scalar. Restrict well-formed inserted strings or retain this atom/string distinction.'}));
}
{
 const seed=new Replica('seed','seed',[]),block=seed.createBlock().newBlockId;seed.insertText(block,0,'a');
 const author=new Replica('author','author',seed.transactions()),tx=author.insertText(block,1,'X');
 const receiver=new Replica('receiver','receiver',[]);assert.equal(receiver.receive(tx),true);
 const beforeDependencies=view(receiver);
 assert.deepEqual(beforeDependencies,[]);assert.notDeepEqual(beforeDependencies.map(b=>b.text),['aX']);
 for(const dependency of seed.transactions())receiver.receive(dependency);
 assert.equal(view(receiver)[0].text,'aX');
 console.log(JSON.stringify({name:'receipt-does-not-enforce-query-readiness',dependent:tx,dependencies:seed.transactions(),
   beforeDependencies,after:view(receiver),note:'receive does not enforce causal closure. With no created blocks, querying this dependency-incomplete state returns an empty document; adding dependencies reconstructs aX.'}));
}
