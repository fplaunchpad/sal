// Directed atomic-boundary checks, not an exhaustive network campaign.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {iterateTextSliceTree} from './text-slice-tree.js';
import {START,END,idKey} from './ids.js';
function inspect(r){
 const d=r.document(),groups=new Map([...d.instances].map(([k])=>[k,[]]));
 for(const b of d.blocks.values())for(const node of iterateTextSliceTree(b.title)){
  const s=node.textSlice;groups.get(s.textInstanceId).push({block:b.id,start:s.startItemId,stop:s.endItemId});
 }
 return [...groups].map(([instance,slices])=>{
  const physical=d.instances.get(instance).rga.orderedItems().map(x=>x.id);
  const pos=x=>x===START?-1:physical.findIndex(v=>idKey(v)===idKey(x));
  slices.sort((a,b)=>pos(a.start)-pos(b.start));
  const adjacent=slices.length>0&&slices[0].start===START&&slices.every((s,i)=>
   (s.start===START||pos(s.start)>=0)&&idKey(s.stop)===idKey(slices[i+1]?.start??END)&&
   (s.stop===END||pos(s.start)<pos(s.stop)));
  return {instance,physical,slices,adjacent};
 });
}
const seed=new Replica('seed','seed',[]),original=seed.createBlock().newBlockId;
seed.insertText(original,0,'a😀bc');
const A=new Replica('A','A',seed.transactions()),B=new Replica('B','B',seed.transactions());
const cutA=A.splitBlock(original,1).transaction,cutB=B.splitBlock(original,3).transaction;
const bundles=[[],[cutA],[cutB],[cutA,cutB]];
let checks=0;
for(const [index,extra] of bundles.entries()){
 const r=new Replica(`follow${index}`,`follow${index}`,[...seed.transactions(),...extra]);
 const history=[];
 function check(label){const groups=inspect(r);assert(groups.every(g=>g.adjacent));checks+=groups.length;
  history.push({label,transactions:r.transactions(),groups});}
 check('concurrent-prefix');
 const live=r.document().aliveBlocks();
 for(const block of live){const n=r.document().blockCharacters(block.id).length;
  r.deleteText(block.id,0,n);check('delete-all-visible');
  r.insertText(block.id,0,'XY');check('insert-after-all-deleted');
  const cut=r.splitBlock(block.id,0);check('split-empty-left');
  r.splitBlock(cut.newBlockId,1);check('repeat-split-in-inherited-interval');}
 assert.notEqual(history.at(-1).groups.length,0);
 console.log(JSON.stringify({name:'honest-atomic-endpoint-adjacency',index,history,
  scope:'Four dependency-closed concurrent-split versions and directed local followups; Map/display order ignored, slices sorted by physical start.'}));
}
{
 const issued=new Replica('author','author',seed.transactions());const tx=issued.insertText(original,1,'X');
 const incomplete=new Replica('receiver','receiver',[tx]),groups=inspect(incomplete);
 assert(groups.some(g=>!g.adjacent));assert.notDeepEqual(groups,[]);
 console.log(JSON.stringify({name:'raw-incomplete-receipt-is-not-covered',transactions:[tx],groups,
  scope:'A received payload without its block/origin dependencies creates an instance with no covering slices. Excluded from honest closed versions.'}));
}
console.log(JSON.stringify({name:'endpoint-adjacency-count',instanceChecks:checks,versions:4}));
