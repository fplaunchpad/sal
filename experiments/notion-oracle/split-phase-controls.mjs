// Observational hooks around unchanged pinned primitives. No source private
// operation is reimplemented; command getters mark phase boundaries.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {CrdtDocument,BlockRecord,TextInstance,createInitialTransactions} from './document.js';
import {RgaText} from './rga.js';
import {TextSliceTreeNode,iterateTextSliceTree} from './text-slice-tree.js';
import {START,END,idKey} from './ids.js';
let active,blocks,instances;
function snapshot(stage){
 const groups=[...instances].map(([instance,value])=>{
  const physical=[START,...value.rga.orderedItems().map(item=>item.id)],refs=[];
  for(const block of blocks.values())for(const node of iterateTextSliceTree(block.title)){
   const s=node.textSlice;if(s.textInstanceId===instance)refs.push({owner:block.id,start:s.startItemId,stop:s.endItemId});
  }
  const pos=id=>physical.findIndex(value=>idKey(value)===idKey(id));refs.sort((a,b)=>pos(a.start)-pos(b.start));
  const counts=physical.map(()=>0);
  for(const ref of refs){const first=pos(ref.start),last=ref.stop===END?physical.length:pos(ref.stop);
   if(first>=0&&last>first)for(let i=first;i<last;i++)counts[i]++;}
  const adjacency=refs.length>0&&refs[0].start===START&&refs.every((ref,i)=>idKey(ref.stop)===idKey(refs[i+1]?.start??END));
  return {instance,physical,refs,counts,coverage:adjacency&&counts.every(n=>n===1),ownerUnique:new Set(refs.map(ref=>ref.owner)).size===refs.length};
 });
 active.records.push({stage,groups});
}
const set=Map.prototype.set,split=RgaText.prototype.insertSplit,detach=TextSliceTreeNode.prototype.detachFromParent,append=TextSliceTreeNode.prototype.appendChild;
Map.prototype.set=function(key,value){const result=set.call(this,key,value);
 if(active&&value instanceof BlockRecord)blocks=this;if(active&&value instanceof TextInstance)instances=this;return result;};
RgaText.prototype.insertSplit=function(...args){const result=split.apply(this,args);
 if(active&&idKey(args[0])===idKey(active.id))snapshot('marker-integrated-before-tree-split');return result;};
TextSliceTreeNode.prototype.detachFromParent=function(...args){const result=detach.apply(this,args);
 if(active&&active.moving&&idKey(this.textSlice.startItemId)===idKey(active.id))snapshot('detached-before-append');return result;};
TextSliceTreeNode.prototype.appendChild=function(...args){const result=append.apply(this,args);
 if(active&&active.moving&&this===blocks.get(active.target)?.title)snapshot('moved-to-destination');return result;};
function observe(prefix,tx,target){
 active={id:tx.id,target,moving:false,records:[]};blocks=undefined;instances=undefined;
 const wrapped={...tx,operations:tx.operations.map(op=>{
  const copy={...op};Object.defineProperty(copy,'command',{get(){
   if(op.command==='createBlock')snapshot('before-create');
   if(op.command==='splitText')snapshot('destination-created-before-marker');
   if(op.command==='moveTextSliceIntoBlock'){snapshot('tree-split-before-move');active.moving=true;}
   return op.command;}});return copy;
 })};
 const doc=new CrdtDocument([...prefix,wrapped]);snapshot('atomic-final');const records=active.records;active=undefined;
 return {transactions:[...prefix,tx],records,view:doc.aliveBlocks().map(b=>({id:b.id,text:doc.blockText(b.id)}))};
}
try{
 const initial=createInitialTransactions('ab'),r=new Replica('S','S',initial),cut=r.splitBlock('block-A',1);
 const literal=observe(initial,cut.transaction,cut.newBlockId);
 assert.deepEqual(cut.transaction.id,{sessionId:'S',counter:3});
 assert.deepEqual(literal.view,[{id:'block-A',text:'a'},{id:'S-block-3',text:'b'}]);
 for(const stage of literal.records){const old=stage.groups.find(g=>g.instance==='block-A');
  if(stage.stage==='tree-split-before-move'){
   assert.equal(old.coverage,true);assert.equal(old.ownerUnique,false);
   assert.deepEqual(old.refs,[{owner:'block-A',start:START,stop:{sessionId:'S',counter:3}},
    {owner:'block-A',start:{sessionId:'S',counter:3},stop:END}]);
  }else if(stage.stage==='detached-before-append'){assert.equal(old.coverage,false);assert.notDeepEqual(old.counts,[1,1,1,1]);}
  else assert(stage.groups.every(g=>g.coverage&&g.ownerUnique));
 }
 const final=literal.records.at(-1),postSplit=literal.records.find(s=>s.stage==='tree-split-before-move');
 assert.notDeepEqual(postSplit.groups,final.groups,'Skipping move must be rejected as final ownership');
 assert.deepEqual(final.groups.map(g=>g.refs),[
  [{owner:'block-A',start:START,stop:{sessionId:'S',counter:3}},{owner:'S-block-3',start:{sessionId:'S',counter:3},stop:END}],
  [{owner:'S-block-3',start:START,stop:END}]]);
 console.log(JSON.stringify({name:'hand-derived-ab-atomic-split-phases',...literal,
  scope:'Source hooks observe create, marker integration, tree split, detach, append. Temporary duplicate owner and detached gap are internal phases; final ownership includes the empty title cell.'}));
 // A further honest inherited interval split after deleting its visible text.
 r.deleteText(cut.newBlockId,0,1);const dead=r.transactions();
 const second=r.splitBlock(cut.newBlockId,0),follow=observe(dead,second.transaction,second.newBlockId);
 assert(follow.records.at(-1).groups.every(g=>g.coverage&&g.ownerUnique));
 assert(follow.records.find(s=>s.stage==='tree-split-before-move').groups.some(g=>g.coverage&&!g.ownerUnique));
 assert.deepEqual(follow.view.map(b=>b.text),['a','','']);
 assert.notDeepEqual(follow.view.map(b=>b.text),['a','b','']);
 console.log(JSON.stringify({name:'honest-hidden-inherited-split-phases',...follow,
  scope:'All-deleted inherited leaf, empty slices, and inactive title roots; source atomic final coverage and per-instance owner uniqueness restored.'}));
}finally{Map.prototype.set=set;RgaText.prototype.insertSplit=split;TextSliceTreeNode.prototype.detachFromParent=detach;TextSliceTreeNode.prototype.appendChild=append;active=undefined;}
