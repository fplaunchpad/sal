import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {IdentityDocument} from './identity-spec.mjs';
import {iterateTextSliceTree,itemsInTextSlice} from './text-slice-tree.js';
import {compareOpIds} from './ids.js';
const key=id=>typeof id==='string'?id:`${id.sessionId}:${id.counter}`;
function decode(tx) {
  return tx.operations.flatMap(op=>{
    const a=op.args;
    if(op.command==='createBlock')return [{kind:'create',block:a.blockId,after:a.afterBlockId,instance:a.titleTextInstanceId}];
    if(op.command==='insertText')return [{kind:'insert',instance:a.textInstanceId,origin:key(a.originId),characters:[...a.content].map((text,i)=>({id:key({...a.id,counter:a.id.counter+i}),text}))}];
    if(op.command==='deleteText')return [{kind:'delete',instance:a.textInstanceId,ids:a.idRanges.flatMap(([id,n])=>Array.from({length:n},(_,i)=>key({...id,counter:id.counter+i})))}];
    if(op.command==='splitText')return [{kind:'split',instance:a.textInstanceId,origin:key(a.originId),id:key(a.id),target:tx.operations.find(x=>x.command==='moveTextSliceIntoBlock').args.targetBlockId}];
    if(op.command==='moveTextSliceIntoBlock')return [];
    throw Error('outside core');
  });
}
const view=r=>{const d=r.document();return d.aliveBlocks().map(b=>[b.id,d.blockText(b.id)]);};
function specification(txs,Model=IdentityDocument) {
  const s=new Model();
  for(const tx of [...txs].sort((a,b)=>a.id.counter-b.id.counter||(a.id.sessionId<b.id.sessionId?-1:a.id.sessionId>b.id.sessionId?1:0)))
    for(const cmd of decode(tx))s.step(cmd);
  return s;
}
let checks=0,structuralChecks=0,slotIntervalChecks=0,permanentlyEmptyRootChecks=0,titleOwnershipChecks=0,maxPopulatedSlices=0,maxBranching=0,maxNodes=0;
function inspect(r,spec) {
  const d=r.document();
  const titles=d.aliveBlocks().map(b=>b.title.textSlice.textInstanceId);
  assert.equal(new Set(titles).size,titles.length,'two block title roots share an instance');
  for(const b of d.aliveBlocks()) {
    const nodes=[...iterateTextSliceTree(b.title)];
    const populated=nodes.filter(n=>itemsInTextSlice(n.textSlice,d.instances.get(n.textSlice.textInstanceId).rga).some(i=>i.kind==='text'));
    const branching=Math.max(...nodes.map(n=>n.children.length));
    maxPopulatedSlices=Math.max(maxPopulatedSlices,populated.length);maxBranching=Math.max(maxBranching,branching);maxNodes=Math.max(maxNodes,nodes.length);structuralChecks++;
    assert(populated.length<=1,'more than one populated slice in a no-merge block');
    assert(branching<=1,'branching slice tree in no-merge fragment');
    assert(nodes.length<=2,'more than root plus one slice in no-merge block');
    titleOwnershipChecks++;
    assert.equal(b.title.textSlice.textInstanceId,b.id,'block title root does not own its fresh instance');
    if(nodes.length===2) {
      permanentlyEmptyRootChecks++;
      const root=nodes[0].textSlice,child=nodes[1].textSlice;
      assert.equal(d.instances.get(root.textInstanceId).rga.items.size,0,'attached root has physical RGA items');
      assert.notEqual(root.textInstanceId,child.textInstanceId,'attached slice shares title instance');
      assert.equal(root.startItemId,'start');assert.equal(root.endItemId,'end');
      assert.equal(root.searchLabel,'');
    }
  }
  // Retained semantic slots assigned to each block/instance must form a single
  // interval in that instance's full source order, including tombstones and
  // split markers. Include the START sentinel as position zero.
  for(const b of spec.blocks) for(const instance of new Set(b.slots.map(s=>s.instance))) {
    const ids=b.slots.filter(s=>s.instance===instance).map(s=>s.id);
    const source=['start',...d.instances.get(instance).rga.traversal().items.map(i=>key(i.id))];
    const first=source.indexOf(ids[0]);slotIntervalChecks++;
    assert(first>=0,'missing retained slot in source order');
    assert.deepEqual(source.slice(first,first+ids.length),ids,'block retained slots not one source-order interval');
  }
}
function check(r,history) {
  checks++;
  try {const spec=specification(r.transactions());assert.deepEqual(spec.view(),view(r));inspect(r,spec);}
  catch(e) {console.log(JSON.stringify({name:'core-adversarial-counterexample',history,transactions:r.transactions(),actual:view(r),expected:specification(r.transactions()).view(),error:e.message}));process.exit(1);}
}
// Same decoder/comparison detects a deliberately broken run insertion rule.
class TruncateRun extends IdentityDocument {
  step(cmd){return super.step(cmd.kind==='insert'?{...cmd,characters:cmd.characters.slice(0,1)}:cmd);}
}
const control=new Replica('control','control',[]),cb=control.createBlock().newBlockId;control.insertText(cb,0,'a😀');
assert.deepEqual(specification(control.transactions()).view(),view(control));
assert.notDeepEqual(specification(control.transactions(),TruncateRun).view(),view(control));
console.log(JSON.stringify({name:'core-adversarial-mutant',mutant:'truncate-multiscalar-run',detected:true}));
// JS compares strings lexicographically by UTF-16 units, not Unicode scalars.
// Emoji starts D83D, below E000, despite its scalar value being greater.
const emoji='😀',privateUse='\uE000';
assert.equal(compareOpIds({counter:7,sessionId:emoji},{counter:7,sessionId:privateUse}),-1);
assert.equal(compareOpIds({counter:7,sessionId:privateUse},{counter:7,sessionId:emoji}),1);
assert.notEqual(emoji.codePointAt(0)<privateUse.codePointAt(0),emoji<privateUse);
console.log(JSON.stringify({name:'source-session-utf16-order-control',sessions:[emoji,privateUse],
  units:[[0xD83D,0xDE00],[0xE000]],emojiBeforePrivateUse:true,scalarOrderWouldReverse:true}));

// Exhaustive short directed split/run-insert pairs, scalar-index positions,
// swapped IDs and unequal valid clock reservations; repeat delivery as control.
let directed=0;
for(const text of ['','ab','a😀b','e\u0301']) for(let split=0;split<=[...text].length;split++)
for(let index=0;index<=[...text].length;index++) for(const sessions of [['A','B'],['B','A'],[emoji,privateUse],[privateUse,emoji]]) for(const gaps of [[0,0],[9,0],[0,9]]) {
  const seed=new Replica('seed','seed',[]),block=seed.createBlock().newBlockId;seed.insertText(block,0,text);
  const a=new Replica(sessions[0],'a',seed.transactions()),b=new Replica(sessions[1],'b',seed.transactions());
  if(gaps[0])a.clock.reserve(gaps[0]);if(gaps[1])b.clock.reserve(gaps[1]);
  const splitTx=a.splitBlock(block,split).transaction,insert=b.insertText(block,index,'🦀λz');
  const history={kind:'directed-split-run-insert',text,split,index,sessions,gaps,transactions:[splitTx,insert]};
  check(a,history);check(b,history);a.receive(insert);a.receive(insert);b.receive(splitTx);check(a,history);check(b,history);assert.deepEqual(view(a),view(b));directed++;
}

// Explicit all-anchor deletion, then repeated concurrent zero-boundary splits
// and sequential reuse of each session. These controls do not rely on random
// generation happening to choose the difficult shape.
let anchorHistories=0;
for(const splitIndex of [0,1,2,3]) {
 const seed=new Replica('seed','seed',[]),block=seed.createBlock().newBlockId;seed.insertText(block,0,'a😀b');
 const a=new Replica('delete','delete',seed.transactions()),b=new Replica('split','split',seed.transactions());
 const del=a.deleteText(block,0,3),cut=b.splitBlock(block,splitIndex).transaction;a.receive(cut);a.receive(del);
 let transactions=a.transactions(),history=[del,cut];check(a,{kind:'deleted-original-anchors',splitIndex,history});
 for(let round=0;round<4;round++) {
   const branches=[];
   for(let branch=0;branch<3;branch++) {
    const r=new Replica(`repeat${round}b${branch}`,'repeat',transactions),blocks=view(r),target=blocks[branch%blocks.length][0];
    const split=r.splitBlock(target,0),insert=r.insertText(split.newBlockId,0,'λ🦀');
    history.push(split.transaction,insert);check(r,{kind:'repeated-zero-splits-after-delete-all',splitIndex,round,branch,history});branches.push(r.transactions());
   }
   const collector=new Replica('collector','collector',transactions);for(const tx of branches.flat())collector.receive(tx);
   transactions=collector.transactions();check(collector,{kind:'repeated-zero-splits-after-delete-all',splitIndex,round,history});
 }
 anchorHistories++;
}

const seeds=[0x134ab912,0x514a2d19,0xabcdef01];let generatedStates=0;
for(const seedValue of seeds) {
 let rng=seedValue;const random=n=>{rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return(rng>>>0)%n;};
 for(let trial=0;trial<20;trial++) {
  const seed=new Replica('seed','seed',[]),block=seed.createBlock().newBlockId;seed.insertText(block,0,['','a😀b','abcd'][trial%3]);
  let txs=seed.transactions(),history=[];
  for(let round=0;round<6;round++) {
   const branches=[];
   for(let branch=0;branch<3;branch++) {
    // Each session is unique concurrently and reused for three sequential local
    // operations. Reusing one session concurrently would violate freshness.
    const r=new Replica(`s${trial}r${round}b${branch}`,'branch',txs);if(branch===1)r.clock.reserve(random(12)+1);
    for(let step=0;step<3;step++) {
     const blocks=view(r),[target,text]=blocks[random(blocks.length)],n=[...text].length,index=random(n+1),kind=random(5);let result,request;
     if(kind===0){const content=['XY','😀λ','e\u0301','🦀'][random(4)];result=r.insertText(target,index,content);request={kind:'insert',target,index,content};}
     if(kind===1){const start=random(n+1),end=start+random(n-start+1);result=r.deleteText(target,start,end);request={kind:'delete',target,start,end};}
     if(kind===2){result=r.splitBlock(target,index);request={kind:'split',target,index};}
     if(kind===3){result=r.createBlock(random(2)?target:undefined);request={kind:'create',after:result.transaction.operations[0].args.afterBlockId};}
     if(kind===4){result=r.deleteText(target,0,n);request={kind:'delete-all',target};}
     history.push({round,branch,step,request,transaction:result?.transaction??result});check(r,{seed:seedValue,trial,steps:history});
    }
    branches.push(r.transactions());
   }
   const collector=new Replica('collector','collector',txs);
   for(const tx of branches.flat().reverse())collector.receive(tx);
   for(const tx of branches.flat())collector.receive(tx);
   txs=collector.transactions();check(collector,{seed:seedValue,trial,steps:history});generatedStates++;
  }
 }
}
console.log(JSON.stringify({name:'core-adversarial-summary',seeds:seeds.map(x=>'0x'+x.toString(16)),trialsPerSeed:20,rounds:6,branches:3,localRequestsPerBranch:3,directedPairs:directed,deletedAnchorRepeatedSplitHistories:anchorHistories,generatedJoinStates:generatedStates,checks,structuralChecks,slotIntervalChecks,permanentlyEmptyRootChecks,titleOwnershipChecks,maxPopulatedSlices,maxBranching,maxNodes,discarded:0,result:'pass',scope:'core create/split/run-insert/delete; observed no-merge tree-chain and populated-slice bounds are finite evidence, not proofs; candidate ID-sorted atomic-transaction witness'}));
