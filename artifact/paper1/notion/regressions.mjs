// Known failures of the ordinary local request contract, positively and
// negatively controlled. Exit success means the counterexamples reproduce.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {debugTextSliceTree} from './text-slice-tree.js';
import {request,plain} from './positional-spec.mjs';
const view=r=>r.document().aliveBlocks().map(b=>({id:b.id,text:r.document().blockText(b.id),
  characters:r.document().blockCharacters(b.id).map(c=>({text:c.text,bold:!!c.bold}))}));
const observable=v=>v.map(b=>b.characters);
const structure=r=>{const d=r.document();return d.aliveBlocks().map(b=>({id:b.id,tree:debugTextSliceTree(b.title,d.instances)}));};
for(const mergeWhich of ['left','right']) {
  const seed=new Replica('seed','seed',[]),{newBlockId:block}=seed.createBlock();seed.insertText(block,0,'ab');
  const a=new Replica('A','A',seed.transactions()),b=new Replica('B','B',seed.transactions());
  const left=a.splitBlock(block,0),right=b.splitBlock(block,1);
  a.receive(right.transaction);a.receive(left.transaction);
  const merged=mergeWhich==='left'?a.mergeBlock(left.newBlockId):a.mergeBlock(right.newBlockId);
  const before=view(a),target=mergeWhich==='left'?right.newBlockId:block;
  const bi=before.findIndex(x=>x.id===target),n=before[bi].characters.length;
  const expected=request(observable(before),{kind:'bold',block:bi,start:0,end:n});
  const bold=a.toggleBold(target,0,n),actual=view(a);
  if(mergeWhich==='left') {
    assert.deepEqual(before.map(x=>x.text),['','ba']);
    assert.deepEqual(actual.map(x=>x.characters.map(c=>c.bold)),[[],[false,false]]);
    assert.notDeepEqual(observable(actual),expected);
  } else {
    // With split0, merging right's b into empty original yields b|a.
    assert.deepEqual(before.map(x=>x.text),['b','a']);
    assert.deepEqual(actual.map(x=>x.characters.map(c=>c.bold)),[[true],[false]]);
    assert.deepEqual(observable(actual),expected);
  }
  console.log(JSON.stringify({name:mergeWhich==='left'?'reversed-bold-selected-effect-failure':'bold-control',initial:seed.transactions(),
    transactions:[left.transaction,right.transaction,merged.transaction,bold],before,expected,actual,
    specAgreement:JSON.stringify(observable(actual))===JSON.stringify(expected)}));
}
// Noncontiguous selected characters in one text instance must not bold an
// unselected character in another block. a and c retain their original order.
{
  const seed=new Replica('seed','seed',[]),{newBlockId:block}=seed.createBlock();seed.insertText(block,0,'abc');
  const a=new Replica('A','A',seed.transactions()),b=new Replica('B','B',seed.transactions());
  const left=a.splitBlock(block,1),right=b.splitBlock(block,2);a.receive(right.transaction);
  const merged=a.mergeBlock(right.newBlockId),before=view(a),expected=request(observable(before),{kind:'bold',block:0,start:0,end:2});
  const bold=a.toggleBold(block,0,2),actual=view(a);
  assert.deepEqual(before.map(x=>x.text),['ac','b']);
  assert.deepEqual(actual.map(x=>x.characters.map(c=>c.bold)),[[true,true],[true]]);
  assert.notDeepEqual(observable(actual),expected);
  console.log(JSON.stringify({name:'bold-outside-selected-block-failure',initial:seed.transactions(),transactions:[left.transaction,right.transaction,merged.transaction,bold],
    before,expected,actual,specAgreement:false}));
}
// Minimized local split failure using freshly prepared requests, with ordinary
// visible split as an independent contract. Two duplicate-intent merges have
// distinct transaction IDs; repeated delivery is not the source of this bug.
{
  const seed=new Replica('seed','seed',[]),{newBlockId:block}=seed.createBlock();seed.insertText(block,0,'a');
  const setup=new Replica('S','S',seed.transactions()),first=setup.splitBlock(block,0);setup.insertText(block,0,'X');
  const a=new Replica('A','A',setup.transactions()),b=new Replica('B','B',setup.transactions());
  const ma=a.mergeBlock(first.newBlockId),mb=b.mergeBlock(first.newBlockId);a.receive(mb.transaction);
  const c=new Replica('C','C',a.transactions()),d=new Replica('D','D',a.transactions());
  const sc=c.splitBlock(block,0),sd=d.splitBlock(block,1);c.receive(sd.transaction);
  const merge=c.mergeBlock(sc.newBlockId),before=view(c),beforeStructure=structure(c),bi=before.findIndex(x=>x.id===sd.newBlockId);
  const expected=request(observable(before),{kind:'split',block:bi,index:0}),split=c.splitBlock(sd.newBlockId,0),actual=view(c);
  assert.deepEqual(before.map(x=>x.text),['','aX']);assert.deepEqual(actual.map(x=>x.text),['','X','a']);
  assert.notDeepEqual(observable(actual),expected);
  console.log(JSON.stringify({name:'split-zero-leaves-suffix-sibling-failure',initial:seed.transactions(),transactions:c.transactions(),before,beforeStructure,afterStructure:structure(c),request:{kind:'split',block:bi,index:0},expected,actual,specAgreement:false}));
}
// Split and block-merge requests never delete text, so every character of the
// seed must stay visible. These two failures hide text in removed blocks.
{
  const seedBlocks=texts=>{const r=new Replica('seed','seed',[]);let previous;
    for(const t of texts){previous=r.createBlock(previous).newBlockId;r.insertText(previous,0,t);}return r.transactions();};
  const idAt=(r,i)=>r.document().aliveBlocks()[i].id;
  const shown=r=>view(r).map(b=>b.text);
  const visible=r=>shown(r).join('').split('').sort().join('');
  const stored=r=>{const d=r.document();return [...d.blocks.values()].map(b=>d.blockText(b.id)).join('').split('').sort().join('');};
  // Each request may emit several transactions; deliver all of them, in order.
  const issue=(r,f)=>{const prior=new Set(r.transactions().map(t=>JSON.stringify(t.id)));f();
    return r.transactions().filter(t=>!prior.has(JSON.stringify(t.id)));};
  const deliver=(r,txs)=>{for(const t of txs)r.receive(t);};
  const merge=(r,i)=>issue(r,()=>r.mergeBlock(idAt(r,i)));
  const split=(r,i,k)=>issue(r,()=>r.splitBlock(idAt(r,i),k));
  // Five requests from a | b | c leave no visible block. A's last merge removes
  // a block that is empty in A's view, but B has meanwhile merged the text into
  // the block that this merge appends to and then removes.
  const lose=({firstMerge=true,lastEarly=false}={})=>{
    const initial=seedBlocks(['a','b','c']),a=new Replica('A','A',initial),b=new Replica('B','B',initial);
    const a0=merge(a,2),a1=split(a,1,0),a2=merge(a,2);
    const b0=firstMerge?merge(b,1):[];deliver(b,a0);deliver(b,a1);
    if(lastEarly)deliver(b,a2);
    const before=view(b),b1=lastEarly?[]:merge(b,1),afterLocal=view(b);
    if(!lastEarly)deliver(b,a2);
    deliver(a,b0);deliver(a,b1);
    assert.deepEqual(shown(a),shown(b));
    return {initial,transactions:[...a0,...a1,...a2,...b0,...b1],before,afterLocal,actual:view(b),visible:visible(b),stored:stored(b)};
  };
  const lost=lose(),controls4={noFirstMerge:lose({firstMerge:false}),lastMergeDeliveredEarly:lose({lastEarly:true})};
  assert.deepEqual(lost.before.map(x=>x.text),['','abc']);assert.deepEqual(lost.afterLocal.map(x=>x.text),['abc']);
  assert.deepEqual(lost.actual,[]);assert.equal(lost.visible,'');assert.notEqual(lost.visible,'abc');
  assert.equal(lost.stored,'abc');
  for(const c of Object.values(controls4)){assert.equal(c.visible,'abc');assert.notDeepEqual(c.actual,[]);}
  console.log(JSON.stringify({name:'merge-into-removed-block-loses-document-failure',initial:lost.initial,transactions:lost.transactions,
    before:lost.before,afterLocal:lost.afterLocal,expected:'abc',actual:lost.actual,storedCharacters:lost.stored,
    controls:Object.fromEntries(Object.entries(controls4).map(([k,c])=>[k,c.actual])),specAgreement:false}));
  // One character is lost when a delayed merge arrives. The move it carries
  // would create a cycle and is skipped, but its block removal still runs.
  const hide=({held=true,localMerge=true,early=false}={})=>{
    const initial=seedBlocks(['x']),a=new Replica('A','A',initial),b=new Replica('B','B',initial);
    const a0=split(a,0,0),b0=split(b,0,1),b1=merge(b,1);
    deliver(a,b0);if(early)deliver(a,b1);
    const before=view(a),a1=localMerge?merge(a,early?1:2):[];
    if(held&&!early)deliver(a,b1);
    deliver(b,a0);deliver(b,a1);
    if(held)assert.deepEqual(shown(a),shown(b));
    return {initial,transactions:[...a0,...b0,...b1,...a1],before,actual:view(a),visible:visible(a),stored:stored(a)};
  };
  const hidden=hide(),controls={notDelivered:hide({held:false}),noLocalMerge:hide({localMerge:false}),deliveredEarly:hide({early:true})};
  assert.equal(hidden.visible,'');assert.notEqual(hidden.visible,'x');assert.equal(hidden.stored,'x');
  for(const c of Object.values(controls)){assert.equal(c.visible,'x');assert.notEqual(c.visible,'');}
  console.log(JSON.stringify({name:'cyclic-merge-removal-hides-character-failure',initial:hidden.initial,transactions:hidden.transactions,
    before:hidden.before,expected:'x',actual:hidden.actual,storedCharacters:hidden.stored,
    controls:Object.fromEntries(Object.entries(controls).map(([k,c])=>[k,c.actual])),specAgreement:false}));
}
