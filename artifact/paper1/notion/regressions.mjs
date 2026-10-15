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
