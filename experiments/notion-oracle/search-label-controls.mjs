// Hand-derived source codec and honest split/move controls.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {iterateTextSliceTree} from './text-slice-tree.js';
import {splitSearchLabel, printableSearchLabel} from './search-labels.js';
const labelOf=path=>[...path].reduce((label,bit)=>splitSearchLabel(label)[bit==='R'?1:0],'');
assert.equal(labelOf('LLLLL'),'=');
assert.equal(labelOf('LLLLLL'),'=L');
assert.notEqual(labelOf('LLLLLL'),'=');
assert.equal(labelOf('LLLLLLLLLLLL'),'==D');
assert.equal(printableSearchLabel('LL'),'LL');
assert.equal(printableSearchLabel('D'),'LL');
assert.notEqual('LL','D'); // Valid-character strings are not all canonical encodings.
const paths=[''];
for(let depth=1;depth<=12;depth++) {
 const layer=Array.from({length:2**depth},(_,n)=>n.toString(2).padStart(depth,'0').replaceAll('0','L').replaceAll('1','R'));
 const labels=layer.map(labelOf);
 assert.equal(new Set(labels).size,layer.length);
 for(let i=0;i<layer.length;i++)assert.equal(printableSearchLabel(labels[i]),layer[i]);
 paths.push(...layer);
}
assert.equal(new Set(paths.map(labelOf)).size,paths.length);
const r=new Replica('labels','labels',[]),block=r.createBlock().newBlockId;
r.insertText(block,0,'a');
const history=[];
for(let depth=1;depth<=12;depth++) {
 const split=r.splitBlock(block,0),doc=r.document(),entries=[];
 for(const b of doc.blocks.values())for(const node of iterateTextSliceTree(b.title)) {
  const s=node.textSlice;
  entries.push({block:b.id,instance:s.textInstanceId,label:s.searchLabel,path:printableSearchLabel(s.searchLabel)});
 }
 assert.equal(new Set(entries.map(x=>`${x.instance}|${x.label}`)).size,entries.length);
 const same=entries.filter(x=>x.instance===block);
 assert.equal(same.length,depth+1);
 const expected=['L'.repeat(depth),...Array.from({length:depth},(_,i)=>'L'.repeat(i)+'R')];
 assert.deepEqual(same.map(x=>x.path).sort(),expected.sort());
 for(const a of same)for(const b of same)if(a!==b)assert(!b.path.startsWith(a.path));
 assert.equal(doc.blockText(block),'');
 assert.equal(doc.aliveBlocks().map(b=>doc.blockText(b.id)).join(''),'a');
 assert.notEqual(same.length,1);
 history.push({depth,newBlock:split.newBlockId,entries});
}
console.log(JSON.stringify({name:'canonical-search-label-depth12-honest-split-move',
 codecChecks:paths.length,depth5:'=',depth6:'=L',depth12:'==D',
 noncanonicalAlias:{labels:['LL','D'],printedPath:'LL'},history,
 note:'Every reconstruction invokes actual duplicate-label assertion. Same-instance active paths form a prefix-free frontier; empty title roots belong to fresh instances.'}));
