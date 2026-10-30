// Targeted convergence search for issue 829. No sequential-spec oracle is used.
import assert from 'node:assert/strict';
import {writeFileSync,readFileSync} from 'node:fs';
const version=process.argv[2]||'14', count=Number(process.argv[3]||1000), start=Number(process.argv[4]||1);
const root=version==='14'?'../repro/v14/node_modules/@y/y/':'../repro/node_modules/yjs/';
const pkg=JSON.parse(readFileSync(new URL(root+'package.json',import.meta.url)));
const Y=await import(new URL(root+(version==='14'?'src/index.js':'dist/yjs.mjs'),import.meta.url));
const text=d=>version==='14'?d.get('t'):d.getText('t');
const stable=o=>Array.isArray(o)?o.map(stable):o&&typeof o==='object'?Object.fromEntries(Object.keys(o).sort().map(k=>[k,stable(o[k])])):o;
const view=d=>{const delta=text(d).toDelta(); const runs=version==='14'?delta.children.map(c=>({insert:c.insert,attributes:c.format??{}})):delta.map(c=>({insert:c.insert,attributes:c.attributes??{}})); return {text:text(d).toString(),delta:stable(runs)};};
const equal=ds=>ds.every(d=>JSON.stringify(view(d))===JSON.stringify(view(ds[0])));
const pending=d=>({structs:d.store.pendingStructs!=null,ds:d.store.pendingDs!=null});
function rng(seed){let s=seed>>>0;return ()=>{s^=s<<13;s^=s>>>17;s^=s<<5;return (s>>>0)/4294967296;};}
function shuffle(a,r){a=a.slice();for(let i=a.length-1;i>0;i--){const j=Math.floor(r()*(i+1));[a[i],a[j]]=[a[j],a[i]];}return a;}
function trial(family,gc,seed,localCount=null){
 const r=rng(seed), docs=[], all=[], seen=new Set(), by=[], trace=[];
 const add=d=>{const us=[];docs.push(d);by.push(us);d.on('update',u=>{us.push(u);const k=Buffer.from(u).toString('base64');if(!seen.has(k)){seen.add(k);all.push(u);}});return d;};
 for(let i=0;i<3;i++){const d=add(new Y.Doc({gc}));d.clientID=100+i; text(d);}
 const [a,b,c]=docs, apply=(d,u)=>Y.applyUpdate(d,u);
 let withheld;
 if(family==='plain-gap'){
  text(a).insert(0,'y');withheld=by[0][0];text(b).insert(0,'b');apply(a,by[1][0]);
  text(a).insert(text(a).toString().indexOf('b')+1,'h');apply(b,by[0].at(-1));
  apply(c,by[1][0]);apply(c,by[0].at(-1));
 }else if(family==='delete-set-gap'){
  text(a).insert(0,'a',{bold:true});const base=by[0].at(-1);text(a).insert(1,'b');withheld=by[0].at(-1);text(a).format(0,2,{bold:null});
  const late=by[0].at(-1);apply(b,base);apply(b,late);apply(c,base);
 }else{
  text(a).insert(0,'ab',{bold:true});const base=by[0].at(-1);apply(b,base);apply(c,base);text(b).format(0,2,{bold:null});withheld=by[1].at(-1);text(b).insert(1,'q');apply(a,by[1].at(-1));apply(c,by[1].at(-1));
 }
 const gapViews=docs.map(view), gapPending=docs.map(pending);
 // Local mutations made while the predecessor is withheld, including formatting.
 const n=localCount??(1+Math.floor(r()*8));
 for(let k=0;k<n;k++){
  const idx=family==='insert-before-unformat'?(r()<.5?0:2):1+Math.floor(r()*2), d=docs[idx], t=text(d), len=t.length, choice=Math.floor(r()*4), pos=Math.floor(r()*(len+1));
  if(choice<2||len===0){const value=String.fromCharCode(65+k%26), attrs=r()<.5?{}:{bold:r()<.5,italic:r()<.5};t.insert(pos,value,attrs);trace.push({op:'insert',replica:idx,pos,value,attrs});}
  else{const from=Math.min(pos,len-1), length=1+Math.floor(r()*(len-from));if(choice===2){t.delete(from,length);trace.push({op:'delete',replica:idx,from,length});}else{const attrs=r()<.5?{bold:null}:{bold:true,italic:r()<.5?true:null};t.format(from,length,attrs);trace.push({op:'format',replica:idx,from,length,attrs});}}
  // Optionally relay the just-produced edit but never the withheld predecessor.
  if(r()<.5 && by[idx].length){const dest=(idx+1)%3,u=by[idx].at(-1);if(Buffer.compare(Buffer.from(u),Buffer.from(withheld))!==0){apply(docs[dest],u);trace.push({op:'relay-last',from:idx,to:dest});}}
 }
 // Every replica gets the identical complete set, using varied order, duplicates,
 // individual delivery or merged batches. Newly generated cleanup updates join it.
 let deliveryQuiescent=false;
 for(let round=0;round<12;round++){
  const before=all.length, batch=all.slice();
  for(const d of docs){const ordered=shuffle(batch,r);for(let i=0;i<ordered.length;){const size=1+Math.floor(r()*3), chunk=ordered.slice(i,i+size);i+=size;const u=chunk.length===1?chunk[0]:Y.mergeUpdates(chunk);apply(d,u);if(r()<.3)apply(d,u);}}
  if(all.length===before){deliveryQuiescent=true;break;}
 }
 const delivered=docs.map(view), mismatchAfterDelivery=!equal(docs);
 // Explicit anti-entropy: exchange state-vector differences in shuffled order.
 let quiescent=false;
 for(let round=0;round<12;round++){
  const before=all.length, old=JSON.stringify(docs.map(view));
  for(const i of shuffle([0,1,2],r))for(const j of shuffle([0,1,2],r))if(i!==j)apply(docs[j],Y.encodeStateAsUpdate(docs[i],Y.encodeStateVector(docs[j])));
  if(all.length===before&&JSON.stringify(docs.map(view))===old){quiescent=true;break;}
 }
 const final=docs.map(view), pend=docs.map(pending), result={family,gc,seed,localCount:n,trace,gapViews,gapPending,deliveryQuiescent,quiescent,mismatchAfterDelivery,delivered,final,pending:pend,updates:all.length,divergence:!equal(docs),unresolved:pend.some(p=>p.structs||p.ds)};
 for(const d of docs)d.destroy();return result;
}
// Oracle controls: differing text must fail, complete shared updates must pass.
{const a=new Y.Doc(),b=new Y.Doc();text(a).insert(0,'x');assert.equal(equal([a,b]),false);Y.applyUpdate(b,Y.encodeStateAsUpdate(a));assert.equal(equal([a,b]),true);text(a).format(0,1,{bold:true});assert.equal(equal([a,b]),false);Y.applyUpdate(b,Y.encodeStateAsUpdate(a));assert.equal(equal([a,b]),true);a.destroy();b.destroy();}
const summary={package:pkg.name,version:pkg.version,node:process.version,start,count,started:new Date().toISOString(),trials:0,divergences:0,unresolved:0,nonquiescent:0,deliveryMismatches:0,groups:[],findings:[]};
console.log(JSON.stringify({event:'START',...summary}));
for(const family of ['plain-gap','delete-set-gap','insert-before-unformat'])for(const gc of [false,true]){
 const group={family,gc,trials:0,divergences:0,unresolved:0,nonquiescent:0,deliveryMismatches:0};
 // Zero-local-edit baseline must converge for each original reported case.
 const baseline=trial(family,gc,829,0);assert.equal(baseline.divergence,false);assert.equal(baseline.unresolved,false);
 if(family==='plain-gap'){assert.equal(baseline.gapViews[1].text,version==='14'?'bh':'b');assert.equal(baseline.gapPending[1].structs,version!=='14');}
 if(family==='delete-set-gap'){assert.equal(baseline.gapViews[1].text,'a');assert.deepEqual(baseline.gapViews[1].delta,[{attributes:{},insert:'a'}]);}
 if(family==='insert-before-unformat'){assert.equal(baseline.gapViews[0].text,'aqb');assert.ok(baseline.gapViews[0].delta.some(x=>x.attributes.bold===true));}
 for(let k=0;k<count;k++){
  const result=trial(family,gc,Math.imul(start+k,0x9e3779b1)>>>0);group.trials++;summary.trials++;
  for(const [name,flag] of [['divergences',result.divergence],['unresolved',result.unresolved],['nonquiescent',!result.quiescent||!result.deliveryQuiescent],['deliveryMismatches',result.mismatchAfterDelivery]])if(flag){group[name]++;summary[name]++;}
  if(result.divergence||result.unresolved||!result.quiescent||result.mismatchAfterDelivery){if(summary.findings.length<20)summary.findings.push(result);console.log(JSON.stringify({event:'FINDING',...result}));}
  if(k%1000===999)console.log(JSON.stringify({event:'PROGRESS',version:pkg.version,...group}));
 }
 summary.groups.push(group);
}
summary.finished=new Date().toISOString();writeFileSync(new URL(`results-v${version}-${start}-${count}.json`,import.meta.url),JSON.stringify(summary,null,2)+'\n');console.log(JSON.stringify({event:'DONE',...summary}));
