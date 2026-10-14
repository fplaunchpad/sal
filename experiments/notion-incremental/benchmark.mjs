import assert from 'node:assert/strict';
import {performance} from 'node:perf_hooks';
import {Replica} from './replica.js';
import {CrdtDocument,createInitialTransactions} from './document.js';
import {compareOpIds,idKey} from './ids.js';
import {Structured} from './structured.mjs';
const args=process.argv.slice(2),arg=(key,d)=>args.includes(key)?args[args.indexOf(key)+1]:d;
const cases=+arg('--cases','100'),sizes=arg('--sizes','32,128,512').split(',').map(Number),repeats=+arg('--repeats','5');
const clone=x=>JSON.parse(JSON.stringify(x));
const view=doc=>doc.aliveBlocks().map(b=>({id:b.id,text:doc.blockText(b.id)}));
const oracle=txs=>view(new CrdtDocument(txs));
class FullReplay {
 constructor(txs=[]){this.transactions=new Map(txs.map(tx=>[idKey(tx.id),clone(tx)]));this.replays=1;this.replayedTransactions=txs.length;this.doc=new CrdtDocument(txs);}
 receive(tx){const key=idKey(tx.id),old=this.transactions.get(key);if(old){assert.deepEqual(tx,old);return false;}
  this.transactions.set(key,clone(tx));this.replay();return true;}
 replay(){this.replays++;this.replayedTransactions+=this.transactions.size;this.doc=new CrdtDocument([...this.transactions.values()]);}
 merge(other){let changed=false;for(const tx of other.transactions.values()){const key=idKey(tx.id),old=this.transactions.get(key);if(old)assert.deepEqual(old,tx);else{this.transactions.set(key,clone(tx));changed=true;}}if(changed)this.replay();return this;}
 query(){return view(this.doc);}
 memoryProxy(){return {archiveTransactions:this.transactions.size,physicalRows:[...this.doc.instances.values()].reduce((n,i)=>n+i.rga.items.size,0),deletedIds:[...this.doc.instances.values()].reduce((n,i)=>n+i.rga.deletedIds.size,0),blocks:this.doc.blocks.size,instances:this.doc.instances.size,mappingEntries:this.doc.textSliceBlockMappings.size,retainedSortedTransactionReferences:this.doc.transactions.length};}
}
function random(seed){let x=seed>>>0;return ()=>{x=(Math.imul(1664525,x)+1013904223)>>>0;return x/2**32;};}
const issued=result=>result?.transaction??result;
function workload(seed,n,mode){
 const rng=random(seed),initial=createInitialTransactions('abcd'),replicas=['B','C','Z'].map(s=>new Replica(s,s,initial));
 const deliveries=[],metadata={inserts:0,splits:0,deletes:0,creates:0,lateArrivals:0};
 for(let step=0;step<n;step++){
  const r=replicas[Math.floor(rng()*replicas.length)];
  if(step%7===0){const peer=replicas[Math.floor(rng()*replicas.length)];for(const tx of peer.transactions())r.receive(tx);}
  const doc=r.document(),blocks=doc.aliveBlocks(),b=blocks[Math.floor(rng()*blocks.length)],len=[...doc.blockText(b.id)].length;
  let result;const choice=rng();
  if(mode==='mixed'&&choice<.22){result=r.splitBlock(b.id,Math.floor(rng()*(len+1)));metadata.splits++;}
  else if(mode==='mixed'&&choice<.42&&len>0){const start=Math.floor(rng()*len);result=r.deleteText(b.id,start,Math.min(len,start+1+Math.floor(rng()*3)));metadata.deletes++;}
  else if(mode==='mixed'&&choice<.48){result=r.createBlock(b.id);metadata.creates++;}
  else {result=r.insertText(b.id,Math.floor(rng()*(len+1)),step%13===0?'😀x':String.fromCharCode(97+step%26));metadata.inserts++;}
  const tx=issued(result);assert(tx);deliveries.push(tx);
 }
 // Reverse complete local-version batches: preserve each sender's causal prefix
 // while enabling lower-clock concurrent transactions to arrive after high ones.
 const batches=replicas.map(r=>r.transactions());let max;const schedule=[];const seen=new Set(initial.map(t=>idKey(t.id)));
 for(const batch of batches.reverse())for(const tx of batch){if(seen.has(idKey(tx.id)))continue;
  if(max&&compareOpIds(tx.id,max)<0)metadata.lateArrivals++;if(!max||compareOpIds(max,tx.id)<0)max=tx.id;
  schedule.push(tx);seen.add(idKey(tx.id));}
 const common=[...initial,...schedule],forks=['merge-B','merge-Z'].map(s=>new Replica(s,s,common));
 const target=forks[0].document().aliveBlocks()[0].id;
 for(const [i,r] of forks.entries())r.insertText(target,0,i===0?'L':'R');
 const mergeBatches=forks.map(r=>r.transactions());
 return {initial,schedule,batches,mergeBatches,metadata,seed,mode};
}
let equalityChecks=0;
function check(w){
 for(let i=0;i<w.batches.length;i++)for(let j=i+1;j<w.batches.length;j++){
  const left=new Structured(w.batches[i]),right=new Structured(w.batches[j]);
  const union=[...new Map([...w.batches[i],...w.batches[j]].map(tx=>[idKey(tx.id),tx])).values()];
  const before=left.counts.transactionsIntegrated;left.merge(right);
  assert.equal(left.counts.transactionsIntegrated,before,'direct join must not interpret transaction payloads');
  assert.deepEqual(left.query(),oracle(union));assert.deepEqual(left.query('fold'),oracle(union));equalityChecks+=2;
  const reverse=new Structured(w.batches[j]).merge(new Structured(w.batches[i]));assert.deepEqual(reverse.query(),left.query());equalityChecks++;
 }
 const state=new Structured(w.initial),past=[...w.initial];assert.deepEqual(state.query(),oracle(past));assert.deepEqual(state.query('fold'),oracle(past));equalityChecks+=2;
 for(const tx of w.schedule){state.receive(tx);past.push(tx);assert.deepEqual(state.query(),oracle(past),JSON.stringify({seed:w.seed,mode:w.mode,tx,past}));equalityChecks++;assert.deepEqual(state.query('fold'),oracle(past));equalityChecks++;assert.equal(state.receive(tx),false);}
 for(const batch of w.batches){const branch=new Structured(batch);const before=state.transactions.size;state.merge(branch);assert.equal(state.transactions.size,before);assert.deepEqual(state.query(),oracle(past));equalityChecks++;}
 return state;
}
function controls(){
 const pre=new Replica('@','pre-factory',[]),preTx=issued(pre.createBlock());
 const preOnly=[{id:'@-block-1',text:''}],preWithSeed=[{id:'block-A',text:'ab'},...preOnly];
 const initial=createInitialTransactions('ab');
 assert.deepEqual(new Structured([preTx]).query('fold'),preOnly);assert.deepEqual(oracle([preTx]),preOnly);
 assert.deepEqual(new Structured([preTx,...initial]).query('fold'),preWithSeed);assert.deepEqual(oracle([preTx,...initial]),preWithSeed);
 assert.notDeepEqual(new Structured([preTx,...initial]).query('fold'),[...preOnly,{id:'block-A',text:'ab'}]);
 const b=new Replica('B','B',initial),z=new Replica('Z','Z',initial);
 const bt=issued(b.splitBlock('block-A',1)),zt=issued(z.splitBlock('block-A',1));
 const expected=[{id:'block-A',text:'a'},{id:zt.operations[0].args.blockId,text:''},{id:bt.operations[0].args.blockId,text:'b'}];
 assert.deepEqual(oracle([...initial,zt,bt]),expected);const direct=new Structured([...initial,zt,bt]);assert.deepEqual(direct.query(),expected);
 // Known-broken append-only structural interpreter: applying create splice in
 // arrival order rather than the canonical source order reverses concurrent blocks.
 const appendOrder=['block-A'];for(const tx of [zt,bt]){const a=tx.operations[0].args;appendOrder.splice(appendOrder.indexOf(a.afterBlockId)+1,0,a.blockId);}
 assert.notDeepEqual(appendOrder,expected.map(b=>b.id));
 const p=new Replica('B','B',initial),q=new Replica('Z','Z',initial);
 const pi=p.insertText('block-A',1,'X'),qi=q.insertText('block-A',1,'Y');
 assert.deepEqual(new Structured([...initial,qi,pi]).query(),[{id:'block-A',text:'aYXb'}]);
 assert.notDeepEqual(new Structured([...initial,qi,pi]).query(),[{id:'block-A',text:'aXYb'}]);
 const d=p.deleteText('block-A',1,2),erased=new Structured([...initial,pi,d]);assert.deepEqual(erased.query(),[{id:'block-A',text:'ab'}]);assert.notDeepEqual(erased.query(),[{id:'block-A',text:'aXb'}]);
 return {preBootstrapLowerKeyCreateLiteral:true,bootstrapAbsentVersionLiteral:true,lateConcurrentInsertLiteral:true,concurrentSplitLiteral:true,noOpDeleteRejected:true,appendOnlyArrivalOrderRejected:true,appendOrder,correctOrder:expected.map(b=>b.id),splitTransactions:[zt,bt]};
}
if(args.includes('--heap-engine')) {
 const name=arg('--heap-engine',''),size=+arg('--heap-size','512'),mode=arg('--heap-mode','mixed');
 if(!global.gc)throw Error('heap comparison requires --expose-gc');
 const Class=name==='full-replay'?FullReplay:name==='indexed-structure'?Structured:undefined;
 if(!Class)throw Error('unknown heap engine');
 // Each invocation is its own process. Workload generation is outside the
 // measured interval and stays retained equally in both engines.
 const w=workload(314159,size,mode),txs=[...w.initial,...w.schedule];
 let warmup=new Class(w.initial);warmup.query();warmup=null;
 for(let i=0;i<3;i++)global.gc();
 const before=process.memoryUsage();
 const state=new Class(txs);
 for(let i=0;i<3;i++)global.gc();
 const after=process.memoryUsage();
 // Retain state and prepared workload across GC, then verify after measurement.
 const actual=state.query(),expected=oracle(txs);assert.deepEqual(actual,expected);
 console.log(JSON.stringify({kind:'retained-heap',engine:name,size,mode,seed:w.seed,
  nodeVersion:process.version,platform:process.platform,architecture:process.arch,
  beforeHeapUsed:before.heapUsed,afterHeapUsed:after.heapUsed,retainedHeapDelta:after.heapUsed-before.heapUsed,
  beforeRss:before.rss,afterRss:after.rss,transactions:txs.length,blocks:actual.length,
  memoryProxy:state.memoryProxy(),scope:'Three explicit GC passes before/after construction; separately spawned process per engine; prepared workload retained outside measured delta; includes engine archive and retained document/index; verification/query done after measurement; GC and V8 heap noise remain.'}));
 process.exit(0);
}
const negativeControls=controls();let metadata={inserts:0,splits:0,deletes:0,creates:0,lateArrivals:0};
for(let seed=1;seed<=cases;seed++)for(const mode of ['insertion','mixed']){const w=workload(seed,24,mode);check(w);for(const key of Object.keys(metadata))metadata[key]+=w.metadata[key];}
console.log(JSON.stringify({kind:'correctness',seedRange:[1,cases],cases:cases*2,equalityChecks,metadata,negativeControls,scope:'Honest pinned Replica issuance and whole-version receipt; independently maintained executable structure against pinned reconstruction; no extraction claim.'}));
function measure(fn){const start=performance.now();const value=fn();return {ms:performance.now()-start,value};}
if(args.includes('--display-fold-only')){
 for(const size of sizes)for(const mode of ['insertion','mixed']){
  const w=workload(314159,size,mode);check(w);const expected=oracle([...w.initial,...w.schedule]);
  for(let repeat=0;repeat<repeats;repeat++){
   const state=new Structured([...w.initial,...w.schedule]);
   const tree=measure(()=>state.query('tree')),fold=measure(()=>state.query('fold'));
   assert.deepEqual(tree.value,expected);assert.deepEqual(fold.value,expected);
   console.log(JSON.stringify({kind:'display-benchmark',size,mode,seed:w.seed,repeat,treeQueryMs:tree.ms,foldQueryMs:fold.ms,createdBlocks:state.blocks.size,retainedRows:state.memoryProxy().physicalRows,scope:'Same maintained rows/cuts/deletes; creator fold versus descending create-child traversal; full answer rendering timed separately from updates/merges.'}));
  }
 }
}else for(const size of sizes)for(const mode of ['insertion','mixed']){
 const w=workload(314159,size,mode);check(w);
 for(let repeat=0;repeat<repeats;repeat++)for(const [name,Class] of [['full-replay',FullReplay],['indexed-structure',Structured]]){
  const state=new Class(w.initial);const update=measure(()=>{for(const tx of w.schedule)state.receive(tx);});
  const query=measure(()=>state.query());assert.deepEqual(query.value,oracle([...w.initial,...w.schedule]));
  const left=new Class(w.mergeBatches[0]),right=new Class(w.mergeBatches[1]);
  const merged=measure(()=>left.merge(right));const mergedQuery=measure(()=>left.query());
  assert.deepEqual(mergedQuery.value,oracle([...new Map([...w.mergeBatches[0],...w.mergeBatches[1]].map(t=>[idKey(t.id),t])).values()]));
  const archiveBytes=Buffer.byteLength(JSON.stringify([...state.transactions.values()]));
  console.log(JSON.stringify({kind:'benchmark',engine:name,size,mode,seed:w.seed,repeat,metadata:w.metadata,
   updateMs:update.ms,queryMs:query.ms,mergeMs:merged.ms,mergedQueryMs:mergedQuery.ms,
   updateTransactions:w.schedule.length,mergeInputTransactions:right.transactions.size,mergeAddedTransactions:left.transactions.size-w.mergeBatches[0].length,
   memory:{kind:'explicit-proxy-not-heap-measurement',archiveJsonBytes:archiveBytes,...state.memoryProxy()},
   work:name==='full-replay'?{reconstructions:state.replays,replayedTransactions:state.replayedTransactions}:state.counts,
   mergeStateWork:name==='full-replay'?{reconstructions:left.replays,replayedTransactions:left.replayedTransactions}:left.counts}));
 }
}
