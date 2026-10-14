// Pinned client/oracle around a separate compiled Lean core. Codec boundary is
// tested/trusted until proved. Native time, IPC time and preparation are separate.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {CrdtDocument,createInitialTransactions,transactionClockMax} from './document.js';
import {compareOpIds,idKey} from './ids.js';
import {encodeTransaction,typedClockMax,encodeBlockName,decodeBlockKey,sessionUnits,textAtoms,atomsText,nativeView,NativeClient} from './native-wire.mjs';
const args=process.argv.slice(2),arg=(key,d)=>args.includes(key)?args[args.indexOf(key)+1]:d;
const cases=+arg('--cases','10'),sizes=arg('--sizes','16').split(',').map(Number),repeats=+arg('--repeats','1');
const txOf=value=>value?.transaction??value;
const view=transactions=>{const doc=new CrdtDocument(transactions);return doc.aliveBlocks().map(b=>({id:b.id,text:doc.blockText(b.id)}));};
const I=(counter,session)=>({counter,session}),initial='initial',issued=id=>({issued:id}),item=id=>({item:id});
function fixtures(){
 const seed=createInitialTransactions('ab'),empty=createInitialTransactions('');
 assert.deepEqual(encodeTransaction(seed[0]),{id:I(1,[65]),payload:{kind:'bootstrap',atoms:[97,98]}});
 assert.deepEqual(encodeTransaction(empty[0]),{id:I(1,[65]),payload:{kind:'bootstrap',atoms:[]}});
 const b=new Replica('B','fixture',seed),split=txOf(b.splitBlock('block-A',1)),block=split.operations[0].args.blockId;
 assert.deepEqual(encodeTransaction(split),{id:I(3,[66]),payload:{kind:'split',block:initial,instance:initial,origin:item(I(1,[65]))}});
 const insert=b.insertText(block,0,'😀x');assert.deepEqual(encodeTransaction(insert),{id:I(4,[66]),payload:{kind:'insert',block:issued(I(3,[66])),instance:initial,origin:item(I(3,[66])),atoms:[128512,120]}});
 const erase=b.deleteText(block,0,1);assert.deepEqual(encodeTransaction(erase),{id:I(6,[66]),payload:{kind:'erase',block:issued(I(3,[66])),instance:initial,targets:[I(4,[66])]}});
 assert.notEqual(transactionClockMax(insert),insert.id.counter+insert.operations[0].args.content.length-1,'UTF-16 string length must not determine allocation width');
 assert.deepEqual(textAtoms('😀a\uD800'),[128512,97,55296]);assert.notDeepEqual(textAtoms('😀a\uD800'),[55357,56832,97,55296]);assert.equal(atomsText([128512,97,55296]),'😀a\uD800');
 const weirdSession='A-block-:|\n😀',weirdName=`${weirdSession}-block-12`;
 assert.deepEqual(sessionUnits('😀'),[55357,56832]);assert.notDeepEqual(sessionUnits('😀'),[128512]);assert.equal(decodeBlockKey(encodeBlockName(weirdName)),weirdName);
 assert.throws(()=>encodeBlockName('B-block-03'),/outside|noncanonical/);
 assert.throws(()=>encodeTransaction({...insert,id:{sessionId:'B',counter:9007199254740992}}),/safe integer/);
 const broken=JSON.parse(JSON.stringify(split));broken.operations[2].args.targetBlockId='C-block-3';assert.throws(()=>encodeTransaction(broken),/inconsistent/);
 const emoji=new Replica('😀','emoji',seed),pua=new Replica('\uE000','pua',seed);
 const emojiTx=emoji.insertText('block-A',1,'E'),puaTx=pua.insertText('block-A',1,'P');
 assert.deepEqual(encodeTransaction(emojiTx).id,I(3,[55357,56832]));assert.deepEqual(encodeTransaction(puaTx).id,I(3,[57344]));
 assert.deepEqual(view([...seed,puaTx,emojiTx]),[{id:'block-A',text:'aPEb'}]);assert.notDeepEqual(view([...seed,puaTx,emojiTx]),[{id:'block-A',text:'aEPb'}]);
 const strange=new Replica(weirdSession,'separator/newline',[]),strangeTx=txOf(strange.createBlock());
 const before=new Replica('@','pre-factory',[]),pre=txOf(before.createBlock());
 const groups=[
  {name:'utf16-concurrent-session-order',transactions:[...seed,puaTx,emojiTx],expected:[{id:'block-A',text:'aPEb'}]},
  {name:'separator-newline-session-create',transactions:[strangeTx],expected:[{id:strangeTx.operations[0].args.blockId,text:''}]},
  {name:'empty-bootstrap',transactions:empty,expected:[{id:'block-A',text:''}]},
  {name:'bootstrap-absent-create',transactions:[pre],expected:[{id:'@-block-1',text:''}]},
  {name:'lower-key-pre-bootstrap',transactions:[pre,...seed],expected:[{id:'block-A',text:'ab'},{id:'@-block-1',text:''}]},
  {name:'split-inherited-unicode-erase',transactions:b.transactions(),expected:[{id:'block-A',text:'a'},{id:block,text:'xb'}]},
 ];
 for(const group of groups){for(const tx of group.transactions)assert.equal(typedClockMax(encodeTransaction(tx)),transactionClockMax(tx));assert.deepEqual(view(group.transactions),group.expected);assert.notDeepEqual(group.expected,[]);}
 return {groups,record:{kind:'native-wire-fixtures',groups:groups.map(g=>({name:g.name,transactions:g.transactions.map(encodeTransaction),expected:g.expected})),controls:{utf16SessionUnits:true,utf16ConcurrentSessionOrder:true,unicodeIteratorAtoms:true,unicodeReservationWidth:true,loneSurrogateAtomRoundtrip:true,separatorNewlineSessionNameRoundtrip:true,noncanonicalCounterRejected:true,unsafeCounterRejected:true,malformedAtomicSplitRejected:true},scope:'Literal typed fixture expectations and pinned source request traces; tested/trusted JSON codec, no extraction theorem.'}};
}
function random(seed){let x=seed>>>0;return()=>{x=(Math.imul(x,1664525)+1013904223)>>>0;return x/2**32;};}
function workload(seed,n,mode){
 const rng=random(seed),initial=createInitialTransactions('abcd'),peers=['B','C','Z'].map(s=>new Replica(s,s,initial));const requests=[];
 for(let k=0;k<n;k++){
  const peer=peers[Math.floor(rng()*3)];if(k%7===0)for(const tx of peers[Math.floor(rng()*3)].transactions())peer.receive(tx);
  const doc=peer.document(),blocks=doc.aliveBlocks(),block=blocks[Math.floor(rng()*blocks.length)],length=doc.blockCharacters(block.id).length,choice=rng();let value;
  if(mode==='mixed'&&choice<.22){const index=Math.floor(rng()*(length+1));value=peer.splitBlock(block.id,index);requests.push({kind:'split',block:block.id,index});}
  else if(mode==='mixed'&&choice<.42&&length>0){const start=Math.floor(rng()*length),end=Math.min(length,start+1+Math.floor(rng()*3));value=peer.deleteText(block.id,start,end);requests.push({kind:'erase',block:block.id,start,end});}
  else if(mode==='mixed'&&choice<.48){value=peer.createBlock(block.id);requests.push({kind:'create',after:block.id});}
  else{const index=Math.floor(rng()*(length+1)),text=k%13===0?'😀x':String.fromCharCode(97+k%26);value=peer.insertText(block.id,index,text);requests.push({kind:'insert',block:block.id,index,text});}
  assert(txOf(value));
 }
 const branches=peers.map(r=>r.transactions()),schedule=[],seen=new Set(initial.map(tx=>idKey(tx.id)));let max,lateArrivals=0;
 for(const batch of [...branches].reverse())for(const tx of batch)if(!seen.has(idKey(tx.id))){if(max&&compareOpIds(tx.id,max)<0)lateArrivals++;if(!max||compareOpIds(max,tx.id)<0)max=tx.id;seen.add(idKey(tx.id));schedule.push(tx);}
 const common=[...initial,...schedule],forks=['merge-B','merge-Z'].map(s=>new Replica(s,s,common)),block=forks[0].document().aliveBlocks()[0].id;
 forks[0].insertText(block,0,'L');forks[1].insertText(block,0,'R');
 return {initial,schedule,branches,forks:forks.map(r=>r.transactions()),requests,lateArrivals};
}
const fixture=fixtures();console.log(JSON.stringify(fixture.record));
if(args.includes('--fixtures-only'))process.exit(0);
const binary=arg('--binary',null);if(!binary)throw Error('--binary required except for --fixtures-only');
const native=new NativeClient(binary);let sequence=0,checks=0,currentContext={phase:'fixtures'};
async function init(transactions){const replica=`r${sequence++}`;await native.request({op:'init',replica});if(transactions.length)await native.request({op:'receive',replica,transactions:transactions.map(encodeTransaction)});return replica;}
async function stats(replica,transactions){
 const result=await native.request({op:'stats',replica}),value=result.response.value;
 const unique=[...new Map(transactions.map(tx=>[idKey(tx.id),tx])).values()];
 assert.equal(value.transactions,unique.length);assert.equal(value.clock,Math.max(0,...unique.map(transactionClockMax)));
 const doc=new CrdtDocument(unique);assert.equal(value.rows,[...doc.instances.values()].reduce((n,i)=>n+i.rga.items.size,0));
 assert.equal(value.cuts,unique.reduce((n,tx)=>n+tx.operations.filter(op=>op.command==='splitText').length,0));assert.equal(value.blocks,doc.blocks.size);
 return value;
}
async function check(replica,transactions){
 const result=await native.request({op:'query',replica});
 try{assert.deepEqual(nativeView(result.response.value),view(transactions));}
 catch(error){console.log(JSON.stringify({kind:'native-counterexample',context:currentContext,replica,transactions,typedTransactions:transactions.map(encodeTransaction),expected:view(transactions),response:result.response}));throw error;}
 checks++;return result;
}
try{
 // Warmup/fixture execution is separated from reported benchmark timings.
 for(const group of fixture.groups){currentContext={phase:'fixture',name:group.name};const replica=await init(group.transactions);const result=await check(replica,group.transactions);assert.deepEqual(nativeView(result.response.value),group.expected);await stats(replica,group.transactions);}
 currentContext={phase:'allocator-gap-control'};
 const gapBase=createInitialTransactions('ab'),gapSource=await init(gapBase),gapTarget=`r${sequence++}`;
 await native.request({op:'clone',target:gapTarget,source:gapSource});await native.request({op:'gap',replica:gapSource,ticks:6});
 const sourceGapStats=(await native.request({op:'stats',replica:gapSource})).response.value;assert.equal(sourceGapStats.clock,8);
 const cloneAfterGap=`r${sequence++}`;await native.request({op:'clone',target:cloneAfterGap,source:gapSource});
 const cloneAfterGapStats=await stats(cloneAfterGap,gapBase);assert.equal(cloneAfterGapStats.clock,2);assert.notEqual(cloneAfterGapStats.clock,sourceGapStats.clock);await check(cloneAfterGap,gapBase);
 await native.request({op:'merge',target:gapTarget,source:gapSource});const targetGapStats=await stats(gapTarget,gapBase);
 assert.equal(targetGapStats.clock,2);assert.notEqual(targetGapStats.clock,sourceGapStats.clock);await check(gapTarget,gapBase);
 console.log(JSON.stringify({kind:'native-metadata-control',sourceClock:8,targetClock:2,cloneAfterGapClock:2,gapNotTransmitted:true,cloneDoesNotCopyGap:true,scope:'Local six-tick allocator gap is preserved locally; merging unchanged receipts does not import source-only allocation gaps.'}));
 currentContext={phase:'raw-atomic-error-controls'};
 const errorSeed=createInitialTransactions('ab'),errorTarget=await init(errorSeed),beforeErrorStats=await stats(errorTarget,errorSeed);
 const beforeErrorView=(await check(errorTarget,errorSeed)).response.value;
 const validPeer=new Replica('B','valid batch prefix',errorSeed),validCreate=txOf(validPeer.createBlock('block-A'));
 const conflictingSeed=createInitialTransactions('XY')[0];
 const batch=[encodeTransaction(validCreate),encodeTransaction(conflictingSeed)];
 const rejectedBatch=await native.request({op:'receive',replica:errorTarget,transactions:batch},true);
 assert.equal(rejectedBatch.response.ok,false);assert.equal(rejectedBatch.response.error,'conflicting transaction identity');
 assert.deepEqual(await stats(errorTarget,errorSeed),beforeErrorStats);assert.deepEqual((await check(errorTarget,errorSeed)).response.value,beforeErrorView);
 const conflictPeer=new Replica('C','conflicting global factory', [conflictingSeed]),conflictCreate=txOf(conflictPeer.createBlock('block-A'));
 const errorSource=await init([conflictingSeed,conflictCreate]);
 const rejectedMerge=await native.request({op:'merge',target:errorTarget,source:errorSource},true);
 assert.equal(rejectedMerge.response.ok,false);assert.equal(rejectedMerge.response.error,'conflicting transaction identity');
 assert.deepEqual(await stats(errorTarget,errorSeed),beforeErrorStats);assert.deepEqual((await check(errorTarget,errorSeed)).response.value,beforeErrorView);
 console.log(JSON.stringify({kind:'native-atomic-error-control',receiveBatchRejected:true,mergeRejected:true,statsUnchanged:true,viewUnchanged:true,batch,mergeSourceTransactions:[conflictingSeed,conflictCreate].map(encodeTransaction),expected:[{id:'block-A',text:'ab'}],scope:'Raw typed transaction-identity conflicts intentionally outside the honest-protocol theorem; a valid prefix preceding failure must not leak core/archive/allocator updates.'}));
 if(args.includes('--controls-only'))process.exitCode=0;
 if(args.includes('--controls-only')){await native.close();process.exit(0);}
 for(let seed=1;seed<=cases;seed++)for(const mode of ['insertion','mixed']){
  currentContext={phase:'generated',seed,mode};
  const w=workload(seed,24,mode),replica=await init(w.initial),past=[...w.initial];await check(replica,past);
  for(const tx of w.schedule){await native.request({op:'receive',replica,transactions:[encodeTransaction(tx)]});past.push(tx);await check(replica,past);await native.request({op:'receive',replica,transactions:[encodeTransaction(tx)]});await check(replica,past);}
  const left=await init(w.branches[0]),right=await init(w.branches[1]);await native.request({op:'merge',target:left,source:right});const union=[...new Map([...w.branches[0],...w.branches[1]].map(tx=>[idKey(tx.id),tx])).values()];await check(left,union);
 }
 console.log(JSON.stringify({kind:'native-correctness',cases:cases*2,checks,seedRange:[1,cases],scope:'Original pinned honest client transactions and whole versions; native queries compared to pinned oracle after duplicate/late receipt and direct joins; codec trusted/tested until proved.'}));
 for(const size of sizes)for(const mode of ['insertion','mixed']){
  currentContext={phase:'benchmark',seed:314159,size,mode};
  const w=workload(314159,size,mode),typed=w.schedule.map(encodeTransaction);
  for(let repeat=0;repeat<repeats;repeat++){
   const replica=await init(w.initial);let updateElapsedNs=0,updateRoundTripMs=0;
   for(const tx of typed){const result=await native.request({op:'receive',replica,transactions:[tx]});updateElapsedNs+=result.response.elapsedNs;updateRoundTripMs+=result.roundTripMs;}
   const query=await check(replica,[...w.initial,...w.schedule]),updateStats=await stats(replica,[...w.initial,...w.schedule]);const left=await init(w.forks[0]),right=await init(w.forks[1]);
   const merge=await native.request({op:'merge',target:left,source:right}),union=[...new Map(w.forks.flat().map(tx=>[idKey(tx.id),tx])).values()],mergedQuery=await check(left,union),mergeStats=await stats(left,union);
   console.log(JSON.stringify({kind:'native-benchmark',size,mode,seed:314159,repeat,updateTransactions:typed.length,lateArrivals:w.lateArrivals,
    native:{updateElapsedNs,queryElapsedNs:query.response.elapsedNs,mergeElapsedNs:merge.response.elapsedNs,mergedQueryElapsedNs:mergedQuery.response.elapsedNs},
    roundTrip:{updateMs:updateRoundTripMs,queryMs:query.roundTripMs,mergeMs:merge.roundTripMs,mergedQueryMs:mergedQuery.roundTripMs},
    updateStats,mergeStats,
    scope:'Prepared typed payloads and native input states built outside reported times; native elapsedNs separate from JSON/IPC roundtrip; same process retains prior replicas, so no isolated memory claim.'}));
  }
 }
}finally{await native.close();}
