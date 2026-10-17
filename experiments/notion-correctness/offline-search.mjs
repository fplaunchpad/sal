// Persistent clients: causal receive events, long disconnected local bursts.
// No concurrent numeric-position reference order is assumed.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {initial,view,obs,texts,equal,valid,apply,queries} from './campaign-lib.mjs';
import {request} from './positional-spec.mjs';
const seed=+(process.argv[2]??17101),trials=+(process.argv[3]??50),steps=+(process.argv[4]??150),mode=process.argv[5]??'mixed';
let rng=seed;function rand(n){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return (rng>>>0)%n;}
const bag=v=>v.flatMap(b=>b.chars.map(c=>c.text)).sort().join('');
const counts={trials:0,locals:0,receives:0,probes:0,equalSetChecks:0,localFailures:0,conservationFailures:0,exceptions:0};
const findings=[], signatures=new Set();
function signature(q,before,expected,actual){
 if(!equal(texts(expected),texts(actual))){const b=x=>x.flat().map(c=>c.text).sort().join('');return q.kind+':'+(b(expected)===b(actual)?'placement':'content');}
 return q.kind+':format';
}
function remember(f){counts[f.kind==='local'?'localFailures':f.kind==='conservation'?'conservationFailures':'exceptions']++;const key=f.kind+':'+(f.signature??f.error);if(!signatures.has(key)){signatures.add(key);findings.push(f);console.error('finding',key,'events',f.trace.events.length);}}
function setup(text,trial){const txs=initial(text);const clients=Array.from({length:3},(_,i)=>({r:new Replica(`p${trial}c${i}`,`p${trial}c${i}`,txs),known:new Set()}));return {clients,archive:new Map(),events:[],text,conservation:mode==='structural'};}
function local(s,c,q,probe=false){
 const cl=s.clients[c],before=view(cl.r),expected=request(obs(before),q),event={kind:'local',client:c,request:q},alias=s.events.length;
 s.events.push(event);let result,after;
 try{result=apply(cl.r,q);after=view(cl.r);}catch(e){remember({kind:'exception',error:e.message,trace:{text:s.text,events:structuredClone(s.events)}});return false;}
 const tx=result?.transaction??result;if(!tx?.id)throw Error('local did not generate transaction');
 s.archive.set(alias,{tx,deps:new Set(cl.known)});cl.known.add(alias);counts.locals++;
 if(s.conservation&&bag(before)!==bag(after))remember({kind:'conservation',before,actual:after,trace:{text:s.text,events:structuredClone(s.events)}});
 const compared=obs(after);if(q.kind==='insert'&&compared[q.block])for(let k=0;k<[...q.text].length;k++)if(compared[q.block][q.index+k])compared[q.block][q.index+k].bold=false;
 if(!equal(expected,compared))remember({kind:'local',signature:signature(q,before,expected,obs(after)),before,expected,actual:obs(after),trace:{text:s.text,events:structuredClone(s.events)}});
 return true;
}
function eligible(s,c){return [...s.archive].filter(([a,x])=>!s.clients[c].known.has(a)&&[...x.deps].every(d=>s.clients[c].known.has(d)));}
function receive(s,c,a){const cl=s.clients[c],entry=s.archive.get(a);assert(entry&&[...entry.deps].every(d=>cl.known.has(d)));const before=view(cl.r);s.events.push({kind:'receive',client:c,transaction:a});cl.r.receive(entry.tx);cl.known.add(a);counts.receives++;let after;try{after=view(cl.r);}catch(e){remember({kind:'exception',error:e.message,trace:{text:s.text,events:structuredClone(s.events)}});return false;}if(s.conservation&&bag(before)!==bag(after))remember({kind:'conservation',before,actual:after,trace:{text:s.text,events:structuredClone(s.events)}});return true;}
function checkSets(s){for(let a=0;a<3;a++)for(let b=a+1;b<3;b++)if(equal([...s.clients[a].known].sort((x,y)=>x-y),[...s.clients[b].known].sort((x,y)=>x-y))){counts.equalSetChecks++;assert.deepEqual(view(s.clients[a].r),view(s.clients[b].r));}}
// Hand-derived calibration: local success and a deliberately false edit oracle.
{const s=setup(['ab'],999999);s.conservation=false;local(s,0,{kind:'insert',block:0,index:1,text:'X'});assert.equal(texts(obs(view(s.clients[0].r)))[0],'aXb');assert.notEqual(texts(obs(view(s.clients[0].r)))[0],'abX');assert.equal(eligible(s,1).length,1);receive(s,1,0);assert.deepEqual(view(s.clients[0].r),view(s.clients[1].r));
 // Causal predecessor restriction is active, not merely a comment.
 local(s,0,{kind:'delete',block:0,start:0,end:1});assert.equal(eligible(s,2).length,1);assert.equal(eligible(s,2)[0][0],0);}
for(const k of Object.keys(counts))counts[k]=0;
assert.equal(findings.length,0);
for(let trial=0;trial<trials;trial++){
 const text=trial%3===0?['abcd']:trial%3===1?['a','b','c']:['ab','cd'];const s=setup(text,trial);let live=true;
 // Long offline bursts, followed by small alternating causal-prefix deliveries.
 for(let step=0;step<steps&&live;step++){
  const c=Math.floor(step/7)%3,cl=s.clients[c],v=view(cl.r);
  const e=eligible(s,c);
  if(e.length&&(step%23>=17||rand(9)===0)){const [a]=e[rand(e.length)];live=receive(s,c,a);}
  else {
   let qs=queries(v).filter(q=>mode!=='structural'||q.kind==='split'||q.kind==='merge');
   // Keep state size finite without excluding tombstone-heavy paths.
   if(v.length>10)qs=qs.filter(q=>q.kind!=='split');
   if(v.some(b=>b.chars.length>12))qs=qs.filter(q=>q.kind!=='insert');
   const kinds=mode==='structural'?['split','merge']:['split','merge','insert','delete','bold'];
   const k=kinds[rand(kinds.length)],preferred=qs.filter(q=>q.kind===k);if(preferred.length)qs=preferred;
   if(!qs.length)continue;
   live=local(s,c,qs[rand(qs.length)]);
  }
  if(step%10===0)checkSets(s);
 }
 if(live){for(let c=0;c<3;c++){let es;while((es=eligible(s,c)).length&&live)live=receive(s,c,es[rand(es.length)][0]);}if(live)checkSets(s);}
 counts.trials++;
 if(trial%10===0)console.error(mode,trial,counts.locals,counts.receives);
}
console.log(JSON.stringify({mode,seed,trials,steps,counts,findings,scope:'persistent distinct sessions; complete known archive recorded as causal dependencies; only whole transactions received; local immediate list semantics; equal-set display convergence; structural mode conserves character multiset across local edits and receives'}));
