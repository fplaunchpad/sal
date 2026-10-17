import assert from 'node:assert/strict';
import fs from 'node:fs';
import {Network,replay,minimize} from './network-lib.mjs';
import {view,queries,texts} from './campaign-lib.mjs';
const [seedS,trialsS,stepsS,mode]=process.argv.slice(2),seed=Number(seedS),trials=Number(trialsS),steps=Number(stepsS);
if(mode==='replay'){
 const saved=JSON.parse(fs.readFileSync('input.json','utf8'));let edits=0;
 for(const t of saved.traces){const n=replay(t.trace);assert.deepEqual(n.failures,t.failures);assert.deepEqual(n.sync().display,t.final.display);edits+=n.stats.edits;}
 for(const f of saved.findings){const n=replay(f.trace);assert(n.failures.some(x=>x.signature===f.failure.signature&&x.classification==='unexplained'));}
 console.log(JSON.stringify({mode:'network-replay',seed:saved.seed,checkedTraces:saved.traces.length,checkedEdits:edits,findings:saved.findings}));process.exit(0);
}
let rng=seed>>>0;const rand=n=>{rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return(rng>>>0)%n;};
const counts={edits:0,deliveries:0,deliveredTransactions:0,causalChecks:0,duplicateChecks:0,continuedDifferentViewEdits:0,partiallyDeliveredEdits:0,synchronizedTrials:0,passes:{},failures:{},classifications:{},generationExceptions:0};
const traces=[],candidates=new Map();
for(let trial=0;trial<trials;trial++){
 const text=[['abc'],['ab','cd'],['a','b','c'],['a🙂b','cd']][trial%4],sessions=Array.from({length:trial%3===0?4:3},(_,i)=>`t${trial}s${i}`),n=new Network(text,sessions);
 const family=['mixed','structural','richtext','deletion'][trial%4];
 let editNo=0;let trialError=null;
 try{
  for(let step=0;step<steps;step++){
   const eligible=[];for(const to of sessions)for(const e of n.eligible(to))eligible.push({to,id:e.id});
   // An initial prolonged partition, then independent one-request causal
   // deliveries interleaved with new editing. No intermediate global barrier.
   if(step>=12&&eligible.length&&rand(100)<(trial%5===0?60:35)){
    const d=eligible[rand(eligible.length)];n.deliver(d.to,d.id);continue;
   }
   let session=sessions[(step<12?step:rand(sessions.length))%sessions.length],v=view(n.replicas.get(session));
   let qs=queries(v);
   if(!qs.length){
    // An empty replica cannot issue these requests. Its saved delivery failure
    // is retained; keep the rest of the network active until it recovers.
    const available=sessions.filter(s=>view(n.replicas.get(s)).length>0);
    if(!available.length){if(eligible.length){const d=eligible[rand(eligible.length)];n.deliver(d.to,d.id);continue;}break;}
    session=available[rand(available.length)];v=view(n.replicas.get(session));qs=queries(v);
   }
   let kinds=family==='structural'?['split','merge','insert']:family==='richtext'?['bold','bold','split','merge','insert','delete']:family==='deletion'?['delete','delete','split','merge','insert','bold']:['split','merge','bold','delete','insert'];
   if(v.length>8)kinds=['merge'];else if(v.some(b=>b.chars.length>12))kinds=['delete','split'];
   kinds=kinds.filter(k=>qs.some(q=>q.kind===k));if(!kinds.length)kinds=[...new Set(qs.map(q=>q.kind))];
   const kind=kinds[rand(kinds.length)];qs=qs.filter(q=>q.kind===kind);
   const q=structuredClone(qs[rand(qs.length)]);if(kind==='insert')q.text=['X','y','pq','🙂'][rand(4)];
   const prior=n.failures.length;n.edit(session,q,`e${editNo++}`);
   if(n.failures.length===prior)counts.passes[kind]=(counts.passes[kind]??0)+1;
  }
 }catch(e){trialError={message:e.message,stack:e.stack};counts.generationExceptions++;}
 let final=null;try{final=n.sync(rand);counts.synchronizedTrials++;}catch(e){trialError={message:e.message,stack:e.stack};}
 const trace={text,sessions,events:n.events};
 for(const f of n.failures){counts.failures[f.signature]=(counts.failures[f.signature]??0)+1;counts.classifications[f.classification]=(counts.classifications[f.classification]??0)+1;
  if(f.classification==='unexplained'&&!candidates.has(f.signature))candidates.set(f.signature,{...trace,events:trace.events.slice(0,f.step+1)});
 }
 for(const k of Object.keys(n.stats))counts[k]+=n.stats[k];
 traces.push({trial,family,trace,failures:n.failures,stats:n.stats,final,error:trialError});
 if(trial%10===0)console.error('network trial',trial,'edits',counts.edits,'failures',JSON.stringify(counts.failures));
}
// Preserve interrupted schedules and diagnostics as data, even on failure.
assert(counts.continuedDifferentViewEdits>0&&counts.partiallyDeliveredEdits>0);
for(const k of ['insert','delete','split','merge','bold'])assert(counts.passes[k]>0,'no passing control for '+k);
const findings=[];
for(const [sig,trace]of candidates){console.error('network minimizing unexplained',sig);findings.push(minimize(trace,sig));}
console.log(JSON.stringify({mode:'network-search',seed,trials,steps,counts,traces,findings,scope:'Measured local effect against independent positional list semantics; insertion ignores only new-character formatting inheritance, preserving existing marks; persistent sessions, causal whole-request delivery, eventual equal-archive display; source-based known-root classification is diagnostic, no production correspondence or proof.'}));
