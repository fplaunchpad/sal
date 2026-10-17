import assert from 'node:assert/strict';
import fs from 'node:fs';
import {Replica} from './replica.js';
import {view,obs,texts,equal,valid,apply,initial,join,replay,probe,queries,minimize} from './campaign-lib.mjs';
const [mode,seedS,trialsS]=process.argv.slice(2),seed=Number(seedS),trials=Number(trialsS);
if(mode==='replay'||mode==='minimize'){
 const saved=JSON.parse(fs.readFileSync('input.json','utf8'));
 if(mode==='minimize')saved.findings=saved.findings.map(f=>minimize(f.trace,f.probe,f.result.signature));
 for(const f of saved.findings){const p=probe(replay(f.trace),f.probe);assert.equal(p.signature,f.result.signature);assert.deepEqual(p.expected,f.result.expected);assert.deepEqual(p.actual,f.result.actual);}
 console.log(JSON.stringify({mode,checked:saved.findings.length,findings:saved.findings}));process.exit(0);
}
let rng=seed>>>0;function rand(n){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return(rng>>>0)%n;}
const counts={states:0,probes:0,passes:{},failures:{},invalidSetups:0,skippedLarge:0,deliveryChecks:0};
const findings=new Map(),failureStates=[];
function check(trace,txs){
 const v=view(new Replica('viewer','viewer',txs));
 if(v.length>9||v.some(b=>b.chars.length>10)){counts.skippedLarge++;return;}
 counts.states++;const failed=[];
 // Same archive, reverse receipt, then repeat receipt: separate convergence control.
 const other=new Replica('reverse','reverse',[...txs].reverse());for(const t of txs)other.receive(t);
 assert.deepEqual(obs(view(other)),obs(v));counts.deliveryChecks++;
 for(const q of queries(v)){
  counts.probes++;const p=probe(txs,q);assert(p.valid);
  if(!p.signature){counts.passes[q.kind]=(counts.passes[q.kind]??0)+1;continue;}
  counts.failures[p.signature]=(counts.failures[p.signature]??0)+1;failed.push({request:q,signature:p.signature});
  const old=findings.get(p.signature),size=trace.rounds.reduce((s,r)=>s+r.branches.reduce((t,b)=>t+b.requests.length,0),0);
  if(!old||size<old.size){findings.set(p.signature,{trace:structuredClone(trace),q,size});console.error('candidate',p.signature,'setup requests',size);}
 }
 if(failed.length)failureStates.push({trace:structuredClone(trace),probes:failed});
}
// Enumerate both concurrent split boundaries and each subsequent block merge.
if(mode!=='sequential')for(const text of ['ab','abc','abcd'])for(let i=0;i<=text.length;i++)for(let j=0;j<=text.length;j++){
 const trace={text,rounds:[{branches:[{session:'A',requests:[{kind:'split',block:0,index:i}]},{session:'B',requests:[{kind:'split',block:0,index:j}]}]}]};
 let txs=replay(trace);check(trace,txs);
 const v=view(new Replica('viewer','viewer',txs));
 for(let block=1;block<v.length;block++){
  const t=structuredClone(trace);t.rounds.push({branches:[{session:'C',requests:[{kind:'merge',block}]}]});
  check(t,replay(t));
 }
}
for(let trial=0;trial<trials;trial++){
 const text=[['abc'],['ab','cd'],['a','b','c']][trial%3];
 let txs=initial(text),trace={text,rounds:[]};
 for(let round=0;round<10;round++){
  const branches=[],archives=[];
  for(let branch=0;branch<(mode==='sequential'?1:(trial%4===0?3:2));branch++){
   const session=`t${trial}r${round}b${branch}`,r=new Replica(session,session,txs),requests=[];
   for(let step=0;step<2;step++){
    const v=view(r),qs=queries(v);if(!qs.length)break;
    // Choose operation kind uniformly, rather than oversampling long intervals.
    const kinds=[...new Set(qs.map(q=>q.kind))],kind=kinds[rand(kinds.length)];
    const candidates=qs.filter(q=>q.kind===kind),q=candidates[rand(candidates.length)];
    apply(r,q);requests.push(q);
   }
   branches.push({session,requests});archives.push(r.transactions());
  }
  trace.rounds.push({branches});txs=join([txs,...archives]);check(trace,txs);
 }
 if(trial%10===0)console.error('trial',trial,'probes',counts.probes);
}
const shrunk=[];
for(const [signature,f]of findings){console.error('minimizing',signature);shrunk.push(minimize(f.trace,f.q,signature));}
for(const kind of ['insert','delete','split','merge','bold'])assert(counts.passes[kind]>0);
if(mode!=='sequential')assert(counts.failures['bold:missed']>0&&counts.failures['bold:outside']>0);
console.log(JSON.stringify({mode,seed,trials,counts,failureStates,findings:shrunk}));
