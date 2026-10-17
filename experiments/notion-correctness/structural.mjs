// Separate correctness property: splits and block merges must not erase text.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {view,obs,texts,equal,valid,apply,initial,join,replay,queries,probe,minimize} from './campaign-lib.mjs';
let rng=17003,states=0,checks=0,examples=[];
function rand(n){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return(rng>>>0)%n;}
const bag=v=>v.flatMap(b=>b.chars.map(c=>c.text)).sort().join('');
for(let trial=0;trial<100;trial++){
 const text=trial%2?['a','b','c']:['abcd'];let txs=initial(text),trace={text,rounds:[]};
 for(let round=0;round<10;round++){
  const before=view(new Replica('viewer','viewer',txs)),branches=[],archives=[];
  for(let branch=0;branch<3;branch++){
   const session=`s${trial}r${round}b${branch}`,r=new Replica(session,session,txs),requests=[];
   for(let step=0;step<2;step++){
    const qs=queries(view(r)).filter(q=>q.kind==='split'||q.kind==='merge');
    const merges=qs.filter(q=>q.kind==='merge');const choices=merges.length&&rand(2)?merges:qs;
    const q=choices[rand(choices.length)];apply(r,q);requests.push(q);
   }
   branches.push({session,requests});archives.push(r.transactions());
  }
  txs=join([txs,...archives]);trace.rounds.push({branches});
  const after=view(new Replica('viewer','viewer',txs));states++;
  if(bag(before)!==bag(after)){
   examples.push({trace:structuredClone(trace),before,after});console.error('STRUCTURAL TEXT LOSS',trial,round);break;
  }
  for(const q of queries(after).filter(q=>q.kind==='merge'||q.kind==='split')){
   checks++;const p=probe(txs,q);if(p.signature&&!examples.some(f=>f.result?.signature===p.signature))examples.push(minimize(trace,q,p.signature));
  }
 }
 if(trial%10===0)console.error('structural',trial,states,checks);
}
console.log(JSON.stringify({mode:'structural',seed:17003,counts:{states,checks},findings:examples}));
