// Replays persistent-client event schedules and shrinks conservation failures.
import fs from 'node:fs';
import {Replica} from './replica.js';
import {initial,view,obs,texts,equal,valid,apply} from './campaign-lib.mjs';
import {request} from './positional-spec.mjs';
const bag=v=>v.flatMap(b=>b.chars.map(c=>c.text)).sort().join('');
export function replay(trace){
 const txs=initial(trace.text),clients=[0,1,2].map(c=>({r:new Replica(`p0c${c}`,`p0c${c}`,txs),known:new Set()})),archive=new Map();
 let failure=null;
 for(let i=0;i<trace.events.length;i++){
  const e=trace.events[i],cl=clients[e.client],before=view(cl.r);
  if(e.kind==='local'){
   if(!valid(before,e.request))throw Error('invalid local');
   const result=apply(cl.r,e.request),tx=result?.transaction??result,alias=e.alias??i;
   archive.set(alias,{tx,deps:new Set(cl.known)});cl.known.add(alias);
  }else{
   const a=archive.get(e.transaction);if(!a)throw Error('missing tx');if(![...a.deps].every(d=>cl.known.has(d)))throw Error('noncausal receive');
   cl.r.receive(a.tx);cl.known.add(e.transaction);
  }
  const after=view(cl.r);
  if(bag(before)!==bag(after)&&(!e.request||e.request.kind==='split'||e.request.kind==='merge'))failure={event:i,before,actual:after,beforeBag:bag(before),afterBag:bag(after)};
 }
 return failure;
}
const input=JSON.parse(fs.readFileSync(process.argv[2]??'input.json','utf8'));
const f=input.findings.find(f=>f.kind==='conservation');if(!f)throw Error('no conservation finding');
let trace=structuredClone(f.trace);trace.events.forEach((e,i)=>{if(e.kind==='local')e.alias=i;});
if(!replay(trace))throw Error('initial trace does not reproduce');
let attempts=0,invalid=0;
function passes(t){attempts++;try{return !!replay(t);}catch{invalid++;return false;}}
function without(t,removed){const aliases=new Set([...removed].filter(i=>t.events[i].kind==='local').map(i=>t.events[i].alias));return {...t,events:t.events.filter((e,i)=>!removed.has(i)&&!(e.kind==='receive'&&aliases.has(e.transaction)))};}
// ddmin chunks, then single request/receive deletions, numeric reductions, seed text.
let width=Math.ceil(trace.events.length/2);
while(width>=1){let changed=false;for(let start=0;start<trace.events.length;start+=width){const t=without(trace,new Set(Array.from({length:Math.min(width,trace.events.length-start)},(_,i)=>start+i)));if(t.events.length&&passes(t)){trace=t;changed=true;console.error('shrunk',trace.events.length,'attempts',attempts);break;}}if(!changed)width=Math.floor(width/2);}
let changed=true;while(changed){changed=false;
 outer:for(let i=0;i<trace.events.length;i++){let t=without(trace,new Set([i]));if(t.events.length&&passes(t)){trace=t;changed=true;break;}
 const e=trace.events[i];if(e.kind!=='local')continue;
 for(const key of ['block','index','start','end'])if(e.request[key]>0)for(const n of [...new Set([0,e.request[key]-1])]){t=structuredClone(trace);t.events[i].request[key]=n;if(passes(t)){trace=t;changed=true;break outer;}}
 }
 if(changed)continue;
 if(trace.text.length>1)for(let b=0;b<trace.text.length;b++){const t=structuredClone(trace);t.text.splice(b,1);if(passes(t)){trace=t;changed=true;break;}}
 if(changed)continue;
 for(let b=0;b<trace.text.length;b++)for(let j=0;j<trace.text[b].length;j++){const t=structuredClone(trace);t.text[b]=t.text[b].slice(0,j)+t.text[b].slice(j+1);if(passes(t)){trace=t;changed=true;break;}}
}
const result=replay(trace);console.log(JSON.stringify({trace,result,shrink:{attempts,invalid,criterion:'event deletion (local deletion also removes its receives), numeric reductions and seed-block/character deletion fixed point; no global minimality claim'}}));
