// Inspect a saved representative separately from the independent oracle.
import fs from 'node:fs';
import assert from 'node:assert/strict';
import {replay} from './network-lib.mjs';
import {view,obs,texts} from './campaign-lib.mjs';
const saved=JSON.parse(fs.readFileSync('input.json','utf8'));
const findings=saved.findings.map(f=>{
 const displays=[];
 for(let i=0;i<f.trace.events.length;i++){
  const n=replay({...f.trace,events:f.trace.events.slice(0,i+1)});
  displays.push({event:f.trace.events[i],replicas:[...n.replicas].map(([session,r])=>({session,display:texts(obs(view(r)))}))});
 }
 const n=replay(f.trace),final=n.sync(),r=[...n.replicas.values()][0],d=r.document();
 assert.deepEqual(final.display,[],'minimized empty-view example recovered after synchronization');
 return {...f,displays,final,blocks:[...d.blocks.values()].map(b=>({id:b.id,alive:b.alive,text:d.blockText(b.id)})),blockOrder:d.blockOrder};
});
console.log(JSON.stringify({mode:'network-diagnose',findings}));
