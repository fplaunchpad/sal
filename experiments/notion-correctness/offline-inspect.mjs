import fs from 'node:fs';
import {Replica,transactionSummary} from './replica.js';
import {initial,view,apply} from './campaign-lib.mjs';
const {trace}=JSON.parse(fs.readFileSync('input.json','utf8')),clients=[0,1,2].map(c=>new Replica(`p0c${c}`,`p0c${c}`,initial(trace.text))),archive=new Map();
for(const e of trace.events){const r=clients[e.client];console.log('EVENT',JSON.stringify(e));if(e.kind==='local'){const out=apply(r,e.request),tx=out?.transaction??out;archive.set(e.alias,tx);console.log(transactionSummary(tx));}else r.receive(archive.get(e.transaction));console.log('VIEW',JSON.stringify(view(r)));if(e===trace.events.at(-1)){for(const b of r.document().blocks.values())console.log('BLOCK',b.id,b.alive,JSON.stringify(r.document().debugBlock(b.id)));}}
