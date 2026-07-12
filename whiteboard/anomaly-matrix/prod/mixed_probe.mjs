// Mixed-direction probe: A types FORWARD (each char after own previous), B types
// BACKWARD (every char at the same index), same spot, then sync. Plus a 200-trial
// re-run of pure-backward for Yjs (random clientIDs -> more tiebreak coverage).
import * as Y from 'yjs';
import { next as AM } from '@automerge/automerge';
import { LoroDoc } from 'loro-crdt';
import { AbsList } from 'list-positions';

function contiguous(text, run) {
  const idx = [...run].map(c => text.indexOf(c)).filter(i => i >= 0).sort((a,b)=>a-b);
  return idx.length === run.length && idx[idx.length-1] - idx[0] === idx.length - 1;
}
const A_RUN='DEF', B_RUN='xyz';

function yjsTrial(mixed, lenA=3) {
  const b=new Y.Doc(); b.getText('t').insert(0,'[]');
  const A=new Y.Doc(), B=new Y.Doc();
  Y.applyUpdate(A,Y.encodeStateAsUpdate(b)); Y.applyUpdate(B,Y.encodeStateAsUpdate(b));
  const ra='DEFGH'.slice(0,lenA), rb='xyzuv'.slice(0,lenA);
  for(let i=0;i<ra.length;i++) A.getText('t').insert(mixed?1+i:1, ra[i]);
  for(let i=0;i<rb.length;i++) B.getText('t').insert(1, rb[i]);
  Y.applyUpdate(A,Y.encodeStateAsUpdate(B)); Y.applyUpdate(B,Y.encodeStateAsUpdate(A));
  const m=A.getText('t').toString();
  return {m, ok: contiguous(m,ra)&&contiguous(m,rb)};
}
function amTrial(mixed) {
  let b=AM.from({t:''}); b=AM.change(b,d=>AM.splice(d,['t'],0,0,'[]'));
  let A=AM.clone(b), B=AM.clone(b);
  for(let i=0;i<3;i++) A=AM.change(A,d=>AM.splice(d,['t'],mixed?1+i:1,0,A_RUN[i]));
  for(let i=0;i<3;i++) B=AM.change(B,d=>AM.splice(d,['t'],1,0,B_RUN[i]));
  const m=AM.merge(AM.clone(A),AM.clone(B)).t;
  return {m, ok: contiguous(m,A_RUN)&&contiguous(m,B_RUN)};
}
let pid=100;
function loroTrial(mixed) {
  const b=new LoroDoc(); b.setPeerId(BigInt(pid++)); b.getText('t').insert(0,'[]'); b.commit();
  const A=new LoroDoc(); A.setPeerId(BigInt(pid++)); A.import(b.export({mode:'snapshot'}));
  const B=new LoroDoc(); B.setPeerId(BigInt(pid++)); B.import(b.export({mode:'snapshot'}));
  for(let i=0;i<3;i++){A.getText('t').insert(mixed?1+i:1,A_RUN[i]); A.commit();}
  for(let i=0;i<3;i++){B.getText('t').insert(1,B_RUN[i]); B.commit();}
  A.import(B.export({mode:'update'})); B.import(A.export({mode:'update'}));
  const m=A.getText('t').toString();
  return {m, ok: contiguous(m,A_RUN)&&contiguous(m,B_RUN)};
}
function lpTrial(mixed) {
  const b=new AbsList(); b.insertAt(0,'['); b.insertAt(1,']');
  const A=new AbsList(), B=new AbsList();
  for(const [p,v] of b.entries()){A.set(p,v);B.set(p,v);}
  for(let i=0;i<3;i++) A.insertAt(mixed?1+i:1, A_RUN[i]);
  for(let i=0;i<3;i++) B.insertAt(1, B_RUN[i]);
  for(const [p,v] of B.entries()) A.set(p,v);
  const m=[...A.values()].join('');
  return {m, ok: contiguous(m,A_RUN)&&contiguous(m,B_RUN)};
}
for (const [name, f] of [['yjs',yjsTrial],['automerge',amTrial],['loro',loroTrial],['list-positions',lpTrial]]) {
  const out=new Map(); let bad=0;
  for(let t=0;t<50;t++){const r=f(true); if(!r.ok)bad++; out.set(r.m,(out.get(r.m)??0)+1);}
  console.log(`[${name}] MIXED fwd-vs-bwd: interleaved ${bad}/50; ${[...out.entries()].map(([k,v])=>`"${k}"x${v}`).join(' ')}`);
}
// Yjs pure-backward, 200 trials, run length 5
{ const out=new Map(); let bad=0;
  for(let t=0;t<200;t++){const r=yjsTrial(false,5); if(!r.ok)bad++; out.set(r.m,(out.get(r.m)??0)+1);}
  console.log(`[yjs] pure-bwd x200 len5: interleaved ${bad}/200; ${[...out.entries()].map(([k,v])=>`"${k}"x${v}`).join(' ')}`);
}
