import {Replica} from './replica.js';
import {request} from './positional-spec.mjs';
import {TransactionSet} from './transaction-set.mjs';
const seed = new Replica('seed','seed',[]);
const {newBlockId:block} = seed.createBlock(); seed.insertText(block,0,'abcd');
const initial = seed.transactions();
const view = r => r.document().aliveBlocks().map(b => ({id:b.id,text:r.document().blockText(b.id),
  characters:r.document().blockCharacters(b.id).map(c=>({text:c.text,bold:!!c.bold}))}));
const obs = v => v.map(b=>b.characters);
let state = 0x514a2d19, checks=0, states=0;
const kinds=process.argv.includes('--core')?['split','insert','delete']:['split','merge','insert','delete'];
function random(n) { state ^= state << 13; state ^= state >>> 17; state ^= state << 5; return (state >>> 0) % n; }
function check(transactions, history) {
  states++;
  const before=view(new Replica('observer','observer',transactions));
  for(let bi=0;bi<before.length;bi++) {
    const n=before[bi].characters.length;
    for(const kind of ['split','insert','delete']) for(let index=0;index<=n;index++) {
      if(kind==='delete' && index===n) continue;
      const r=new Replica('check','check',transactions);
      const op=kind==='delete'?{kind,block:bi,start:index,end:Math.min(n,index+2)}:{kind,block:bi,index,text:'X'};
      const expected=request(obs(before),op); let result,actual,error;
      try {
        result=kind==='split'?r.splitBlock(before[bi].id,index):kind==='insert'?r.insertText(before[bi].id,index,'X'):r.deleteText(before[bi].id,index,op.end);
        actual=view(r);
      } catch(e) {error=e.message;}
      checks++;
      if(error || JSON.stringify(obs(actual))!==JSON.stringify(expected)) {
        console.log(JSON.stringify({name:'reachable-local-counterexample',initial,history,transactions,request:op,before,
          generated:result?.transaction??result,expected,actual,error}));
        console.error(JSON.stringify({states,checks,seed:'0x514a2d19',result:'counterexample'})); return false;
      }
    }
  }
  return true;
}
for(let trial=0;trial<80;trial++) {
  let transactions=initial,history=[];
  for(let round=0;round<7;round++) {
    const branches=[];
    for(let branch=0;branch<2;branch++) {
      const r=new Replica(`t${trial}r${round}b${branch}`,'branch',transactions), requests=[];
      for(let step=0;step<2;step++) {
        const blocks=view(r), bi=random(blocks.length), target=blocks[bi], n=target.characters.length;
        const kind=kinds[random(kinds.length)];
        const index=random(n+1); let result;
        const op={kind,block:target.id,index};
        if(kind==='split') result=r.splitBlock(target.id,index);
        if(kind==='merge') result=r.mergeBlock(target.id);
        if(kind==='insert') result=r.insertText(target.id,index,'X');
        if(kind==='delete') {op.start=index;op.end=Math.min(n,index+1+random(2));result=r.deleteText(target.id,op.start,op.end);}
        requests.push({request:op,transaction:result?.transaction??result});
      }
      branches.push(r.transactions()); history.push({trial,round,branch,requests});
    }
    try { transactions=TransactionSet.merge(new TransactionSet(transactions),...branches.map(x=>new TransactionSet(x))).transactions(); }
    catch(e) {console.log(JSON.stringify({name:'reachable-merge-error',initial,history,error:e.message}));process.exit(1);}
    if(!check(transactions,history)) process.exit(1);
  }
}
console.error(JSON.stringify({states,checks,seed:'0x514a2d19',kinds,result:'no counterexample'}));
