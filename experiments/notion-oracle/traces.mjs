import {Replica} from './replica.js';
const seed=new Replica('seed','seed',[]);
const {newBlockId:block}=seed.createBlock(); seed.insertText(block,0,'abcd');
const initial=seed.transactions();
const view=r=>r.document().aliveBlocks().map(b=>[b.id,r.document().blockText(b.id)]);
function run(kind,splitSession='A',editSession='B',index=2){
 const a=new Replica(splitSession,'split',initial), b=new Replica(editSession,'edit',initial);
 const split=a.splitBlock(block,2).transaction;
 const edit=kind==='insert'?b.insertText(block,index,'X'):b.deleteText(block,1,3);
 const local=[view(a),view(b)]; a.receive(edit);b.receive(split);
 const c=new Replica('C','delivery split first',initial),d=new Replica('D','delivery edit first',initial);
 c.receive(split);c.receive(edit);d.receive(edit);d.receive(split);
 console.log(JSON.stringify({kind,splitSession,editSession,index,initial:view(seed),split,edit,local,afterExchange:[view(a),view(b)],deliveryOrders:[view(c),view(d)],converged:[a,b,c,d].every(r=>JSON.stringify(view(r))===JSON.stringify(view(a)))}));
}
run('insert');run('insert','B','A');run('insert','A','B',1);run('insert','A','B',3);run('delete');
