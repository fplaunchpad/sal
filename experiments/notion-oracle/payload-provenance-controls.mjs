// Hand-derived PASS+FAIL source controls; fabricated pending deletes are
// primitive trust-boundary probes, not honestly issued network histories.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {RgaText} from './rga.js';
import {START,idKey} from './ids.js';
const id=counter=>({sessionId:'P',counter});
const items=r=>r.orderedItems().map(x=>({id:x.id,origin:x.originId,kind:x.kind,content:x.content,deleted:x.deleted}));
{
 const r=new Replica('P','P',[]),left=r.createBlock().newBlockId,right=r.createBlock(left).newBlockId;
 const tx=r.insertText(left,0,'a'),doc=r.document();
 const owners=[...doc.instances].filter(([,inst])=>inst.rga.items.has(idKey(tx.id))).map(([name])=>name);
 assert.deepEqual(owners,[left]);assert.notDeepEqual(owners,[right]);
 assert.equal(doc.instances.get(right).rga.items.has(idKey(tx.id)),false);
 console.log(JSON.stringify({name:'honest-located-birth-is-not-global-membership',transactions:r.transactions(),item:tx.id,owners,
   wrongInstance:right,wrongInstanceContains:false,scope:'Honest single-writer create/create/insert history; global ID presence cannot justify selecting another instance.'}));
}
{
 const text=new RgaText(),marker=new RgaText();text.delete([id(7)]);marker.delete([id(7)]);
 text.insertRun(id(7),START,'x');marker.insertSplit(id(7),START);
 assert.equal(text.items.get(idKey(id(7))).deleted,true);
 assert.equal(marker.items.get(idKey(id(7))).deleted,false);
 assert.notEqual(text.items.get(idKey(id(7))).deleted,false);
 assert.notEqual(marker.items.get(idKey(id(7))).deleted,true);
 assert.equal(text.visibleText(),'');assert.notEqual(text.visibleText(),'x');
 console.log(JSON.stringify({name:'fabricated-pending-tombstone-birth-kinds',pendingDelete:[id(7)],text:items(text),marker:items(marker),
   scope:'Direct primitive future-target delete, excluded by honest dependency-closed issuance; text birth reads pending tombstone, split birth stays undeleted.'}));
}
{
 const r=new Replica('P','P',[]),block=r.createBlock().newBlockId;
 const before={clock:{...r.clock},transactions:r.transactions()};
 assert.equal(r.insertText(block,0,''),undefined);assert.equal(r.deleteText(block,0,0),undefined);
 assert.deepEqual({...r.clock},before.clock);assert.deepEqual(r.transactions(),before.transactions);
 const next=r.insertText(block,0,'x');assert.equal(next.id.counter,2);assert.notEqual(next.id.counter,4);
 console.log(JSON.stringify({name:'honest-empty-requests-do-not-reserve',before,afterEmpty:{clock:before.clock,transactions:before.transactions},
   next,scope:'Honest ordinary requests emit undefined and leave both clock and archive unchanged; distinct from empty bootstrap.'}));
}
