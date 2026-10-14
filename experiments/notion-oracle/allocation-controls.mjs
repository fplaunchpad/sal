// Distinguish transaction-first sorting from honest whole-run clock observation.
// The first fixture is intentionally NOT an honestly prepared client message.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {IdentityDocument} from './identity-spec.mjs';
const seed = new Replica('seed','seed',[]);
const {newBlockId:block} = seed.createBlock();
const run={id:{sessionId:'Z',counter:10},operations:[{command:'insertText',
  pointer:{table:'block',id:block},path:[],opVersion:2,
  args:{textInstanceId:block,searchLabel:'',id:{sessionId:'Z',counter:10},
    originId:'start',content:'ab'}}]};
const dishonest={id:{sessionId:'A',counter:11},operations:[{command:'insertText',
  pointer:{table:'block',id:block},path:[],opVersion:2,
  args:{textInstanceId:block,searchLabel:'',id:{sessionId:'A',counter:11},
    originId:{sessionId:'Z',counter:10},content:'X'}}]};
const raw = new Replica('observer','observer',[...seed.transactions(),run,dishonest]);
// Hand source-tree calculation: b=Z@11 and X=A@11 are siblings below a=Z@10;
// descending session order visits b before X. Sorting first tx IDs differs.
assert.equal(raw.document().blockText(block),'abX');
const direct = new IdentityDocument();
direct.step({kind:'create',block,instance:block});
direct.step({kind:'insert',instance:block,origin:'start',characters:[{id:'Z:10',text:'a'},{id:'Z:11',text:'b'}]});
direct.step({kind:'insert',instance:block,origin:'Z:10',characters:[{id:'A:11',text:'X'}]});
assert.deepEqual(direct.view(),[[block,'aXb']]);
assert.notEqual(raw.document().blockText(block),direct.view()[0][1]);
const honest=new Replica('A','A',[...seed.transactions(),run]);
const prepared=honest.insertText(block,1,'X');
assert.equal(prepared.id.counter,12);
assert.notEqual(prepared.id.counter,dishonest.id.counter);
assert.equal(honest.document().blockText(block),'aXb');
assert.notEqual(honest.document().blockText(block),'abX');
console.log(JSON.stringify({name:'whole-run-clock-observation',initial:seed.transactions(),run,
  fabricated:{transaction:dishonest,result:raw.document().blockText(block),honestlyIssuable:false},
  independentImmediateSplice:direct.view(),honest:{transaction:prepared,result:honest.document().blockText(block)},
  conclusion:'First-ID sorting alone is insufficient; honest receive observes the complete run maximum.'}));
