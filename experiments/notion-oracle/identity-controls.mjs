// Test the independent model's concrete semantic checks against intentional
// broken variants. This is harness sensitivity evidence, not source validation.
import assert from 'node:assert/strict';
import {IdentityDocument} from './identity-spec.mjs';
class DeleteNoOp extends IdentityDocument {
  step(command) { return command.kind==='delete'?this:super.step(command); }
}
class SplitDropsSuffix extends IdentityDocument {
  step(command) {
    super.step(command);
    if(command.kind==='split') {
      const target=this.blocks.find(b=>b.id===command.target);
      for(const slot of target.slots) slot.visible=false;
    }
    return this;
  }
}
const fixtures=[
  {name:'split-retains-suffix',commands:[
    {kind:'create',block:'left',instance:'text'},
    {kind:'insert',instance:'text',origin:'start',characters:[{id:'a',text:'a'},{id:'b',text:'b'}]},
    {kind:'create',block:'right',instance:'right-text',after:'left'},
    {kind:'split',instance:'text',origin:'a',id:'cut',target:'right'}
  ],expected:[['left','a'],['right','b']]},
  {name:'delete-retains-hidden-anchor',commands:[
    {kind:'create',block:'left',instance:'text'},
    {kind:'insert',instance:'text',origin:'start',characters:[{id:'a',text:'a'},{id:'b',text:'b'}]},
    {kind:'delete',instance:'text',ids:['a']},
    {kind:'insert',instance:'text',origin:'a',characters:[{id:'x',text:'X'}]}
  ],expected:[['left','Xb']]}
];
function mismatches(Model) {
  return fixtures.flatMap(f=>{
    const s=new Model();for(const command of f.commands)s.step(command);
    return JSON.stringify(s.view())===JSON.stringify(f.expected)?[]:[{fixture:f.name,expected:f.expected,actual:s.view()}];
  });
}
assert.deepEqual(mismatches(IdentityDocument),[]);
for(const [name,Model,requiredFixture] of [
  ['delete-no-op',DeleteNoOp,'delete-retains-hidden-anchor'],
  ['split-drops-suffix',SplitDropsSuffix,'split-retains-suffix']]) {
  const failures=mismatches(Model);
  assert(failures.some(f=>f.fixture===requiredFixture));
  console.log(JSON.stringify({name:'identity-harness-mutant-control',mutant:name,detected:true,failures}));
}
