// Hand-derived controls shared with the finite-tree and endpoint proof models.
// Direct source primitive calls exercise the representation boundary; these
// are not whole-client reachability certificates.
import assert from 'node:assert/strict';
import {RgaText} from './rga.js';
import {START, END} from './ids.js';
import {TextSlice, textSliceContainsItem, itemsInTextSlice} from './text-slice-tree.js';
const id = counter => ({sessionId: 'A', counter});
const physical = rga => rga.orderedItems().map(x => ({id:x.id, origin:x.originId,
  kind:x.kind, content:x.content, deleted:x.deleted}));
function seed() {
  const rga = new RgaText();
  rga.insertRun(id(1), START, 'd');
  rga.insertRun(id(2), START, 'a');
  rga.insertRun(id(3), id(2), 'bc');
  rga.delete([id(3)]);
  return rga;
}
{
  const rga=seed();
  rga.insertRun(id(10), id(3), 'XY');
  assert.deepEqual(rga.orderedItems().map(x=>x.id.counter),[2,3,10,11,4,1]);
  assert.equal(rga.visibleText(),'aXYcd');
  assert.notEqual(rga.visibleText(),'acdXY');
  console.log(JSON.stringify({name:'physical-hidden-origin-subtree-splice',physical:physical(rga),
    visible:rga.visibleText(),note:'Matches the hand-derived OriginTree hidden nonroot fixture; stored insertion order is not traversal order.'}));
}
for (const [origin, marker, expected] of [[3,10,'left'],[5,11,'right']]) {
  const rga=seed();rga.insertSplit(id(5),id(3));
  const left=new TextSlice({textInstanceId:'I',startItemId:START,endItemId:id(5)});
  const right=new TextSlice({textInstanceId:'I',startItemId:id(5),endItemId:END});
  rga.insertSplit(id(marker),id(origin));
  const owners=[['left',left],['right',right]].filter(([,slice])=>textSliceContainsItem(slice,rga,id(marker)))
    .map(([owner])=>owner);
  assert.deepEqual(owners,[expected]);
  assert.notDeepEqual(owners,[expected==='left'?'right':'left']);
  // The new marker exists physically inside one old interval before the
  // endpoint update. It is not rendered as text.
  const retained=itemsInTextSlice(expected==='left'?left:right,rga,
    {includeDeleted:true,includeSplitItems:true}).map(x=>x.id.counter);
  assert(retained.includes(marker));
  assert.equal(rga.visibleText(),'acd');
  console.log(JSON.stringify({name:'integrate-marker-before-routing',origin:id(origin),marker:id(marker),
    owners,physical:physical(rga),retained,
    note:'The new marker belongs to the origin interval after RGA integration and before endpoint splitting.'}));
}
