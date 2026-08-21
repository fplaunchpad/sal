import test from 'node:test';
import assert from 'node:assert/strict';
import { DistributedReplica } from '../src/replica.js';
import { compactiblePeritext } from '../src/compact-peritext.js';

test('trusted generation requires an explicit unique slot', () => {
  const raw = new DistributedReplica(compactiblePeritext, 'raw');
  assert.throws(() => raw.generate({ type: 'ins', el: 'x', anchorId: null }), /unique persistent mint slot/);
});

test('distinct slots mint distinct ids and causal fetch advances the clock', () => {
  const a = new DistributedReplica(compactiblePeritext, 'A', { mint: { slot: 11 } });
  const b = new DistributedReplica(compactiblePeritext, 'B', { mint: { slot: 22 } });
  const x = a.commitGenerated({ type: 'ins', el: 'x', anchorId: null }).payload;
  const y = b.commitGenerated({ type: 'ins', el: 'y', anchorId: null }).payload;
  assert.notEqual(x.id, y.id);
  b.ingest(a.delta(b.ancestryGids()));
  b.mergeWithGid(a.headGid);
  const z = b.generate({ type: 'ins', el: 'z', anchorId: x.id });
  assert.ok(z.id > x.id);
  assert.ok(z.id > y.id);
});

test('every generated operation has clock evidence, including delete', () => {
  const r = new DistributedReplica(compactiblePeritext, 'A', { mint: { slot: 7 } });
  const ins = r.commitGenerated({ type: 'ins', el: 'x', anchorId: null }).payload;
  const del = r.commitGenerated({ type: 'del', id: ins.id }).payload;
  const mark = r.generate({ type: 'addMark', mtype: 'bold', startId: ins.id, endId: ins.id });
  assert.ok(del.time > ins.id);
  assert.equal(mark.mid, mark.ts);
  assert.ok(mark.mid > del.time);
});
