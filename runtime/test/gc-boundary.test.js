import test from 'node:test';
import assert from 'node:assert/strict';
import { DistributedReplica } from '../src/replica.js';
import { compactiblePeritext } from '../src/compact-peritext.js';
import { encodeWire, decodeWire } from '../src/wire.js';

const text = (r) => r.read().map((e) => e.char).join('');

function collectedSource() {
  const a = new DistributedReplica(compactiblePeritext, 'A');
  a.commit({ type: 'ins', id: 1, el: 'a', anchorId: null });
  a.commit({ type: 'ins', id: 2, el: 'b', anchorId: 1 });
  const g = a.gc([a.head.id]);
  assert.ok(g.dropped > 0);
  return a;
}

test('certified GC boundary bootstraps a fresh replica and supports continuation', () => {
  const a = collectedSource();
  const b = new DistributedReplica(compactiblePeritext, 'B');
  const wire = decodeWire(encodeWire({ t: 'delta', c: a.delta(b.ancestryGids()) })).c;
  assert.equal(wire[0].kind, 'base');
  b.ingest(wire);
  b.mergeWithGid(a.headGid);
  assert.equal(text(b), 'ab');

  a.commit({ type: 'ins', id: 3, el: 'c', anchorId: 2 });
  b.ingest(a.delta(b.ancestryGids()));
  b.mergeWithGid(a.headGid);
  assert.equal(text(b), 'abc');
  assert.equal(b.headGid, a.headGid);
});

test('GC boundary rejects corrupted materialization and certificate', () => {
  const a = collectedSource();
  const b = new DistributedReplica(compactiblePeritext, 'B');
  const base = a.delta(b.ancestryGids())[0];
  assert.equal(base.kind, 'base');

  const badFingerprint = { ...base, fp: base.fp + 'damage' };
  assert.throws(() => b.ingest([badFingerprint]), /fingerprint mismatch/i);

  const badCertificate = { ...base, proof: base.proof + 'damage' };
  assert.throws(() => b.ingest([badCertificate]), /certificate mismatch/i);
});
