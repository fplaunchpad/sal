// EPOCH-BASE BOOTSTRAP + HISTORY PRUNING: the answer to "why keep full
// history?" -- you don't. After a certified compaction, pruneToEpochBase
// drops everything below the compact commit (gated on the theorem's
// condition: cut complete + every registered replica's evidence at the
// epoch), the compact commit becomes a parent-free EPOCH BASE whose content
// id still verifies (hash({compact, p, fp}): p is the wire parent STRING,
// fp recomputes from the inline state), and a fresh peer bootstraps from it
// at O(document) instead of replaying genesis. PASS+FAIL shaped throughout.

import test from 'node:test';
import assert from 'node:assert/strict';
import { compactiblePeritext } from '../src/compact-peritext.js';
import { DistributedReplica } from '../src/replica.js';

const mint = (k) => k * 1000 + 7;
function buildCompacted(n = 40) {
  const r = new DistributedReplica(compactiblePeritext, 'A');
  const ops = [];
  for (let i = 1; i <= n; i++) {
    ops.push({ type: 'ins', id: mint(i), el: 'abcdefghij'[i % 10], anchorId: i === 1 ? null : mint(i - 1) });
  }
  for (let d = 3; d <= 15; d += 3) ops.push({ type: 'del', id: mint(d) });
  r.commitBatch(ops);
  r.commit({ type: 'ins', id: mint(n + 1), el: '!', anchorId: mint(n) });
  const g = r.compactStable(); // solo: the cut is trivially complete
  assert.equal(g.compacted, true, 'fixture compacted');
  r.commit({ type: 'ins', id: mint(n + 2), el: '?', anchorId: mint(n + 1) }); // post-epoch tail
  return r;
}

test('prune -> fresh peer bootstraps from the epoch base at O(document)', () => {
  const a = buildCompacted();
  const before = a.dag.size;
  const readBefore = a.read().map((e) => e.char).join('');
  const pr = a.pruneToEpochBase();
  assert.ok(pr.pruned >= 3, `history dropped (${pr.pruned} commits)`);
  assert.ok(a.dag.size < before, 'dag shrank');
  assert.equal(a.read().map((e) => e.char).join(''), readBefore, 'reads preserved');

  // the delta to an EMPTY peer now starts at the base, not genesis
  const b = new DistributedReplica(compactiblePeritext, 'B');
  const wire = a.delta(b.ancestryGids());
  assert.equal(wire[0].kind, 'compact', 'first wire commit is the epoch base');
  assert.ok(wire.length <= 3, `O(document + tail), not O(history) (${wire.length} commits)`);
  b.ingest(wire); // base verifies WITHOUT its parent (content gate holds)
  b.mergeWithGid(a.headGid); // pristine adopt
  assert.equal(b.read().map((e) => e.char).join(''), readBefore, 'fresh peer converged');
  assert.equal(b.headGid, a.headGid, 'same head SHA');

  // and B can keep AUTHORING on the adopted chain
  b.commit({ type: 'ins', id: mint(99), el: '.', anchorId: mint(42) });
  a.ingest(b.delta(a.ancestryGids()));
  a.mergeWithGid(b.headGid);
  assert.equal(a.read().map((e) => e.char).join(''), readBefore + '.', 'post-bootstrap edit merged back');
});

test('FAIL companions: tampered base refused; unsettled prune refused', () => {
  const a = buildCompacted();
  a.pruneToEpochBase();
  const b = new DistributedReplica(compactiblePeritext, 'B');
  const wire = a.delta(b.ancestryGids());
  // tamper the inline state: the recomputed fingerprint changes the hash
  const bad = structuredClone(wire);
  bad[0].state.deleted.push(424242);
  assert.throws(() => new DistributedReplica(compactiblePeritext, 'C').ingest(bad),
    /content-address mismatch/, 'tampered epoch base trips the gate');

  // a peer whose evidence is BELOW the epoch blocks pruning
  const p = new DistributedReplica(compactiblePeritext, 'P');
  p.commit({ type: 'ins', id: mint(1), el: 'x', anchorId: null });
  const q = new DistributedReplica(compactiblePeritext, 'Q');
  q.commit({ type: 'ins', id: mint(2), el: 'y', anchorId: null });
  p.ingest(q.delta(p.ancestryGids()));
  p.mergeWithGid(q.headGid);      // p knows q authored...
  p.commit({ type: 'del', id: mint(1) });
  const g = p.compactStable();     // ...but q has no evidence AT the new epoch
  if (g.compacted) {
    const pr = p.pruneToEpochBase();
    assert.equal(pr.pruned, 0, 'refused');
    assert.match(pr.reason, /below epoch|incomplete/, `held by the gate (${pr.reason})`);
  } else {
    // compaction itself already refused for the same reason: equally correct
    assert.match(String(g.reason ?? ''), /./);
  }
});

test('persistence round-trips an epoch base (records layer)', async () => {
  const { nodeRecords, rebuildNode } = await import('../../p2p-demo/src/records.js');
  const a = buildCompacted();
  a.pruneToEpochBase();
  const { records, heads } = nodeRecords(a, { datatypeLabel: 'peritext' });
  assert.ok(records.some((r) => r.kind === 'compact'), 'base serialized as compact');
  assert.ok(!records.some((r) => r.kind === 'root'), 'no root record below the base');
  const back = rebuildNode(records, heads, compactiblePeritext);
  assert.equal(back.read().map((e) => e.char).join(''), a.read().map((e) => e.char).join(''));
  assert.equal(back.headGid, a.headGid, 'same head SHA through the store');
});
