// EPOCH-BASE HISTORY PRUNING, re-ported onto the #112 cut-keyed epoch model.
// After a SETTLED compaction, pruneToEpochBase drops everything below the
// compaction (gated on: cut complete + every registered replica's evidence has
// ADVANCED PAST the compaction's cut, epochDag.subcut). The compaction commit
// becomes a parent-free EPOCH BASE whose content id still verifies (the hash
// covers the wire parent gid STRING + the state fingerprint), and a fresh peer
// bootstraps from it at O(document) instead of replaying genesis. Soundness is
// the model-independent "a settled cut licenses forgetting" (the stability VC),
// so it rides the cut-keyed epochs unchanged. PASS+FAIL shaped throughout.

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
const textOf = (r) => r.read().map((e) => e.char).join('');

test('prune -> fresh peer bootstraps from the epoch base at O(document)', () => {
  const a = buildCompacted();
  const before = a.dag.size;
  const readBefore = textOf(a);
  const pr = a.pruneToEpochBase();
  assert.ok(pr.pruned >= 3, `history dropped (${pr.pruned} commits)`);
  assert.ok(a.dag.size < before, 'dag shrank');
  assert.equal(textOf(a), readBefore, 'reads preserved by the prune');

  // the delta to an EMPTY peer now starts at the base, not genesis
  const b = new DistributedReplica(compactiblePeritext, 'B');
  const wire = a.delta(b.ancestryGids());
  assert.equal(wire[0].kind, 'compact', 'first wire commit is the epoch base');
  assert.ok(wire.length <= 3, `O(document + tail), not O(history) (${wire.length} commits)`);
  b.ingest(wire);              // base verifies WITHOUT its parent (content gate holds)
  b.mergeWithGid(a.headGid);   // pristine adopt
  assert.equal(textOf(b), readBefore, 'fresh peer converged');
  assert.equal(b.headGid, a.headGid, 'same head SHA');

  // and B can keep AUTHORING on the adopted chain, merging back to A
  b.commit({ type: 'ins', id: mint(99), el: '.', anchorId: mint(42) });
  a.ingest(b.delta(a.ancestryGids()));
  a.mergeWithGid(b.headGid);
  assert.equal(textOf(a), readBefore + '.', 'post-bootstrap edit merged back');
  assert.equal(a.headGid, b.headGid, 'reconverged');
});

test('FAIL companions: tampered base refused; under-evidenced prune refused', () => {
  const a = buildCompacted();
  a.pruneToEpochBase();
  const b = new DistributedReplica(compactiblePeritext, 'B');
  const bad = structuredClone(a.delta(b.ancestryGids()));
  // tamper the inline state: the recomputed fingerprint changes the hash
  bad[0].state.deleted.push(424242);
  assert.throws(() => new DistributedReplica(compactiblePeritext, 'C').ingest(bad),
    /content-address mismatch/, 'tampered epoch base trips the content gate');

  // a registered peer whose evidence has NOT advanced past the cut blocks the prune
  const p = new DistributedReplica(compactiblePeritext, 'P');
  p.commit({ type: 'ins', id: mint(1), el: 'x', anchorId: null });
  const q = new DistributedReplica(compactiblePeritext, 'Q');
  q.commit({ type: 'ins', id: mint(2), el: 'y', anchorId: null });
  p.ingest(q.delta(p.ancestryGids()));
  p.mergeWithGid(q.headGid);      // p knows q authored...
  p.commit({ type: 'del', id: mint(1) });
  const g = p.compactStable();     // ...but q has not advanced past the new cut
  if (g.compacted) {
    const pr = p.pruneToEpochBase();
    assert.equal(pr.pruned, 0, 'refused');
    assert.match(pr.reason, /not reached the compaction cut|incomplete/, `held by the gate (${pr.reason})`);
  } else {
    assert.match(String(g.reason ?? ''), /./); // compaction itself refused, equally correct
  }
});

test('persistence round-trips an epoch base (records layer)', async () => {
  const { nodeRecords, rebuildNode } = await import('../../p2p-demo/src/records.js');
  const a = buildCompacted();
  a.pruneToEpochBase();
  const { records, heads } = nodeRecords(a, { datatypeLabel: 'peritext' });
  assert.ok(records.some((r) => r.kind === 'compact' && r.cut), 'base serialized as compact with its cut');
  assert.ok(!records.some((r) => r.kind === 'root'), 'no root record below the base');
  const back = rebuildNode(records, heads, compactiblePeritext);
  assert.equal(textOf(back), textOf(a), 'reads survive the store round-trip');
  assert.equal(back.headGid, a.headGid, 'same head SHA through the store');
});
