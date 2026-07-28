// GROUP-OP COMMIT (commitBatch): a gesture's op list sealed as ONE commit,
// applied via applyBatch (proven == folding apply). The commit's payload is the
// op ARRAY; the content-id folds it in opaquely, so delta ships it verbatim and
// ingest replays it via applyBatch with no wire/hash change. These pin: batch
// read == folded read but as ONE commit; the wire round-trip passes the
// content-address gate with an identical SHA head; convergence with mixed
// batch/single commits; peritext (ins + marks) batches; and the certified GC cut
// still collects a batch commit's ids.
//
// Each PASS carries a FAIL companion (empty/degenerate read, batch silently
// becoming N commits, marks lost, the cut dropping array-payload ids).

import test from 'node:test';
import assert from 'node:assert/strict';
import { DistributedReplica, syncReplicas } from '../src/replica.js';
import { compactibleEmbedRGA } from '../src/compact.js';
import { peritext } from '../src/datatypes/peritext.js';
import { insertIds } from '../src/frontier.js';
import { peritextCutFromMeet } from '../src/compact-peritext.js';

const ins = (id, el, anchorId) => ({ type: 'ins', id, el, anchorId });
const addMark = (mid, mtype, startId, endId) =>
  ({ type: 'addMark', mid, mtype, startId, endId, startSide: 'before', endSide: 'after' });
const txt = (r) => r.read().join('');

test('commitBatch == folding commit, but as ONE commit', () => {
  const ops = [ins(1, 'a', null), ins(2, 'b', 1), ins(3, 'c', 2)];
  const folded = new DistributedReplica(compactibleEmbedRGA, 'A');
  ops.forEach((o) => folded.commit(o));
  const batched = new DistributedReplica(compactibleEmbedRGA, 'B');
  batched.commitBatch(ops);

  assert.equal(txt(batched), 'abc');
  assert.equal(txt(batched), txt(folded), 'batched read == folded read');
  assert.equal(folded.dag.size, 4, 'fold: root + 3 op commits');
  assert.equal(batched.dag.size, 2, 'batch: root + 1 group-op commit');
  // FAIL companions: not empty, and the batch did NOT expand into 3 commits.
  assert.notEqual(txt(batched), '');
  assert.notEqual(batched.dag.size, folded.dag.size);
});

test('a batch commit round-trips the wire: content-address gate holds, same SHA head', () => {
  const A = new DistributedReplica(compactibleEmbedRGA, 'A');
  A.commitBatch([ins(1, 'a', null), ins(2, 'b', 1), ins(3, 'c', 2)]);
  const B = new DistributedReplica(compactibleEmbedRGA, 'B');

  assert.doesNotThrow(() => B.ingest(A.delta(B.ancestryGids())),
    'the array payload recomputes to the same content id (no mismatch)');
  B.mergeWithGid(A.headGid);
  assert.equal(txt(B), 'abc');
  assert.equal(B.headGid, A.headGid, 'identical SHA head for the batch commit on both replicas');
  // FAIL companion: not the empty degenerate.
  assert.notEqual(txt(B), '');
});

test('convergence with mixed batch and single commits, two authors', () => {
  const A = new DistributedReplica(compactibleEmbedRGA, 'A');
  const B = new DistributedReplica(compactibleEmbedRGA, 'B');
  A.commitBatch([ins(1, 'H', null), ins(2, 'i', 1)]); // "Hi" as one batch
  B.commit(ins(3, '!', null));                         // a single op
  syncReplicas(A, B);

  assert.equal(txt(A), txt(B), 'converged to one document');
  assert.equal(A.headGid, B.headGid, 'same SHA head after sync');
  // FAIL companion: every author's contribution survived (not one side dropped).
  const s = txt(A);
  assert.ok(s.includes('H') && s.includes('i') && s.includes('!'), `all chars present: ${s}`);
});

test('peritext batch (ins + addMark) applies and round-trips over the wire', () => {
  const A = new DistributedReplica(peritext, 'A');
  A.commitBatch([ins(1, 'a', null), ins(2, 'b', 1), addMark(3, 'bold', 1, 2)]);
  const ra = A.read();
  assert.equal(ra.map((e) => e.char).join(''), 'ab');
  assert.ok(ra.every((e) => e.marks.some((m) => m.mtype === 'bold')), 'both chars bold from the batch');

  const B = new DistributedReplica(peritext, 'B');
  B.ingest(A.delta(B.ancestryGids()));
  B.mergeWithGid(A.headGid);
  const rb = B.read();
  assert.equal(rb.map((e) => e.char).join(''), 'ab');
  assert.equal(B.headGid, A.headGid, 'same SHA head');
  assert.ok(rb.every((e) => e.marks.some((m) => m.mtype === 'bold')), 'marks survive the round-trip');
  // FAIL companion: not the plain (unmarked) degenerate.
  assert.ok(!rb.every((e) => e.marks.length === 0));
});

test('the certified GC cut collects a batch commit\'s ids (frontier + peritext)', () => {
  const A = new DistributedReplica(compactibleEmbedRGA, 'A');
  A.commitBatch([ins(1, 'a', null), ins(2, 'b', 1)]);
  const ids = insertIds(A.stableCut().meet);
  assert.ok(ids.has(1) && ids.has(2), 'batch ins ids are in the settled text cut');
  assert.notEqual(ids.size, 0); // FAIL companion: the array-payload bug dropped them to 0

  const P = new DistributedReplica(peritext, 'A');
  P.commitBatch([ins(10, 'a', null), ins(11, 'b', 10), addMark(12, 'bold', 10, 11)]);
  const cut = peritextCutFromMeet(P.stableCut().meet);
  assert.ok(cut.settledIds.has(10) && cut.settledIds.has(11), 'batch ins ids in the peritext cut');
  assert.ok(cut.settledMarkMids.has(12), 'batch mark mid in the peritext cut');
  assert.notEqual(cut.settledIds.size, 0);
});
