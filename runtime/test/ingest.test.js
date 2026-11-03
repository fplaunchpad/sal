// Binary runs reconstruct intermediate content ids. Repeated delivery must
// reuse their local nodes: duplicating a node makes a false fork and can revive
// an OR-set element that its issuer removed. Exercise both ingest implementations.
import test from 'node:test';
import assert from 'node:assert/strict';
import { DistributedReplica } from '../src/replica.js';
import { Peer } from '../src/sync.js';
import { orset } from '../src/datatypes/orset.js';
import { encodeWire, decodeWire } from '../src/wire.js';

const wire = (c) => decodeWire(encodeWire({ t: 'delta', c })).c;
const indexSnapshot = (replica) => ({
  size: replica.dag.size,
  gids: [...replica.gid],
  byGid: [...replica.byGid],
});

function assertReplayAddsNothing(replica, commits) {
  const before = indexSnapshot(replica);
  assert.equal(replica.ingest(commits), 0, 'duplicate delivery adds no commits');
  assert.deepEqual(indexSnapshot(replica), before, 'duplicate delivery preserves both content-id indices');
}

for (const Replica of [DistributedReplica, Peer]) {
  const make = (name) => new Replica(orset, name);

  test(`${Replica.name}: overlapping binary deltas preserve removal and commit identity`, () => {
    const a = make('A'), d = make('D');
    const have = d.ancestryGids();
    const add = a.commit({ type: 'add', tag: 1, el: 'a' });
    d.ingest(wire(a.delta(have)));
    d.mergeWithGid(a.headGid);
    const original = d.byGid.get(add), size = d.dag.size;

    a.commit({ type: 'rm', tags: [1] });
    // Both messages were computed against the same receiver summary, as when
    // they overlap in flight. The repeated add's id is implicit this time.
    const overlap = wire(a.delta(have));
    assert.equal(overlap[0].gid, null);
    assert.deepEqual(overlap[1].parents, [null]);
    assert.equal(d.ingest(overlap), 1, 'only the removal is new');
    assert.equal(d.byGid.get(add), original, 'the add keeps its original local node');
    assert.equal(d.dag.size, size + 1);
    d.mergeWithGid(a.headGid);
    assert.deepEqual(d.read(), []);
    assert.notDeepEqual(d.read(), ['a'], 'the removed element does not revive through a false fork');
    assert.equal(d.headGid, a.headGid, 'the receiver fast-forwards to the source');
    assertReplayAddsNothing(d, overlap);
  });

  test(`${Replica.name}: skipped implicit middle commits retain null parent references`, () => {
    const a = make('A'), d = make('D');
    a.commit({ type: 'add', tag: 1, el: 'a' });
    a.commit({ type: 'add', tag: 2, el: 'b' });
    a.commit({ type: 'add', tag: 3, el: 'c' });
    a.commit({ type: 'rm', tags: [1] });
    const history = a.delta(new Set());
    const prefix = history.slice(0, 2);
    d.ingest(wire(prefix));
    d.mergeWithGid(prefix.at(-1).gid);
    const before = indexSnapshot(d);

    const chain = wire(history);
    assert.deepEqual(chain.map((c) => c.gid === null), [true, true, true, false]);
    assert.ok(chain.slice(1).every((c) => c.parents[0] === null));
    assert.equal(d.ingest(chain), 2, 'the two known intermediate commits are skipped');
    assert.equal(d.dag.size, before.size + 2);
    for (const [gid, id] of before.byGid) assert.equal(d.byGid.get(gid), id);
    d.mergeWithGid(a.headGid);
    assert.deepEqual(d.read(), ['b', 'c']);
    assert.notDeepEqual(d.read(), ['a', 'b', 'c']);
    assertReplayAddsNothing(d, chain);

    // ingest also accepts a run whose ids are all implicit, including its last
    // commit. Here every parent after the first must use the reconstructed id.
    const implicit = chain.map((c) => ({ ...c, gid: null }));
    assertReplayAddsNothing(d, implicit);
    const e = make('E');
    assert.equal(e.ingest(implicit), 4);
    e.mergeWithGid(a.headGid);
    assert.deepEqual(e.read(), ['b', 'c']);
    assert.notDeepEqual(e.read(), []);
    assertReplayAddsNothing(e, implicit);
  });

  test(`${Replica.name}: overlap after a merge retains indices and endpoint validation`, () => {
    const a = make('A'), b = make('B'), d = make('D');
    a.commit({ type: 'add', tag: 1, el: 'a' });
    b.commit({ type: 'add', tag: 2, el: 'b' });
    a.ingest(wire(b.delta(a.ancestryGids())));
    a.mergeWithGid(b.headGid);
    const mergeGid = a.headGid;
    a.commit({ type: 'add', tag: 3, el: 'c' });
    d.ingest(wire(a.delta(new Set())));
    d.mergeWithGid(a.headGid);
    const before = indexSnapshot(d);

    a.commit({ type: 'rm', tags: [1] });
    const overlap = wire(a.delta(new Set()));
    const mergeIndex = overlap.findIndex((c) => c.gid === mergeGid);
    assert.ok(mergeIndex >= 0, 'the merge has an explicit content id');
    assert.equal(overlap[mergeIndex + 1].parents[0], mergeGid);
    assert.equal(overlap[mergeIndex + 1].gid, null, 'the authored child has an implicit id');
    assert.equal(d.ingest(overlap), 1);
    assert.equal(d.dag.size, before.size + 1);
    for (const [gid, id] of before.byGid) assert.equal(d.byGid.get(gid), id);
    d.mergeWithGid(a.headGid);
    assert.deepEqual(d.read(), ['b', 'c']);
    assert.notDeepEqual(d.read(), ['a', 'b', 'c']);
    assert.equal(d.headGid, a.headGid);
    assertReplayAddsNothing(d, overlap);

    const damaged = wire(a.delta(new Set()));
    damaged.at(-1).payload = { type: 'rm', tags: [2] };
    assert.throws(() => make('E').ingest(damaged), /content-address mismatch/,
      'a changed endpoint operation still fails its explicit content-id check');
  });
}
