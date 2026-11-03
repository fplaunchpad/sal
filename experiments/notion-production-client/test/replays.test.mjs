import assert from 'node:assert/strict';
import { test } from 'node:test';
import { extract } from '../extract.mjs';
import { replayCases } from '../replay.mjs';

const cache = process.env.NOTION_PRODUCTION_CACHE;
if (!cache) throw new Error('Set NOTION_PRODUCTION_CACHE');
const extracted = extract(cache);
const variants = [{}, { A: 'B', B: 'A', C: 'D', D: 'C' }];
const records = variants.flatMap(sessions => replayCases(extracted, sessions));

test('all five analogous schedules run under both session-ID tie-break orders', () => {
  assert.equal(records.length, 10);
  for (const id of ['N-001','N-002','N-003','N-004','N-005'])
    assert.equal(records.filter(r => r.id === id).length, 2);
  assert.equal(records.filter(r => r.status === 'trace-rejected').length, 0);
});

test('every observed local edit agrees with the independent positional contract', () => {
  let checked = 0;
  for (const r of records) for (const replica of r.replicas) for (const action of replica.actions) {
    if (action.localContract === undefined) continue;
    checked++;
    assert.equal(action.localContract, true, JSON.stringify({ id: r.id, session: replica.session, action }));
  }
  assert.ok(checked >= 50); // Reject empty or trivially unexercised schedules.
  assert.equal(records.filter(r => r.status === 'handler-contract-failure').length, 0);
});

test('formatting reaches a nonempty selection rather than passing vacuously', () => {
  for (const r of records.filter(r => ['N-002','N-003'].includes(r.id))) {
    const bold = r.replicas.flatMap(x => x.actions).filter(a => a.request?.kind === 'bold');
    assert.equal(bold.length, 1);
    assert.ok(bold[0].request.end > bold[0].request.start);
    assert.notDeepEqual(bold[0].expected, []);
  }
});

test('the split/merge schedules retain the seed characters on both replicas', () => {
  for (const r of records.filter(r => ['N-004','N-005'].includes(r.id))) {
    const expected = r.id === 'N-004' ? 'abc' : 'x';
    assert.deepEqual(r.actual, [expected, expected]);
    assert.notDeepEqual(r.actual, ['', '']);
  }
});

test('different intermediate layouts are explicit, rather than claimed as exact demo reproductions', () => {
  for (const r of records) {
    assert.equal(r.demoLayoutReached, false);
    assert.notDeepEqual(r.before.map(b => b.text), r.demoBefore);
    assert.equal(r.status, 'not-reproduced');
  }
});
