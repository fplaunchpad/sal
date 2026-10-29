import test from 'node:test';
import assert from 'node:assert/strict';
import { rcNonComm } from '../src/laws.js';
import { lawReportRow, lawReportCounts, lawReportExitCode } from '../../experiments/notion-ra-pbt/lib.mjs';

test('Notion law reports retain unresolved checks and return a distinct exit status', () => {
  // The sampled effects agree, but no exact semantic oracle certifies them.
  const datatype = { init: () => 0, apply: (s) => s, merge3: () => 0, read: (s) => s };
  const instance = { replicas: 1, syncProbability: 0, genEvent: (_r, _s, ctx) => ctx.fresh() };
  const result = rcNonComm(datatype, instance, { trials: 1, maxSize: 2 });
  assert.deepEqual(result.failures, []);
  const report = lawReportRow(result);
  assert.equal(report.verdict, 'inconclusive');
  assert.equal(report.pass, false);
  assert.equal(report.runs, 0);
  assert.equal(report.inconclusive, 1);
  assert.equal(report.inconclusiveExamples[0].kind, 'commutation-unresolved');
  assert.deepEqual(lawReportCounts([report]), {
    pass: 0, fail: 0, inconclusive: 1, vacuous: 0, 'not-applicable': 0,
  });
  assert.equal(lawReportExitCode([report]), 2);
  assert.notEqual(lawReportExitCode([report]), 0);
  // A real failure still dominates unresolved checks; skipped checks alone
  // cannot produce a checked pass, while an inapplicable law is harmless.
  assert.equal(lawReportExitCode([report, { verdict: 'fail' }]), 1);
  assert.equal(lawReportExitCode([{ verdict: 'vacuous' }]), 2);
  assert.equal(lawReportExitCode([{ verdict: 'not-applicable' }]), 2);
  assert.equal(lawReportExitCode([{ verdict: 'pass' }, { verdict: 'not-applicable' }]), 0);
});
