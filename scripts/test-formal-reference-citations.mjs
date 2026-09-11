import test from 'node:test';
import assert from 'node:assert/strict';
import { citationSource, checkCoverage } from './check-formal-reference-citations.mjs';
import { runLean } from './check-public-certificates.mjs';

const anchor = (name) => `\\anchor{Sal/MRDTs/Instances/RGA.lean}{${name}}`;

test('citation gate resolves a real name and rejects a stale one', () => {
  const good = runLean(citationSource(anchor('RGA.applicable')).source);
  assert.equal(good.status, 0, good.stdout + good.stderr);
  const bad = runLean(citationSource(anchor('RGA.missingDeclarationForGateTest')).source);
  assert.notEqual(bad.status, 0);
  assert.match(bad.stdout, /missingDeclarationForGateTest/);
});

test('citation gate rejects missing paths and malformed labels', () => {
  assert.throws(() => citationSource('\\anchor{Sal/missing.lean}{RGA.applicable}'));
  assert.throws(() => citationSource(anchor('RGA.applicable; #check Nat')));
});

test('coverage gate rejects either stale count', () => {
  const manifest = { contracts: [{}, {}] };
  const good = 'production registry contains 2 \\lean{PackagedMRDT}; same 2-entry';
  checkCoverage(good, manifest);
  assert.throws(() => checkCoverage(good.replace('contains 2', 'contains 1'), manifest));
  assert.throws(() => checkCoverage(good.replace('same 2', 'same 1'), manifest));
});
