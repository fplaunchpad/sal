import assert from 'node:assert/strict';
import { existsSync, readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import test from 'node:test';
import { readJSON, validateContracts } from '../../scripts/check-public-certificates.mjs';

const runtimeRoot = fileURLToPath(new URL('..', import.meta.url));
const repoRoot = fileURLToPath(new URL('../..', import.meta.url));
const manifest = JSON.parse(readFileSync(
  new URL('../evidence-manifest.json', import.meta.url), 'utf8'));
const contracts = readJSON('public-contracts.json');

test('every released runtime datatype names an exact VerifiedMRDT package', () => {
  const required = new Set(['rga', 'embed-rga', 'sided-embed-rga', 'peritext']);
  assert.deepEqual(new Set(manifest.production.map((entry) => entry.id)), required);
  validateContracts(contracts, manifest);

  for (const entry of manifest.production) {
    assert.equal(entry.correspondenceStatus, 'differential-tested');
    assert.match(entry.verifiedMRDT, /^Sal\.MRDTs\.Instances\./);
    assert.ok(entry.exports.length > 0);
    assert.ok(existsSync(`${runtimeRoot}/${entry.source}`), entry.source);

  }
});

test('every comparison-only runtime datatype is explicitly excluded', () => {
  for (const entry of manifest.comparisonOnly) {
    assert.ok(entry.reason.length >= 20, `${entry.id} needs a concrete exclusion reason`);
    assert.ok(existsSync(`${runtimeRoot}/${entry.source}`), entry.source);
  }
  assert.ok(existsSync(`${repoRoot}/Sal/MRDTs/Metatheory/NegativeLedger.lean`));
});
