import assert from 'node:assert/strict';
import { existsSync, readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import test from 'node:test';

const runtimeRoot = fileURLToPath(new URL('..', import.meta.url));
const repoRoot = fileURLToPath(new URL('../..', import.meta.url));
const manifest = JSON.parse(readFileSync(
  new URL('../evidence-manifest.json', import.meta.url), 'utf8'));
const ledger = readFileSync(
  new URL('../../Sal/MRDTs/Metatheory/ProductionLedger.lean', import.meta.url),
  'utf8');

test('every released runtime datatype names an exact VerifiedMRDT package', () => {
  const required = new Set(['rga', 'embed-rga', 'sided-embed-rga', 'or-set', 'peritext']);
  assert.deepEqual(new Set(manifest.production.map((entry) => entry.id)), required);

  for (const entry of manifest.production) {
    assert.equal(entry.correspondenceStatus, 'differential-tested');
    assert.match(entry.verifiedMRDT, /^Sal\.MRDTs\.Instances\./);
    assert.ok(entry.exports.length > 0);
    assert.ok(existsSync(`${runtimeRoot}/${entry.source}`), entry.source);

    const shortName = entry.verifiedMRDT.replace('Sal.MRDTs.', '');
    assert.ok(ledger.includes(shortName),
      `${entry.id} certificate is absent from the typed production ledger`);
  }
});

test('every comparison-only runtime datatype is explicitly excluded', () => {
  for (const entry of manifest.comparisonOnly) {
    assert.ok(entry.reason.length >= 20, `${entry.id} needs a concrete exclusion reason`);
    assert.ok(existsSync(`${runtimeRoot}/${entry.source}`), entry.source);
  }
  assert.ok(existsSync(`${repoRoot}/Sal/MRDTs/Metatheory/NegativeLedger.lean`));
});
