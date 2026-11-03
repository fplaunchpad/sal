#!/usr/bin/env node
/**
 * Downloads the pinned demo modules into `<sources>/cache`, checks every
 * SHA-256 against experiments/notion-oracle/sources.json, and writes each
 * variant of design-patch/patch.py to `<sources>/variants/<name>`.
 *
 *   node ra-pbt/instances/notion/prepare.js [--offline]
 *
 * With --offline the cache must already hold the pinned modules.
 */
import { execFileSync } from 'node:child_process';
import { mkdirSync, readFileSync, existsSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { join } from 'node:path';
import { MANIFEST, PATCHER, VARIANTS, sourcesDir, variantDir, variantHashes, verifyCache } from './sources.js';

const offline = process.argv.includes('--offline');
const cache = join(sourcesDir(), 'cache');
mkdirSync(cache, { recursive: true });
const manifest = JSON.parse(readFileSync(MANIFEST, 'utf8'));
for (const m of manifest.modules) {
  const path = join(cache, m.file);
  const ok = existsSync(path) && createHash('sha256').update(readFileSync(path)).digest('hex') === m.sha256;
  if (!ok) {
    if (offline) throw new Error(`cache lacks the pinned ${m.file}`);
    execFileSync('curl', ['-fsSL', m.url, '-o', path]);
  }
}
verifyCache();
for (const v of VARIANTS) execFileSync('python3', [PATCHER, '--cache', cache, '--emit', variantDir(v), '--variant', v], { stdio: 'inherit' });
console.log(JSON.stringify({ sources: sourcesDir(), observed: manifest.observed, variants: Object.fromEntries(VARIANTS.map((v) => [v, variantHashes(v)])) }, null, 1));
