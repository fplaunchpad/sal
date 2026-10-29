/**
 * Checks that the installed loro-crdt matches the pinned manifest in
 * sources.json: the version in package.json, the lockfile's resolved URL and
 * integrity, and SHA-256 digests of the files the instance executes (the
 * Node entry point, the wasm-bindgen glue and the wasm binary). The manifest
 * also names the source tag and commit the release was built from. Uses no
 * network access.
 */
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));

const sha256 = (path) => createHash('sha256').update(readFileSync(path)).digest('hex');

/** Throws an Error listing every mismatch; returns the manifest when all agree. */
export function verifySources() {
  const manifest = JSON.parse(readFileSync(join(here, 'sources.json'), 'utf8'));
  const problems = [];
  const pkg = JSON.parse(readFileSync(join(here, 'node_modules', manifest.package, 'package.json'), 'utf8'));
  if (pkg.version !== manifest.version) problems.push(`installed version ${pkg.version} != ${manifest.version}`);
  const lock = JSON.parse(readFileSync(join(here, 'package-lock.json'), 'utf8'));
  const entry = lock.packages?.[`node_modules/${manifest.package}`];
  if (!entry) problems.push('package-lock.json has no entry for the package');
  else {
    if (entry.version !== manifest.version) problems.push(`lockfile version ${entry.version} != ${manifest.version}`);
    if (entry.resolved !== manifest.resolved) problems.push(`lockfile resolved ${entry.resolved} != ${manifest.resolved}`);
    if (entry.integrity !== manifest.integrity) problems.push('lockfile integrity differs');
  }
  for (const [rel, expected] of Object.entries(manifest.sha256)) {
    const actual = sha256(join(here, rel));
    if (actual !== expected) problems.push(`sha256 ${rel} = ${actual} != ${expected}`);
  }
  if (problems.length) throw new Error(`source verification failed:\n  ${problems.join('\n  ')}`);
  return manifest;
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  const m = verifySources();
  console.log(`sources verified: ${m.package}@${m.version}, ${Object.keys(m.sha256).length} file digests match`);
}
