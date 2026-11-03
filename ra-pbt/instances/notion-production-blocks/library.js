/**
 * Loads the exported production library from $NOTION_PRODUCTION_LIBRARY
 * after verifying it (verify-sources.js). `withVerifiedLibrary(run)` checks
 * the digests before and after `run`, so every result is bracketed by two
 * successful verifications.
 */
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { verifySources } from './verify-sources.js';

let cached = null;

/** { createClient, RequestBuilder, provenance, directory, manifest } */
export async function loadLibrary() {
  if (cached) return cached;
  const { manifest, directory } = verifySources();
  const lib = await import(pathToFileURL(join(directory, 'index.mjs')).href);
  cached = { createClient: lib.createClient, RequestBuilder: lib.RequestBuilder, provenance: lib.provenance, directory, manifest };
  return cached;
}

/** Verifies, loads, runs `run(lib)`, verifies again; returns run's result. */
export async function withVerifiedLibrary(run) {
  const lib = await loadLibrary();
  const result = await run(lib);
  verifySources(lib.directory);
  return result;
}
