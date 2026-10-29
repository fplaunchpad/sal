/**
 * The exported production library: `vendor/notion-production/` at the
 * repository root, or the directory named by the environment variable
 * NOTION_PRODUCTION_LIBRARY. The export is Notion's code, outside this
 * repository's licence (see the notice in that directory); `verify-sources.js`
 * checks its digests before and after every run.
 */
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));

export function libraryPath() {
  return process.env.NOTION_PRODUCTION_LIBRARY || resolve(here, '../../../vendor/notion-production');
}

let loaded = null;

/** Loads the export once; later calls return the same module. */
export async function loadLibrary() {
  if (!loaded) loaded = await import(pathToFileURL(join(libraryPath(), 'index.mjs')).href);
  return loaded;
}

await loadLibrary();

/** The loaded export: { createClient, RequestBuilder, provenance }. */
export function library() {
  return loaded;
}
