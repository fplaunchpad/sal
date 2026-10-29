/**
 * The exported production library, loaded from the directory named by the
 * environment variable NOTION_PRODUCTION_LIBRARY. The export is proprietary
 * code and is never stored in the repository; `verify-sources.js` refuses a
 * directory inside it.
 */
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';

export function libraryPath() {
  const dir = process.env.NOTION_PRODUCTION_LIBRARY;
  if (!dir) throw new Error('NOTION_PRODUCTION_LIBRARY must name the directory written by experiments/notion-production-client/extract.mjs');
  return dir;
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
