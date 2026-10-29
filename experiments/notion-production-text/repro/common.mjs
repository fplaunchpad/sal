// Shared helpers for the reproductions. Imports nothing but the exported
// library, named by NOTION_PRODUCTION_LIBRARY (outside the repository).
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';

const dir = process.env.NOTION_PRODUCTION_LIBRARY;
if (!dir) throw new Error('set NOTION_PRODUCTION_LIBRARY to the directory written by extract.mjs');
export const { createClient } = await import(pathToFileURL(join(dir, 'index.mjs')).href);

export const block = { table: 'block', id: '00000000-0000-4000-8000-0000000000b1', spaceId: '00000000-0000-4000-8000-000000000100' };

/** A replica that created the block itself. */
export function created(session) {
  const c = createClient(session);
  c.createBlock(block);
  return c;
}

/** Issues a prepared batch on its own replica and returns it for delivery elsewhere. */
export function issue(client, ops) {
  client.apply(ops);
  return ops;
}

/** The block as text with '*' after every bold character. */
export function show(client) {
  return client.rich(block).map(([text, marks]) => [...text].map((ch) => ch + ((marks ?? []).some((m) => m[0] === 'b') ? '*' : '')).join('')).join('');
}

let failures = 0;
/** Prints one expectation; counts a mismatch. */
export function expect(label, actual, expected) {
  const ok = actual === expected;
  if (!ok) failures++;
  console.log(`${ok ? 'ok  ' : 'FAIL'} ${label}: ${actual}${ok ? '' : ` (expected ${expected})`}`);
}
export const done = () => {
  process.exitCode = failures ? 1 : 0;
};
