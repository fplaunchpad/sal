/**
 * Checks the exported production Notion library (`vendor/notion-production/`
 * at the repository root, or $NOTION_PRODUCTION_LIBRARY) against library.json: the SHA-256 and length of every exported file, the
 * module count, and the digests of the source slices of the modules this
 * instance's findings name (split/merge request builders 701590, record
 * operations 971340, slice tree 300957, text slice 458789, slice lookup by
 * label 121141, label subdivision 663360, list commands 929891 and list
 * placement 75332). The export is Notion's code, outside this repository's
 * licence (see the notice in that directory). Uses no network access.
 */
import { createHash } from 'node:crypto';
import { readFileSync, realpathSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));

const sha256 = (bytes) => createHash('sha256').update(bytes).digest('hex');

/** The library directory: the environment variable, else the vendored export. */
export function libraryDirectory() {
  return realpathSync(process.env.NOTION_PRODUCTION_LIBRARY || resolve(here, '../../../vendor/notion-production'));
}

/** Throws an Error listing every mismatch; returns { manifest, directory } when all agree. */
export function verifySources(directory = libraryDirectory()) {
  const manifest = JSON.parse(readFileSync(join(here, 'library.json'), 'utf8'));
  const problems = [];
  for (const [name, pin] of Object.entries(manifest.files)) {
    let bytes;
    try {
      bytes = readFileSync(join(directory, name));
    } catch (e) {
      problems.push(`${name}: ${e.message}`);
      continue;
    }
    if (bytes.length !== pin.bytes) problems.push(`${name}: ${bytes.length} bytes, pinned ${pin.bytes}`);
    const digest = sha256(bytes);
    if (digest !== pin.sha256) problems.push(`${name}: sha256 ${digest}, pinned ${pin.sha256}`);
  }
  if (!problems.length) {
    const { modules } = JSON.parse(readFileSync(join(directory, 'modules.json'), 'utf8'));
    if (Object.keys(modules).length !== manifest.moduleCount) problems.push(`module count ${Object.keys(modules).length}, pinned ${manifest.moduleCount}`);
    for (const [id, pin] of Object.entries(manifest.modules)) {
      const m = modules[id];
      if (!m) problems.push(`module ${id} missing`);
      else if (sha256(m.source) !== pin.sha256 || m.file !== pin.file || m.start !== pin.start) problems.push(`module ${id} differs from its pin`);
    }
  }
  if (problems.length) throw new Error(`production library verification failed:\n  ${problems.join('\n  ')}`);
  return { manifest, directory };
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  const { manifest, directory } = verifySources();
  console.log(`production library verified at ${directory}: ${Object.keys(manifest.files).length} file digests and ${Object.keys(manifest.modules).length} module digests match (${manifest.moduleCount} modules, ${manifest.assets} pinned assets)`);
}
