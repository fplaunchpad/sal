/**
 * Verifies the exported production library before and after every run.
 *
 * Level 1 (always): NOTION_PRODUCTION_LIBRARY resolves outside the
 * repository, and every file of the export has the SHA-256 pinned in this
 * directory's sources.json. The pinned digests include the export's own
 * asset manifest (sources.json), so the manifest of public asset URLs and
 * digests cannot change unnoticed.
 *
 * Level 2 (when NOTION_PRODUCTION_CACHE names the downloaded asset cache):
 * every asset listed in the export's manifest has the recorded length and
 * SHA-256, and every module body in the export's modules.json is exactly the
 * source slice of its asset at the recorded offsets. This ties the code that
 * runs to the public bytes, not only to an earlier export.
 *
 * Uses no network access.
 */
import { createHash } from 'node:crypto';
import { readFileSync, realpathSync, readdirSync } from 'node:fs';
import { dirname, join, resolve, sep } from 'node:path';
import { fileURLToPath } from 'node:url';
import { libraryPath } from './library.js';

const here = dirname(fileURLToPath(import.meta.url));
const repository = realpathSync(resolve(here, '../../..'));
const sha256 = (bytes) => createHash('sha256').update(bytes).digest('hex');

/** Throws an Error listing every mismatch; returns a summary when all agree. */
export function verifySources() {
  const pins = JSON.parse(readFileSync(join(here, 'sources.json'), 'utf8'));
  const problems = [];
  const dir = realpathSync(libraryPath());
  if (dir === repository || dir.startsWith(repository + sep)) problems.push(`the export ${dir} lies inside the repository ${repository}`);
  const present = readdirSync(dir).sort();
  const pinned = Object.keys(pins.exportFiles).sort();
  if (JSON.stringify(present) !== JSON.stringify(pinned)) problems.push(`export files ${present.join(',')} != ${pinned.join(',')}`);
  for (const [file, expected] of Object.entries(pins.exportFiles)) {
    const actual = sha256(readFileSync(join(dir, file)));
    if (actual !== expected) problems.push(`sha256 ${file} = ${actual} != ${expected}`);
  }
  const manifest = JSON.parse(readFileSync(join(dir, 'sources.json'), 'utf8'));
  const { modules, roots } = JSON.parse(readFileSync(join(dir, 'modules.json'), 'utf8'));
  if (Object.keys(modules).length !== pins.modules) problems.push(`${Object.keys(modules).length} modules != ${pins.modules}`);
  if (manifest.assets.length !== pins.assets) problems.push(`${manifest.assets.length} assets != ${pins.assets}`);
  for (const id of [...Object.values(pins.textModules), ...Object.values(roots)]) if (!modules[id]) problems.push(`module ${id} missing`);
  let level = 1;
  const cache = process.env.NOTION_PRODUCTION_CACHE;
  if (cache) {
    level = 2;
    let bytes = 0;
    const text = new Map();
    for (const asset of manifest.assets) {
      const data = readFileSync(join(cache, asset.file));
      bytes += data.length;
      if (data.length !== asset.bytes || sha256(data) !== asset.sha256) problems.push(`asset ${asset.file} differs from the manifest`);
      text.set(asset.file, data.toString('utf8'));
    }
    if (bytes !== pins.assetBytes) problems.push(`asset bytes ${bytes} != ${pins.assetBytes}`);
    for (const [id, m] of Object.entries(modules)) {
      const source = text.get(m.file);
      if (source === undefined || source.slice(m.start, m.end) !== m.source) problems.push(`module ${id} is not the slice ${m.file}:${m.start}-${m.end}`);
    }
  }
  if (problems.length) throw new Error(`source verification failed:\n  ${problems.slice(0, 20).join('\n  ')}`);
  return { level, directory: dir, modules: Object.keys(modules).length, assets: manifest.assets.length, recordedAt: manifest.recordedAt };
}

/** One-line description of a verification summary. */
export const describeVerification = (v) =>
  `export verified (level ${v.level}: ${v.level === 2 ? 'pinned export digests, asset digests and all module slices' : 'pinned export digests'}), ${v.modules} modules from ${v.assets} assets recorded ${v.recordedAt}`;

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) console.log(describeVerification(verifySources()));
