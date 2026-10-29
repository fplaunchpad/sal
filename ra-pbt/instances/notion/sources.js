/**
 * The executable Notion block-editor models.
 *
 * The models are the seven JavaScript modules of Notion's public CRDT demo,
 * pinned by SHA-256 in `experiments/notion-oracle/sources.json`, and patched
 * copies of them built by `experiments/notion-merge-design/design-patch/patch.py`.
 * Third-party source is not committed: `prepare.js` downloads the pinned
 * modules into a cache, checks every hash, and writes one directory per
 * variant. This module loads a variant from that directory.
 *
 *   demo           the unmodified pinned demo (the model the oracle,
 *                  correctness and network campaigns execute)
 *   anchor-absorb  the corrected block merge of the merge design gate: one
 *                  mergeBlock operation anchored at the target's last slice,
 *                  removal derived from attachment, the source tree attached
 *                  under the last node of the holder tree
 *
 * The other variants of patch.py load the same way; they are negative
 * controls of the corrected merge.
 *
 * The sources directory is `$NOTION_RA_PBT_SOURCES`, by default
 * `<os tmpdir>/notion-ra-pbt-sources`, laid out as `cache/` (the pinned
 * modules) and `variants/<name>/`.
 */
import { createHash } from 'node:crypto';
import { existsSync, readFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve, dirname } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
export const REPO = resolve(here, '../../..');
export const MANIFEST = join(REPO, 'experiments/notion-oracle/sources.json');
export const PATCHER = join(REPO, 'experiments/notion-merge-design/design-patch/patch.py');
export const VARIANTS = ['demo', 'anchor-absorb', 'design', 'slice-following', 'remove-independently'];
export const MODULES = ['replica.js', 'document.js', 'text-slice-tree.js', 'ids.js', 'rga.js', 'rich-text.js', 'search-labels.js'];

export const sourcesDir = () => process.env.NOTION_RA_PBT_SOURCES ?? join(tmpdir(), 'notion-ra-pbt-sources');
export const variantDir = (variant) => join(sourcesDir(), 'variants', variant);

const sha256 = (path) => createHash('sha256').update(readFileSync(path)).digest('hex');

/** Content hashes of a variant's modules. */
export function variantHashes(variant) {
  const dir = variantDir(variant);
  return Object.fromEntries(MODULES.map((m) => [m, sha256(join(dir, m))]));
}

/** Throws unless the cache holds exactly the pinned modules. */
export function verifyCache() {
  const manifest = JSON.parse(readFileSync(MANIFEST, 'utf8'));
  for (const m of manifest.modules) {
    const path = join(sourcesDir(), 'cache', m.file);
    if (!existsSync(path)) throw new Error(`missing ${path}; run node ra-pbt/instances/notion/prepare.js`);
    if (sha256(path) !== m.sha256) throw new Error(`hash mismatch for ${m.file}`);
  }
  return manifest;
}

const loaded = new Map();

/**
 * The modules of one variant: { variant, Replica, CrdtDocument,
 * iterateTextSliceTree, compareOpIds, sameId, idKey, hashes }. The demo
 * variant must hash to the pinned manifest.
 */
export async function loadModel(variant) {
  if (loaded.has(variant)) return loaded.get(variant);
  const manifest = verifyCache();
  const dir = variantDir(variant);
  if (!existsSync(join(dir, 'replica.js'))) throw new Error(`variant ${variant} not prepared; run node ra-pbt/instances/notion/prepare.js`);
  const hashes = variantHashes(variant);
  if (variant === 'demo')
    for (const m of manifest.modules) if (hashes[m.file] !== m.sha256) throw new Error(`demo variant ${m.file} differs from the pinned source`);
  const url = (f) => pathToFileURL(join(dir, f)).href;
  const [replica, document, tree, ids] = await Promise.all(['replica.js', 'document.js', 'text-slice-tree.js', 'ids.js'].map((f) => import(url(f))));
  const model = {
    variant,
    dir,
    hashes,
    Replica: replica.Replica,
    CrdtDocument: document.CrdtDocument,
    iterateTextSliceTree: tree.iterateTextSliceTree,
    compareOpIds: ids.compareOpIds,
    sameId: ids.sameId,
    idKey: ids.idKey,
  };
  loaded.set(variant, model);
  return model;
}
