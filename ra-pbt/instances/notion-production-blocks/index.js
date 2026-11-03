/**
 * ra-pbt instance for the block layer of the production Notion editing
 * code: block creation, split, merge into the predecessor, with insertion
 * and bold inside blocks.
 *
 * `productionBlocksInstance(lib, { texts, profile, sessions, maxBlocks })`
 * is an end-to-end instance (specification, adapter, request generation and
 * reduction) over clients of the library loaded by `loadLibrary`
 * (library.js), seeded with the document whose blocks have the texts
 * `texts`. Profiles are listed in requests.js; `format` and `mixed` compare
 * bold flags.
 */
import { specFor } from './spec.js';
import { makeAdapter, seedDocument, clientFactory } from './adapter.js';
import { nextRequest, reduceRequest, renderStep } from './requests.js';

export { loadLibrary, withVerifiedLibrary } from './library.js';
export { verifySources, libraryDirectory } from './verify-sources.js';
export { specFor, foldGroups, localEdit, ProductionBlockSpec, blocksOf, textsOf, SpecStuck } from './spec.js';
export { decodeOps, itemKey, siblingMoves } from './decode.js';
export { makeAdapter, seedDocument, clientFactory, liveTrees, stateOf, viewOf, charactersOf, contentOf, issueOn, createOps, adapterStats, DEFAULT_SESSIONS, PAGE, pointer, uuid } from './adapter.js';
export { nextRequest, reduceRequest, renderStep, renderBlocks, validOn, allRequests, PROFILES } from './requests.js';

export const FORMAT_PROFILES = new Set(['format', 'mixed']);

export function productionBlocksInstance(lib, { texts, profile = 'structure', sessions, maxBlocks = 6, isolated = false, liveClock = true, observe = null, splitPlacement = 'holder', inherit = 'apply' } = {}) {
  const newClient = clientFactory(lib, { isolated, liveClock });
  const seed = seedDocument(lib, texts, newClient);
  const format = FORMAT_PROFILES.has(profile);
  return {
    name: `notion-production-blocks-${profile}`,
    texts,
    profile,
    format,
    seed,
    lib,
    spec: specFor({ seedGroups: seed.groups, format, splitPlacement, inherit }),
    adapter: makeAdapter(lib, { seed, sessions, newClient, observe }),
    nextRequest: (rnd, view, options) => nextRequest(rnd, view, { profile, maxBlocks, ...options }),
    reduceRequest,
    generateOptions: (o) => ({ openedReplicas: false, ...o }),
    renderStep,
  };
}
