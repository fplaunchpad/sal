/**
 * Notion block-editor instances for ra-pbt.
 *
 * `notionInstance(model, { texts, format, sessions })` is an end-to-end
 * instance (specification, adapter, request generation and reduction) over
 * replicas of a model loaded by `loadModel` (sources.js), seeded with the
 * document whose blocks have the texts `texts`. `lawsFor(model, { texts,
 * format })` (laws.js) is the law-layer datatype and instance over the same
 * model. `diagnose` (classify.js) names the demo code path behind a failure.
 *
 * Models: `demo`, the pinned public demo, and `anchor-absorb`, the corrected
 * block merge; see sources.js.
 */
import { specFor } from './spec.js';
import { makeAdapter, seedTransactions } from './adapter.js';
import { nextRequest, reduceRequest, renderStep } from './requests.js';

export { loadModel, variantHashes, verifyCache, VARIANTS } from './sources.js';
export { specFor, blocksOf, textsOf, decode, decodeTx, FormattedIdentitySpec } from './spec.js';
export { makeAdapter, seedTransactions, viewOf, presentOf, issueOn, adapterStats, DEFAULT_SESSIONS } from './adapter.js';
export { nextRequest, reduceRequest, renderStep, renderBlocks, validOn, allRequests } from './requests.js';
export { lawsFor } from './laws.js';
export { diagnose, classifyFailure, pathClasses } from './classify.js';

export function notionInstance(model, { texts, format = false, profile, sessions, maxBlocks = 6 } = {}) {
  const seed = seedTransactions(model, texts);
  return {
    name: `notion-${model.variant}-${profile ?? (format ? 'format' : 'text')}`,
    model,
    texts,
    format,
    profile: profile ?? (format ? 'format' : 'text'),
    seed,
    spec: specFor({ seedTransactions: seed, format }),
    adapter: makeAdapter(model, { seed, sessions }),
    nextRequest: (rnd, view, options) => nextRequest(rnd, view, { format, profile, maxBlocks, ...options }),
    reduceRequest,
    generateOptions: (o) => ({ openedReplicas: false, ...o }),
    renderStep,
  };
}
