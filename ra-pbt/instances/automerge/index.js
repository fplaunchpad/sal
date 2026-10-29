/**
 * The Automerge text instance: text with marks under two mark semantics
 * (`spec.js`), Automerge replicas behind the ra-pbt adapter interface
 * (`adapter.js`), request generation and reduction (`requests.js`), and the
 * ra-pbt entry points bound to them.
 *
 * `instanceFor(semantics, direct)` is the instance under a mark semantics
 * ('anchor', Peritext's anchors, or 'marker', boundaries as list elements).
 * `direct` is retained as configuration metadata ('layout' or 'chars');
 * both values use the full relational search, which explores every
 * placement the gap rule admits and compares views without identities.
 * `automergeText` is the anchor instance. A failure the end-to-end check
 * reports is repeated by `confirmWitness` in `classify.js` under an
 * application budget, which distinguishes exhaustion from rejection.
 */
import * as core from '../../src/index.js';
import { textSpec } from './spec.js';
import { automergeAdapter } from './adapter.js';
import { nextRequest, reduceRequest, generateOptions, renderStep } from './requests.js';

export * from './spec.js';
export { A, Replica, automergeAdapter, walk, attributed, interpret, localNeighbours, validateEdit, requestOf, actorOf, compareIds, parseId } from './adapter.js';
export { nextRequest, reduceRequest, generateOptions, renderStep } from './requests.js';
export { verifySources } from './verify-sources.js';

const INSTANCES = new Map();

/** The instance under a mark semantics and a search direction. */
export function instanceFor(semantics = 'anchor', direct = 'layout') {
  const key = semantics + '/' + direct;
  if (!INSTANCES.has(key))
    INSTANCES.set(key, { spec: textSpec({ semantics, direct }), adapter: automergeAdapter(semantics), nextRequest, reduceRequest, generateOptions });
  return INSTANCES.get(key);
}

export const automergeText = instanceFor('anchor', 'layout');
export const CHECKS = core.CHECKS;

const pick = (opts) => instanceFor(opts?.semantics ?? 'anchor', opts?.direct ?? 'layout');

/** An execution over Automerge replicas; `opts.semantics` and `opts.direct` select the instance. */
export class Execution extends core.Execution {
  constructor(n, opts = {}) {
    super(pick(opts), n, opts);
  }
}

export const execute = (schedule, opts = {}) => core.execute(pick(opts), schedule, opts);
export const generate = (seed, options, opts = {}) => core.generate(pick(opts), seed, options);
export const shrink = (schedule, fails, opts = {}) => core.shrink(pick(opts), schedule, fails);
export const runCampaign = (opts = {}) => core.runCampaign(pick(opts), { renderStep, ...opts });
export const eventsAt = core.eventsAt;
export const finalSyncSteps = core.finalSyncSteps;
