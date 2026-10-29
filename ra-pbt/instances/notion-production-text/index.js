/**
 * The production Notion text instance: the specification (`spec.js`),
 * replicas of the exported production library behind the ra-pbt adapter
 * interface (`adapter.js`), request generation (`requests.js`), and the
 * ra-pbt entry points bound to them.
 *
 * `instanceFor({ rule, reading, local })` is the instance under an insertion
 * rule ('gap', 'left', 'both'), an annotation reading ('anchored',
 * 'interval') and a local meaning ('positional', 'inherit'); `notionText` is
 * the default (gap, anchored, positional).
 */
import * as core from '../../src/index.js';
import { textSpec } from './spec.js';
import { notionTextAdapter } from './adapter.js';
import { nextRequest, reduceRequest, generateOptions, renderStep } from './requests.js';

export * from './spec.js';
export { Replica, BLOCK, items, visibleWithIds, displayedOf, notionTextAdapter, requestOf, validateRequest, sessionOf } from './adapter.js';
export { nextRequest, reduceRequest, generateOptions, renderStep } from './requests.js';
export { verifySources, describeVerification } from './verify-sources.js';
export { library } from './library.js';

const INSTANCES = new Map();

/** The instance for a specification configuration (memoised, so its prepared form is shared). */
export function instanceFor(config = {}) {
  const key = JSON.stringify({ rule: 'gap', reading: 'anchored', local: 'positional', ...config });
  if (!INSTANCES.has(key)) INSTANCES.set(key, { spec: textSpec(JSON.parse(key)), adapter: notionTextAdapter, nextRequest, reduceRequest, generateOptions });
  return INSTANCES.get(key);
}

export const notionText = instanceFor();
export const CHECKS = core.CHECKS;

export const execute = (schedule, opts = {}, config) => core.execute(instanceFor(config), schedule, opts);
export const runCampaign = (opts, config) => core.runCampaign(instanceFor(config), { renderStep, ...opts });
