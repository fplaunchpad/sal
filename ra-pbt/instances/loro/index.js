/**
 * The Loro text instance: the list specification with styles (`spec.js`),
 * Loro replicas behind the ra-pbt adapter interface (`adapter.js`), request
 * generation and reduction (`requests.js`), and the ra-pbt entry points bound
 * to them.
 *
 * `loroText(rule, attrs)` is the instance under an insertion rule ('gap',
 * the default, 'left' or 'both') and a reading of the expand configuration
 * ('carry', the default, 'inherit', 'expand', 'anchors' or 'persistent'); `loroGap` is the default instance. The bound
 * functions take the arguments of their ra-pbt counterparts without the
 * instance, plus `rule` and `attrs` in their options.
 */
import * as core from '../../src/index.js';
import { specFor } from './oracle.js';
import { loroAdapter } from './adapter.js';
import { nextRequest, reduceRequest, generateOptions, renderStep } from './requests.js';

export * from './oracle.js';
export { Replica, LoroDoc, loroAdapter, validateEdit, requestOf, STYLE_CONFIG } from './adapter.js';
export { nextRequest, reduceRequest, generateOptions, renderStep } from './requests.js';
export { verifySources } from './verify-sources.js';

const INSTANCES = {};

/** The instance under an insertion rule and an attribute reading. */
export function loroText(rule = 'gap', attrs = 'carry') {
  return (INSTANCES[rule + '/' + attrs] ??= { spec: specFor(rule, attrs), adapter: loroAdapter, nextRequest, reduceRequest, generateOptions });
}

export const loroGap = loroText('gap');
export const CHECKS = core.CHECKS;

/** An execution over Loro replicas. */
export class Execution extends core.Execution {
  constructor(n, { rule = 'gap', attrs = 'carry', ...opts } = {}) {
    super(loroText(rule, attrs), n, opts);
  }
}

export const execute = (schedule, { rule = 'gap', attrs = 'carry', ...opts } = {}) => core.execute(loroText(rule, attrs), schedule, opts);
export const generate = (seed, options) => core.generate(loroGap, seed, options);
export const shrink = (schedule, fails, { rule = 'gap', attrs = 'carry' } = {}) => core.shrink(loroText(rule, attrs), schedule, fails);
export const eventsAt = core.eventsAt;
export const finalSyncSteps = core.finalSyncSteps;
export const runCampaign = ({ rule = 'gap', attrs = 'carry', ...opts } = {}) => core.runCampaign(loroText(rule, attrs), { renderStep, ...opts });
