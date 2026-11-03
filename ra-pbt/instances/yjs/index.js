/**
 * The Y.Text instance: the strong list specification with formatting marks
 * (`spec.js`), Yjs replicas behind the ra-pbt adapter interface
 * (`adapter.js`), request generation and reduction (`requests.js`), and the
 * ra-pbt entry points bound to them.
 *
 * `yjsText` is the instance under the gap rule. The bound functions take the
 * same arguments as their ra-pbt counterparts without the instance; the
 * witness functions (from `oracle.js`) also take `rule` ('gap', 'left' or
 * 'both').
 */
import * as core from '../../src/index.js';
import { specFor } from './oracle.js';
import { yjsAdapter } from './adapter.js';
import { nextRequest, reduceRequest, generateOptions, renderStep } from './requests.js';

export * from './oracle.js';
export { Replica, Y, yjsAdapter, effectOf, deletedUnits, validateEdit, requestOf } from './adapter.js';
export { nextRequest, reduceRequest, generateOptions, renderStep } from './requests.js';
export { verifySources } from './verify-sources.js';

export const yjsText = { spec: specFor('gap'), adapter: yjsAdapter, nextRequest, reduceRequest, generateOptions };

export const CHECKS = core.CHECKS;

/** An execution over Yjs replicas. */
export class Execution extends core.Execution {
  constructor(n, opts = {}) {
    super(yjsText, n, opts);
  }
}

export const execute = (schedule, opts) => core.execute(yjsText, schedule, opts);
export const generate = (seed, options) => core.generate(yjsText, seed, options);
export const shrink = (schedule, fails) => core.shrink(yjsText, schedule, fails);
export const eventsAt = core.eventsAt;
export const finalSyncSteps = core.finalSyncSteps;
export const runCampaign = (opts) => core.runCampaign(yjsText, { renderStep, ...opts });
