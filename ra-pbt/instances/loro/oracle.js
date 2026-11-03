/**
 * The Loro text specification with the ra-pbt witness search bound to it.
 * This module and everything it imports are independent of Loro.
 *
 * `findWitness` and `allFinalViews` take the arguments of their ra-pbt
 * counterparts without the specification, plus `rule` ('gap', the default,
 * 'left' or 'both') choosing the insertion rule and `attrs` ('carry', the
 * default, 'inherit', 'expand', 'anchors' or 'persistent', the last from
 * anchored.js) choosing the reading of the expand
 * configuration.
 */
import { findWitness as coreFindWitness, allFinalViews as coreAllFinalViews } from '../../src/witness.js';
import { textSpec } from './spec.js';
import { anchoredSpec } from './anchored.js';

export * from './spec.js';

const SPECS = {};

/** The specification under an insertion rule and an attribute reading. */
export function specFor(rule = 'gap', attrs = 'carry') {
  if (!['gap', 'left', 'both'].includes(rule)) throw new Error('unknown insertion rule: ' + rule);
  if (attrs === 'persistent') {
    if (rule !== 'gap') throw new Error('the persistent reading is defined under the gap rule only');
    return (SPECS['gap/persistent'] ??= anchoredSpec());
  }
  if (!['carry', 'inherit', 'expand', 'anchors'].includes(attrs)) throw new Error('unknown attribute reading: ' + attrs);
  return (SPECS[rule + '/' + attrs] ??= textSpec(rule, { attrsMode: attrs }));
}

export const findWitness = (events, target, { rule = 'gap', attrs = 'carry' } = {}) => coreFindWitness(specFor(rule, attrs), events, target);
export const allFinalViews = (events, { rule = 'gap', attrs = 'carry', ...opts } = {}) => coreAllFinalViews(specFor(rule, attrs), events, opts);
