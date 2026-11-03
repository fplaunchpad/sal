/**
 * The Y.Text specification with the ra-pbt witness search bound to it. This
 * module and everything it imports are independent of Yjs.
 *
 * `findWitness` and `allFinalViews` take the arguments of their ra-pbt
 * counterparts without the specification, plus `rule` ('gap', the default,
 * 'left' or 'both') choosing the insertion rule.
 */
import { findWitness as coreFindWitness, allFinalViews as coreAllFinalViews } from '../../src/witness.js';
import { textSpec } from './spec.js';

export * from './spec.js';

const SPECS = { gap: textSpec('gap'), left: textSpec('left'), both: textSpec('both') };

/** The specification under an insertion rule. */
export function specFor(rule = 'gap') {
  const s = SPECS[rule];
  if (!s) throw new Error('unknown insertion rule: ' + rule);
  return s;
}

export const findWitness = (events, target, { rule = 'gap' } = {}) => coreFindWitness(specFor(rule), events, target);
export const allFinalViews = (events, { rule = 'gap', ...opts } = {}) => coreAllFinalViews(specFor(rule), events, opts);
