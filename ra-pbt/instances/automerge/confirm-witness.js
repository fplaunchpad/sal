/** Pure bounded confirmation against the independent text specification. */
import { findWitness } from '../../src/witness.js';
import { textSpec } from './spec.js';

/**
 * Search the full observation-preserving dependency history, bounded by
 * `budget` specification applications. Return true for a witness, false
 * for completed rejection, or 'undecided' on exhaustion.
 */
export function confirmWitness(semantics, events, target, budget = 200_000) {
  // instanceFor(semantics, 'chars').spec is exactly this construction; no
  // implementation adapter or Automerge package is needed for confirmation.
  const base = textSpec({ semantics, direct: 'chars' });
  let n = 0;
  const OUT = new Error('budget');
  const bounded = {
    ...base,
    applyAll: (s, op) => {
      if (++n > budget) throw OUT;
      return base.applyAll(s, op);
    },
    applyDirected: (s, op, t) => {
      if (++n > budget) throw OUT;
      return base.applyDirected(s, op, t);
    },
  };
  try {
    return findWitness(bounded, events, target).found;
  } catch (e) {
    if (e === OUT) return 'undecided';
    throw e;
  }
}
