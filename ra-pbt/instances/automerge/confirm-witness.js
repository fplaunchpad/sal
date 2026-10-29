/** Pure bounded confirmation against the independent text specification. */
import { findWitness } from '../../src/witness.js';
import { DEFAULT_WITNESS_STATE_LIMIT } from '../../src/checks.js';
import { textSpec } from './spec.js';

/**
 * Search the full observation-preserving dependency history, bounded by
 * `budget` specification applications and by `stateLimit` explored
 * (subset, state) pairs, the cap of the end-to-end check. Return true for a
 * witness, false for a completed rejection, or 'undecided' when either
 * bound is exhausted.
 */
export function confirmWitness(semantics, events, target, budget = 200_000, stateLimit = DEFAULT_WITNESS_STATE_LIMIT) {
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
    const res = findWitness(bounded, events, target, { limit: stateLimit });
    return res.truncated ? 'undecided' : res.found;
  } catch (e) {
    if (e === OUT) return 'undecided';
    throw e;
  }
}
