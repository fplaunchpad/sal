/**
 * Sequential specifications.
 *
 * A specification is an object
 *
 *   init()                       the initial state
 *   apply(state, op)             the next state, or null when a precondition fails
 *   applyAll?(state, op)         every next state (a relational specification);
 *                                defaults to [apply(state, op)] without nulls,
 *                                and a specification without it is
 *                                deterministic
 *   applyDirected?(state, op, target)
 *                                the next states consistent with a target view
 *                                (for instance, placements in the order the
 *                                target gives); defaults to applyAll. It must
 *                                not lose a witness: some witness for `target`
 *                                exists under applyAll exactly when one exists
 *                                under applyDirected.
 *   directs?(target)             whether applyDirected narrows the search for
 *                                this target; defaults to true exactly when
 *                                applyDirected is given
 *   view(state)                  the observable value of a state
 *   serialise(state)             canonical string of a state (states with equal
 *                                strings are interchangeable in the search)
 *   viewKey(view)                canonical string of a view; two views are
 *                                equal exactly when their keys are
 *   normalise?(view)             a view as displayed in reports (for instance
 *                                with identities dropped); defaults to the
 *                                identity
 *   localEdit?(view, request)    the meaning of a request on the issuing
 *                                replica's own view, used by the localMeaning
 *                                check
 *   rc?(op1, op2)                optional specification-conflict annotation;
 *                                copied through normalisation, but unused
 *                                by the end-to-end witness search. It neither
 *                                filters dependencies nor supplies the
 *                                implementation's directed rc policy.
 *   equivalent?(a, b)            equivalence of states; defaults to equal
 *                                serialisations
 *
 * States must be treated as immutable values: the witness search shares them
 * between branches.
 */

const NORMALISED = Symbol('ra-pbt.spec');

/** The specification with every optional member filled in. Idempotent. */
export function normaliseSpec(spec) {
  if (spec && spec[NORMALISED]) return spec;
  const missing = ['init', 'apply', 'view', 'serialise', 'viewKey'].filter((k) => typeof spec?.[k] !== 'function');
  if (missing.length) throw new TypeError('specification lacks ' + missing.join(', '));
  const applyAll =
    spec.applyAll ??
    ((state, op) => {
      const next = spec.apply(state, op);
      return next === null || next === undefined ? [] : [next];
    });
  const hasDirected = typeof spec.applyDirected === 'function';
  return {
    ...spec,
    applyAll,
    applyDirected: hasDirected ? spec.applyDirected : (state, op) => applyAll(state, op),
    directs: spec.directs ?? (() => hasDirected),
    relational: typeof spec.applyAll === 'function',
    normalise: spec.normalise ?? ((v) => v),
    equivalent: spec.equivalent ?? ((a, b) => spec.serialise(a) === spec.serialise(b)),
    [NORMALISED]: true,
  };
}

/** Equality of two views under the specification's canonical key. */
export function viewsEqual(spec, a, b) {
  return spec.viewKey(a) === spec.viewKey(b);
}

/** Folds operations deterministically from the initial state; null on a failed precondition. */
export function fold(spec, ops, from = spec.init()) {
  let state = from;
  for (const op of ops) {
    state = spec.apply(state, op);
    if (state === null || state === undefined) return null;
  }
  return state;
}

/** Every state the operations can reach from the initial state, deduplicated by serialisation. */
export function foldAll(spec, ops, from = spec.init()) {
  const s = normaliseSpec(spec);
  let states = [from];
  for (const op of ops) {
    const next = new Map();
    for (const st of states) for (const n of s.applyAll(st, op)) next.set(s.serialise(n), n);
    states = [...next.values()];
    if (states.length === 0) return [];
  }
  return states;
}
