// The Sal runtime OR-set as a law-checking target.
//
// `orset` is the paper's ordinary OR-set: add_x mints a fresh tagged
// instance of x, and rem_x removes every instance of x present in the state
// it is applied to. The effect of rem_x is the runtime's `rm` applied to the
// tags the runtime's `observe` reports for x in that state, so the issuing
// replica performs exactly the runtime operation. Merge, read and
// serialisation are the runtime's. The raw `do` is total: an add whose tag is
// already present leaves the state unchanged (set union), where the runtime
// refuses a duplicate tag at issuance.
//
// `orsetObservedTags` keeps the runtime's operation shape literally: an
// `rm` carries the tag list observed by its issuer and kills exactly those
// tags wherever it is applied.

import { orset as runtimeOrset } from '../../../runtime/src/datatypes/orset.js';
import { PMap } from '../../../runtime/src/pmap.js';

const ELEMENTS = ['a', 'b'];

const addEffect = (s, op) => (s.has(op.tag) ? s : runtimeOrset.apply(s, { type: 'add', tag: op.tag, el: op.el }));

export const orsetDatatype = {
  name: 'orset',
  init: () => runtimeOrset.init(),
  apply(s, op) {
    if (op.type === 'add') return addEffect(s, op);
    if (op.type === 'rm') return runtimeOrset.apply(s, { type: 'rm', tags: runtimeOrset.observe(s, op.el) });
    throw new Error(`unknown op ${op.type}`);
  },
  merge3: (l, a, b) => runtimeOrset.merge3(l, a, b),
  read: (s) => runtimeOrset.read(s),
  serialise: (s) => runtimeOrset.fingerprint(s),
};

export const orsetObservedTagsDatatype = {
  ...orsetDatatype,
  name: 'orset-observed-tags',
  apply(s, op) {
    if (op.type === 'add') return addEffect(s, op);
    if (op.type === 'rm') return runtimeOrset.apply(s, { type: 'rm', tags: op.tags });
    throw new Error(`unknown op ${op.type}`);
  },
};

/** The ordinary set specification: add_x and rem_x on a finite set,
 *  observed as the sorted element list. Every update is admitted. */
export const setSpec = {
  init: () => [],
  step(phi, op) {
    if (op.type === 'add') return phi.includes(op.el) ? phi : [...phi, op.el].sort();
    if (op.type === 'rm') return phi.filter((x) => x !== op.el);
    return undefined;
  },
  observe: (phi) => phi,
};

function genOrsetEvent(rnd, state, ctx, withTags) {
  if (rnd() < 0.55) return { type: 'add', el: ELEMENTS[Math.floor(rnd() * ELEMENTS.length)], tag: ctx.fresh() };
  const live = runtimeOrset.read(state);
  const el = live.length && rnd() < 0.8 ? live[Math.floor(rnd() * live.length)] : ELEMENTS[Math.floor(rnd() * ELEMENTS.length)];
  return withTags ? { type: 'rm', el, tags: runtimeOrset.observe(state, el) } : { type: 'rm', el };
}

const specCommutes = (o1, o2) => !(o1.el === o2.el && o1.type !== o2.type);

/** rc = {(rem_x, add_x)}: a concurrent removal is ordered before an
 *  addition of the same element (add wins). Labels drop the tag. */
export const orsetInstance = {
  name: 'orset',
  genEvent: (rnd, state, ctx) => genOrsetEvent(rnd, state, ctx, false),
  rc: (o1, o2) => o1.type === 'rm' && o2.type === 'add' && o1.el === o2.el,
  label: (op) => `${op.type}:${op.el}`,
  specCommutes,
  spec: setSpec,
  observe: (s) => runtimeOrset.read(s),
};

/** The literal runtime operation shape. rc relates an rm to an add exactly
 *  when the rm names the add's tag; the label is the whole operation. */
export const orsetObservedTagsInstance = {
  name: 'orset-observed-tags',
  genEvent: (rnd, state, ctx) => genOrsetEvent(rnd, state, ctx, true),
  rc: (o1, o2) => o1.type === 'rm' && o2.type === 'add' && o1.tags.includes(o2.tag),
  label: (op) => JSON.stringify(op),
  specCommutes,
  spec: setSpec,
  observe: (s) => runtimeOrset.read(s),
};

/** The element-level rc of the paper paired with the observed-tags
 *  operations. */
export const orsetObservedTagsElementRcInstance = {
  ...orsetObservedTagsInstance,
  name: 'orset-observed-tags-element-rc',
  rc: orsetInstance.rc,
};

/** Negative control: the runtime OR-set with a merge that keeps only
 *  (A ∩ B) ∪ (A ∖ L), forgetting instances added on the second branch. */
export const brokenOrsetDatatype = {
  ...orsetDatatype,
  name: 'broken-orset',
  merge3(l, a, b) {
    const t = PMap.empty().begin();
    for (const [tag, el] of a.entries()) if (b.has(tag) || !l.has(tag)) t.set(tag, el);
    return t.freeze();
  },
};
export const brokenOrsetInstance = { ...orsetInstance, name: 'broken-orset' };
