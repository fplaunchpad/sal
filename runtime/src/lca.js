// LCA = maximal common ancestors (MCA) over the commit DAG.
//
// The merge discipline needs ONE lowest common ancestor to feed
// merge3(lcaState, aState, bState). Over a DAG the MCA need not be unique
// (criss-cross merges), a case this gate does not resolve: virtual merge bases
// (recursive merge of the MCAs, git-merge style) are not yet supported.
// So lca() is an explicit gate: unique MCA => return it; multiple MCAs =>
// throw CrissCrossError. Never a silent pick.

export class CrissCrossError extends Error {
  constructor(mcaIds) {
    super(
      `criss-cross merge: ${mcaIds.length} maximal common ancestors ` +
      `(${mcaIds.join(', ')}). Virtual merge bases are not yet in the ` +
      `verified model; refusing to pick one silently.`
    );
    this.name = 'CrissCrossError';
    this.mcas = mcaIds;
  }
}

/** ALL maximal common ancestors of commits a and b (array of commit ids).
 *
 *  Maximality shortcut: the common-ancestor set CA is downward closed
 *  (an ancestor of a common ancestor is a common ancestor), so a member c
 *  is NON-maximal iff some member of CA lists c as an immediate parent.
 *  One pass over CA's parent lists suffices; no per-pair reachability. */
export function mcas(dag, aId, bId) {
  const A = dag.ancestorSet(aId);
  const B = dag.ancestorSet(bId);
  const ca = new Set();
  for (const x of A) if (B.has(x)) ca.add(x);
  const nonMax = new Set();
  for (const c of ca) {
    for (const p of dag.get(c).parents) if (ca.has(p)) nonMax.add(p);
  }
  return [...ca].filter((c) => !nonMax.has(c));
}

/** The unique LCA of a and b, or throw.
 *  - no common ancestor: Error (cannot happen for commits grown from the
 *    runtime's single root unless gc severed unrelated histories);
 *  - multiple MCAs: CrissCrossError (the criss-cross gate). */
export function lca(dag, aId, bId) {
  const m = mcas(dag, aId, bId);
  if (m.length === 1) return m[0];
  if (m.length === 0) {
    throw new Error(`no common ancestor of ${aId} and ${bId}`);
  }
  throw new CrissCrossError(m);
}
