// Commit GC: the keep-set.
//
// Given the CURRENT heads h_1..h_n of the registered replicas:
//
//   Seeds = union over all pairs i <= j of MCA(h_i, h_j)
//           (i = j included: MCA(h,h) = {h}, so every head is a seed)
//   Keep  = the upward closure of Seeds: all reflexive DESCENDANTS of any
//           seed, i.e. everything from the pairwise meets up to the heads
//           and beyond.
//
// gc() drops every commit outside Keep.
//
// SOUNDNESS CAVEATS:
//
// 1. Sound ONLY under the head-sync discipline: every future merge is
//    between two CURRENT heads. That is exactly the hypothesis of the
//    gc_safety theorem. If a
//    replica could merge against an OLD commit (pull of a stale head), the
//    LCA of that merge could lie strictly below the keep-set horizon and be
//    gone, so the merge would run with a wrong (higher or missing) LCA
//    state; e.g. an element deleted in both branches below the horizon is
//    no longer witnessed by the LCA and resurrects. src/runtime.js enforces
//    the discipline by construction (commit on own head, sync of current
//    heads only).
//
// 2. Sound only against the CURRENT registered replica set (open-membership
//    caveat): the keep-set is computed from the heads that exist NOW. A
//    replica registered after gc, or an unregistered/offline peer, may need
//    history that was pruned. Membership must be closed at gc time; the
//    runtime refuses to register new replicas once the root is pruned.
//
// Note gc uses mcas() (ALL maximal common ancestors), not lca(): keeping
// every MCA of a criss-cross pair is sound and needs no uniqueness, so gc
// never throws CrissCrossError; only merging does.

import { mcas } from './lca.js';

/** The keep-set (Set of commit ids) for the given current head ids.
 *  Seeds are the MCA CLOSURE of the heads (the least superset closed under
 *  pairwise MCA): virtual criss-cross resolution reads MCAs of MCAs, and a
 *  one-layer seed is one closure layer short. Finite: ranks only decrease. */
export function keepSet(dag, headIds) {
  const seeds = new Set(headIds);
  let grew = true;
  while (grew) {
    grew = false;
    const arr = [...seeds];
    for (let i = 0; i < arr.length; i++) {
      for (let j = i; j < arr.length; j++) { // j = i included: members kept
        for (const m of mcas(dag, arr[i], arr[j])) {
          if (!seeds.has(m)) { seeds.add(m); grew = true; }
        }
      }
    }
  }
  // Upward closure: reflexive descendants of every seed.
  const children = dag.childrenIndex();
  const keep = new Set(seeds);
  const stack = [...seeds];
  while (stack.length > 0) {
    for (const child of children.get(stack.pop()) ?? []) {
      if (!keep.has(child)) { keep.add(child); stack.push(child); }
    }
  }
  return keep;
}

/** Drop every commit outside the keep-set. Returns { kept, dropped }. */
export function runGc(dag, headIds) {
  const keep = keepSet(dag, headIds);
  let dropped = 0;
  for (const id of dag.ids()) {
    if (!keep.has(id)) { dag.remove(id); dropped++; }
  }
  // Do not retain the old skeleton as dangling ids.  Because `keep` is upward
  // closed, no retained-to-retained path uses a dropped node; boundary parent
  // edges can simply be cut (the seed becomes a parent-free epoch base).
  dag.restrictParents(keep);
  return { kept: keep.size, dropped };
}
