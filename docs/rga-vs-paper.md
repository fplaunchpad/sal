# RGA in Sal vs. the literature

Cross-reference between the Lean formalization in
`Sal/CRDTs/RGA/RGA_CRDT.lean` (state-based CRDT), `Sal/MRDTs/Replicated_Growable_Array/Replicated_Growable_Array_MRDT.lean`
(state-based MRDT), and their read-side companions
(`*/RGA_ReadSide.lean`, `*/Replicated_Growable_Array_ReadSide.lean`),
against the canonical RGA reference:

> Hyun-Gul Roh, Myeongjae Jeon, Jin-Soo Kim, Joonwon Lee.
> *Replicated Abstract Data Types: Building Blocks for
> Collaborative Applications.* Journal of Parallel and Distributed
> Computing, 71(3):354–368, 2011.

This document maps the paper's claims to the Lean theorems. It is the
RGA counterpart of `peritext-vs-paper.md`.

## Formalization target

The paper presents RGA as an **op-based** sequence CRDT. Our Lean is
a **state-based** reformulation: the op log is stored as three
grow-only maps (`chars`, `afters`, `deleted`) keyed by `OpId =
(timestamp, replica id)`, joined componentwise on merge. The two
formulations are convergence-equivalent under the paper's
`distinct_ops` assumption, but the correctness criteria land in
different places:

| Paper | Our Lean | Notes |
|---|---|---|
| Convergence (Section 4) | 24 RA-linearizability VCs (per variant) | All 24 closed on the MRDT (`by sal` / `by grind`); CRDT is the substrate Peritext builds on. Pointwise equality on each state component. |
| Causal delivery (Section 4.1) | Framework-level assumption | Sal's state-based model assumes causal delivery; the VCs verify the local reconciliation rule. |
| RGA traversal order (Section 4.3) | `visible_lt` inductive in `RGA_ReadSide.lean` (mirrored on MRDT) | Four-rule DFS: parent-child, sibling tiebreak by `opid_max`, left-descendant-of-sibling, transitive. |
| User-visible sequence | `readSeq` (CRDT) / `readSeq_visible` (MRDT) | Per-OpId read; convergence at the read is proved. Full list-form traversal is a follow-up (see `docs/list-form-readrichtext-design.md`). |

## Intent-preservation: literature claims ↔ Lean theorems

| Claim | Lean theorem (CRDT) | Lean theorem (MRDT) | Status |
|---|---|---|---|
| Causal-order preservation: an insert appears in the visible sequence after its `afterId` predecessor (and transitively after every ancestor). | `causal_order_visible_lt` | `causal_order_visible_lt` | ✅ |
| Tombstones are monotonic: a `Remove` never resurrects a previously-removed (or never-inserted) character. | `tombstone_monotone_under_remove` (+ `remove_tombstones_target` companion) | `tombstone_monotone_under_remove` (+ `remove_tombstones_target`) | ✅ |
| Concurrent inserts at the same anchor resolve deterministically: the insert with the higher `opid_max` (CRDT) / higher `ts` (MRDT) is read first, regardless of merge order. | `concurrent_insert_tiebreak_deterministic` | `concurrent_insert_tiebreak_deterministic` | ✅ |
| Read converges with state: equal states give equal reads. | `readSeq_convergent` | `readSeq_visible_convergent` | ✅ |

## Read-side substrate sharing

Peritext (`Sal/CRDTs/Peritext/Peritext_ReadSide.lean`) duplicates
`visible_lt` and `afters_reach` on its own (richer) state shape.
That duplication predates the standalone RGA readside; refactoring
Peritext to import from `RGA_ReadSide` is a follow-up. The two
inductives are intentionally identical in shape so the refactor is
mechanical.

## Deliberate scope cuts

- **List form of `readSeq` is not yet built.** A per-OpId read is
  enough for the headline causal-order, tombstone, and tiebreak
  theorems. The list form needs a Prop-valued `is_rga_traversal`
  spec (see `docs/list-form-readrichtext-design.md` for the design).
- **Garbage-collection soundness** (dropping a tombstone once every
  replica has observed it) is not yet stated. It needs version-vector
  state, which the current Σ does not carry.
- **Concurrent-insert stability under arbitrary delivery orderings**
  is implicit in `concurrent_insert_tiebreak_deterministic`: the
  sibling rule depends only on `opid_max`, which is symmetric in its
  arguments, so the order in which the two inserts arrive at a
  replica does not change the resulting `visible_lt`. A standalone
  theorem stating this could be added if needed.

## Known structural obstruction (separate file)

`docs/rga-rehab-limitation.md` records why a tombstone-free
"`RGA_Splice_MRDT`" variant — proposed to drop the `deleted` map by
having merge rewrite orphan `afterId` pointers via LCA-derived
predecessors — fails the `lem_0op` VC structurally. That work was
removed from the suite (commit `17cf879`); the present read-side
does not depend on it.

## Files at a glance

| Purpose | Path |
|---|---|
| State-based CRDT (24 VCs) | `Sal/CRDTs/RGA/RGA_CRDT.lean` |
| State-based MRDT (24 VCs) | `Sal/MRDTs/Replicated_Growable_Array/Replicated_Growable_Array_MRDT.lean` |
| CRDT read-side | `Sal/CRDTs/RGA/RGA_ReadSide.lean` |
| MRDT read-side | `Sal/MRDTs/Replicated_Growable_Array/Replicated_Growable_Array_ReadSide.lean` |
| Tombstone-free obstruction (historical) | `docs/rga-rehab-limitation.md` |
