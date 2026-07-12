import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Sig

/-! # Shesha — the conditioned instance and the RA-linearizability capstone

Shesha enters the one framework by the **mergeable-queue route**: the
ternary merge is exhibited directly as the linearization witness. But the
queue's plain hook (`JoinLemma3At` at every honest configuration) is
**FALSE for Shesha** — machine-checked in `Shesha_Join_Refuted.lean`:
`IsCanonicalState` is existential, Shesha's canonical states are not unique
per event set (a concurrent `(ins x←a, del a)` pair folds to different live
sets under the two enumeration orders), and a misaligned canonical triple
makes the merge emit a node twice. The queue was immune only because its
canonical states are unique.

The corrected route (`WitnessClass.lean`) restricts the witnesses to the
class real executions produce: **effective** enumerations (`SheshaEff` —
every insert applies: its anchor is live, or the root, at its point in the
fold). Effectiveness realigns the three slots of the join: the live set of
an effective fold is determined by the event set alone (inserted minus
deleted), which restores `HonestMerge.fresh`-style membership agreement and
the branch-structure invariants that the M0–M2 layer consumes.

The definitional layer (`SheshaD`, `SheshaHonest`, `SheshaEff`, the op
bridge) lives in `Shesha_Sig.lean`; this file holds the capstone
`shesha_ra_linearizable3`, reduced to the **single owed hook**
`shesha_join_at_eff` (documented `sorry`). -/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

/-- **The owed join hook** (the last obligation): under honest histories,
Shesha's ternary merge is the fold of some `lo`-respecting **effective**
enumeration of the union of the branches' events, given effective
witnesses for the LCA and both branches.

`sorry` — the replay half of phase 2. The witness is
`ρ⋆ = (all inserts of the union, planned over the pre-splice anchored
forest: anchors before children, same-anchor runs right-to-left)
++ (all deletes, ascending timestamps)`. Landed layers it composes
(`Shesha_Replay.lean`, `Shesha_EffFold.lean`, all kernel-clean):
- §1 commutation (`insert_insert_comm`, `delete_insert_comm`) — with
  honesty (which excludes `vis` from a delete into an insert of its own
  target or anchor: the target would be dead at the issuer's causal past)
  this discharges `respects` for the inserts-then-deletes shape;
- §3 realization (`fold_planF` via the §2 graft algebra) — the insert
  phase builds any WF anchored forest exactly; `applySeq_toSOp` bridges
  the framework fold to the datatype fold;
- the effective-fold theory (`Shesha_EffFold.lean`): the delete phase is
  an order-free set-drop (`steps_dels`), deletes postpone
  (`steps_postpone_deletes`), the insert phase is the anchored forest
  (`row_steps_ins`), and collapse rows are fronts (`row_dropF`,
  `mem_row_dropF`).
Still owed:
(ii) the **pre-splice forest**: from the merge output `merge s₀ s₁ s₂`
    and the three effective witnesses (each now in `dropF`-normal-form),
    the anchored forest `T` with original-anchor parenthood whose
    delete-collapse is the output — the un-spliced `outRows` plus the
    ghost ids (born-and-died within a branch) that the merge never saw;
(iii) the delete-phase equation: `dropF (deleted) T = merge s₀ s₁ s₂`
    (the merge-time splice IS the delete splice — `expandRow_filter_L` /
    `collapseRow` in `Shesha_M2` is the L-instance of this). -/
theorem shesha_join_at_eff :
    ∀ C', SheshaHonest C' →
      JoinLemma3AtW SheshaD SheshaEff (Configuration.core C') := by
  sorry

/-- **RA-linearizability of Shesha**: at every honestly-reachable
configuration, every version's state is the raw fold of some
`lo`-respecting linearization of its events. -/
theorem shesha_ra_linearizable3 {C : Configuration SheshaD}
    (hReach : HonestReach SheshaD SheshaHonest trivial C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_genHonest_reachW (P := sGuard)
    sheshaEff_init sheshaEff_step shesha_join_at_eff
    (show HonestReach SheshaD (GenHonest SheshaD sGuard) trivial C from hReach)

end Sal.ConditionedMRDTs

section AxiomAuditCond
/-! Axiom audit: the capstone carries exactly the hook's `sorry`; the
route and the witness-class bookkeeping are kernel-clean. -/
#print axioms Sal.ConditionedMRDTs.shesha_ra_linearizable3
#print axioms Sal.ConditionedMRDTs.sheshaEff_step
#print axioms Sal.ConditionedMRDTs.applySeq_toSOp
end AxiomAuditCond
