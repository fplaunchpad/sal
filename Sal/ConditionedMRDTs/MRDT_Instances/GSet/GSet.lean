import Sal.ConditionedMRDTs.Metatheory.Adequacy

/-!
# G-Set — the LCA-blind demo kernel (unconditional delta route)

Split out of the original monolithic `MRDT_Instances.lean`; declarations
verbatim, names unchanged.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## G-Set -/

/-- Every pair of G-Set events commutes (insert-insert). -/
theorem GSet_all_comm : ∀ a b : Op GSetCond.AppOp,
    GSetCond.toCRDTSig.commutes a b :=
  fun a b s => (Set.insert_comm a.2.2 b.2.2 s).symm

/-- G-Set's `rc` is constantly `Either`. -/
theorem GSet_rc_either : ∀ o₁ o₂ : Op GSetCond.AppOp,
    GSetCond.toCRDTSig.rc o₁ o₂ = RcRes.Either :=
  fun _ _ => rfl

/-- The update-layer bundle for G-Set: `rc = Either` kills every rc premise. -/
theorem GSet_updateVCs : UpdateVCs GSetCond.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (GSet_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [GSet_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [GSet_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [GSet_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

/-- G-Set `update`, unfolded to `Set Nat` (where the instances live). -/
theorem GSet_update_eq (s : Set Nat) (e : Op GSetCond.AppOp) :
    GSetCond.update s e = insert e.2.2 s := rfl

/-- G-Set `mergeL`, unfolded to `Set Nat`. -/
theorem GSet_mergeL_eq (l a b : Set Nat) :
    GSetCond.mergeL l a b = a ∪ b := rfl

/-- The ternary core bundle for G-Set (`mergeL _ a b = a ∪ b`, LCA-blind). -/
theorem GSet_coreVCs3 : CoreVCs3 GSetCond := by
  refine ⟨GSet_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    exact Set.union_comm a b
  · intro s
    exact Set.empty_union s
  · intro l a b e
    simp only [GSet_update_eq, GSet_mergeL_eq]
    apply Set.ext
    intro x
    simp only [Set.mem_union, Set.mem_insert_iff]
    tauto
  · intro a e π₀ π₂ _ _
    simp only [GSet_update_eq, GSet_mergeL_eq]
    exact Set.insert_union


end Sal.ConditionedMRDTs
