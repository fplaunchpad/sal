import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_EqJoin_NF
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_Instance_NF
import Sal.ConditionedMRDTs.Framework.Base.CRDT_TS
import Sal.ConditionedMRDTs.Metatheory.GenericEqQuotient
import Sal.ConditionedMRDTs.Metatheory.GenericEqQuotient_NF
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_ConditionedConvergence
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_Instance
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_MergeLinearization
import Sal.ConditionedMRDTs.Refutations.UpdateFeasibility_Gate
import Sal.ConditionedMRDTs.Development.RGA_SwapRoute_Residuals

/-!
# `EqJoinLemma3C_NF` for the RGA, reduced to the LITERAL-fold merge residual

*Additive; modifies no existing file; 0 `sorry`.*

The born-applicable resolution of the `≈`-vs-literal obstruction (`WALL1_ANALYSIS.md`).  The merge
machinery (`eq_merge_two_sided_final`) needs the branches as LITERAL folds; `GoodConfig3NF` supplies
the born-applicable deliveries `ρ₀/ρ₁/ρ₂` whose raw folds ARE literal states `≈ s₀/s₁/s₂`.  So state
the residual over those literal folds, and transport to the `≈`-classes by ONE `merge`-congruence
(`mergeFold_transport`).

* `RgaEqJoinResidualLit` — produce, from the three born-applicable deliveries, a delta enum `π₀` with
  the LITERAL merge=fold `eq (merge (fold ρ₀) (fold ρ₁) (fold ρ₂)) (applySeqR (fold ρ₀) π₀)`.
* `rga_eqJoin_of_residualLit_NF : RgaEqJoinResidualLit → EqJoinLemma3C_NF` — the reduction, via
  `mergeFold_transport` + `isCanonicalStateEqNF_union_of_fold`.  **`EqJoinLemma3C_NF` now reduces to a
  pure literal-fold merge identity — NO `≈`-vs-literal, NO `GenDisc`.**  What remains is discharging
  the LITERAL residual (the six pieces hD/hB/hBE/hcm/hbridge/hMSR on literal branch folds), now UNBLOCKED.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGAEqJoinNF

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' rgaCongVC')
open Sal.ConditionedMRDTs.RGAInstanceNF (rga_invCong)
open Sal.ConditionedMRDTs (noopFeasible)
open RGAMergeLinearization (applySeqR)

/-- **The literal-fold merge residual.**  From the three born-applicable deliveries `ρ₀` (LCA),
`ρ₁`/`ρ₂` (branches) — enumerating `ev₁∩ev₂`, `ev₁`, `ev₂` respectively, all `loOnEq`-respecting and
`noopFeasible` — produce a `loOnEq`-respecting, `noopFeasible` delta enum `π₀` whose fold from the LCA
fold equals the RGA `merge` of the three LITERAL folds.  No `≈`: the branches are literal. -/
def RgaEqJoinResidualLit (W : op_t → concrete_st → Prop) : Prop :=
  ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ : List op_t),
    (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
    (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
    (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
    fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
    listPermOf ρ₀ (ev₁ ∩ ev₂) → respects ρ₀ (loOnEq rgaEqEquiv' W vis (ev₁ ∩ ev₂)) →
      noopFeasible RGACondSig' ρ₀ init_st →
    listPermOf ρ₁ ev₁ → respects ρ₁ (loOnEq rgaEqEquiv' W vis ev₁) →
      noopFeasible RGACondSig' ρ₁ init_st →
    listPermOf ρ₂ ev₂ → respects ρ₂ (loOnEq rgaEqEquiv' W vis ev₂) →
      noopFeasible RGACondSig' ρ₂ init_st →
    ∃ π₀ : List op_t,
      listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
      respects π₀ (loOnEq rgaEqEquiv' W vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
      noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀) ∧
      eq (merge (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂))
        (applySeqR (applySeqR init_st ρ₀) π₀)

/-- **`EqJoinLemma3C_NF` from the literal-fold residual.**  Extract the three born-applicable
deliveries from the canonical-state inputs; run the residual on their LITERAL folds; `mergeFold_transport`
carries the resulting merge=fold to the `≈`-classes `mergeL s₀ s₁ s₂`; `isCanonicalStateEqNF_union_of_fold`
assembles the union canonical state.  The `≈`-vs-literal obstruction is fully confined to the transport. -/
theorem rga_eqJoin_of_residualLit_NF
    (W : op_t → concrete_st → Prop) (hRes : RgaEqJoinResidualLit W) :
    EqJoinLemma3C_NF RGACondSig' rgaEqEquiv' W := by
  intro vis events ev₁ ev₂ s₀ s₁ s₂ hI0 hI1 hI2 htr hir hdts hev1 hev2 hcl1 hcl2 hcs0 hcs1 hcs2
  obtain ⟨ρ₀, h₀p, h₀r, hnf₀, hfold0⟩ := hcs0
  obtain ⟨ρ₁, h₁p, h₁r, hnf₁, hfold1⟩ := hcs1
  obtain ⟨ρ₂, h₂p, h₂r, hnf₂, hfold2⟩ := hcs2
  obtain ⟨π₀, hπp, hπr, hnfπ, hlit⟩ :=
    hRes vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ htr hir hdts hev1 hev2 hcl1 hcl2
      h₀p h₀r hnf₀ h₁p h₁r hnf₁ h₂p h₂r hnf₂
  have hI0' : RGACondSig'.Inv (applySeqR init_st ρ₀) :=
    rga_invCong (rgaEqEquiv'.equiv.symm hfold0) hI0
  have hI1' : RGACondSig'.Inv (applySeqR init_st ρ₁) :=
    rga_invCong (rgaEqEquiv'.equiv.symm hfold1) hI1
  have hI2' : RGACondSig'.Inv (applySeqR init_st ρ₂) :=
    rga_invCong (rgaEqEquiv'.equiv.symm hfold2) hI2
  have hMF : eq (applySeqR (applySeqR init_st ρ₀) π₀) (RGACondSig'.mergeL s₀ s₁ s₂) :=
    mergeFold_transport hI0' hI1' hI2' hI0 hI1 hI2 hfold0 hfold1 hfold2 hlit
  exact isCanonicalStateEqNF_union_of_fold W vis ev₁ ev₂ hcl1 hcl2
    (RGACondSig'.mergeL s₀ s₁ s₂) ρ₀ π₀ h₀p h₀r hπp hπr hnf₀ hnfπ hMF

/-! ## Axiom audit -/

#print axioms rga_eqJoin_of_residualLit_NF

end Sal.ConditionedMRDTs.RGAEqJoinNF
