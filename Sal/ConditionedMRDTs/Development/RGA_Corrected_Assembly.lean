import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_Corrected_Residual
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_ConditionedConvergence
import Sal.ConditionedMRDTs.Framework.Base.CRDT_TS
import Sal.ConditionedMRDTs.Metatheory.GenericEqQuotient
import Sal.ConditionedMRDTs.Metatheory.GenericEqQuotient_NF
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_CanonConvergence
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_Instance
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_MergeLinearization
import Sal.ConditionedMRDTs.Refutations.UpdateFeasibility_Gate

/-!
# The corrected canonical route — `EqJoinLemma3C_NF` from the CORRECTED leaves

*Additive; modifies no existing file; 0 `sorry`.*

Mirror of `RGA_EqJoin_NF_Assembly` over the corrected residual. The two leaves:

* `hEnum` (corrected) — produce BOTH a delta enum `π₀` carrying the per-event canonical discipline
  from the LCA fold (`CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀` — K1: rehome-tolerant `ChainOK`/`DelOK`,
  NOT the refuted `noopFeasible`) and the LCA's own discipline (`CanonFoldOK [] init_st ρ₀`), AND a
  from-`init` union re-enumeration `ρᵤ` (K2: `listPermOf`/`respects`/`noopFeasible`/`CanonFoldOK`
  from `init_st`).
* `hCanon` (corrected) — merge and δ-fold are both the canonical state of `ρ₀ ++ π₀`, with the
  `CanonFoldOK` premises replacing the refuted `noopFeasible π₀` premise.

The merge=fold identity is `eq_of_canonMatch2` as before; the NEW step is the union-fold
convergence `applySeqR init_st (ρ₀ ++ π₀) ≈ applySeqR init_st ρᵤ` via the proved headline
`RGA_update_convergence_canon` (two disciplined enumerations of the same set fold to equal states),
with `CanonFoldOK [] init_st (ρ₀ ++ π₀)` assembled by `canonFoldOK_concat`. This replaces the old
route's dependence on feasibility at the LCA-first fold — exactly the clause the refutation killed.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGACorrectedResidual

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient (loOnEq EqJoinLemma3C_NF fullClosureRel)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv')
open Sal.ConditionedMRDTs (noopFeasible)
open Sal.ConditionedMRDTs.RGAConditionedConvergence (eq_trans)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonMatch CanonFoldOK eq_of_canonMatch2 RGA_update_convergence_canon)

/-- **`RgaEqJoinResidualLit2` via the corrected canonical route.**  `hEnum` supplies the disciplined
delta enum (K1) and the union re-enumeration (K2); `hCanon` supplies the two `CanonMatch` facts;
merge=fold is `eq_of_canonMatch2`; the union-fold hop is `RGA_update_convergence_canon`. -/
theorem rgaResidualLit2_of_canon (W : op_t → concrete_st → Prop)
    (hEnum : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ : List op_t),
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
        ∃ π₀ ρᵤ : List op_t,
          listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
          respects π₀ (loOnEq rgaEqEquiv' W vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
          CanonFoldOK [] init_st ρ₀ ∧
          CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ ∧
          listPermOf ρᵤ (ev₁ ∪ ev₂) ∧
          respects ρᵤ (loOnEq rgaEqEquiv' W vis (ev₁ ∪ ev₂)) ∧
          noopFeasible RGACondSig' ρᵤ init_st ∧
          CanonFoldOK [] init_st ρᵤ)
    (hCanon : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' W vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        CanonFoldOK [] init_st ρ₀ →
        CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ →
        CanonMatch (ρ₀ ++ π₀)
            (merge (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂))
          ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR init_st ρ₀) π₀)) :
    RgaEqJoinResidualLit2 W := by
  intro vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ htr hir hdts hev1 hev2 hcl1 hcl2
    h₀p h₀r hnf₀ h₁p h₁r hnf₁ h₂p h₂r hnf₂
  obtain ⟨π₀, ρᵤ, hπp, hπr, h₀OK, hπOK, hup, hur, hnfu, huOK⟩ :=
    hEnum vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ htr hir hdts hev1 hev2 hcl1 hcl2
      h₀p h₀r hnf₀ h₁p h₁r hnf₁ h₂p h₂r hnf₂
  obtain ⟨hCMmerge, hCMfold⟩ :=
    hCanon vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ htr hir hdts hev1 hev2 hcl1 hcl2
      h₀p h₁p h₂p hπp hπr h₀OK hπOK
  -- merge = δ-fold, by canonical uniqueness (unchanged)
  have heq1 : eq (merge (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂))
      (applySeqR (applySeqR init_st ρ₀) π₀) :=
    eq_of_canonMatch2 (ρ₀ ++ π₀) (ρ₀ ++ π₀) _ _ (fun _ => Iff.rfl) hCMmerge hCMfold
  -- the union-fold hop: `ρ₀ ++ π₀` and `ρᵤ` are disciplined enums of the same set
  have hcatOK : CanonFoldOK [] init_st (ρ₀ ++ π₀) :=
    canonFoldOK_concat ρ₀ [] init_st π₀ h₀OK hπOK
  have hmem : ∀ o, o ∈ ρ₀ ++ π₀ ↔ o ∈ ρᵤ := by
    intro o
    rw [List.mem_append, h₀p.2 o, hπp.2 o, hup.2 o]
    constructor
    · rintro (h | h)
      · exact Set.mem_union_left _ h.1
      · exact h.1
    · intro h
      by_cases hI : o ∈ ev₁ ∩ ev₂
      · exact Or.inl hI
      · exact Or.inr ⟨h, hI⟩
  have heq2 : eq (applySeqR init_st (ρ₀ ++ π₀)) (applySeqR init_st ρᵤ) :=
    RGA_update_convergence_canon (ρ₀ ++ π₀) ρᵤ hmem hcatOK huOK
  have happ : applySeqR init_st (ρ₀ ++ π₀) = applySeqR (applySeqR init_st ρ₀) π₀ := by
    simp only [applySeqR, List.foldl_append]
  rw [happ] at heq2
  exact ⟨ρᵤ, hup, hur, hnfu, eq_trans _ _ _ heq1 heq2⟩

/-- **`EqJoinLemma3C_NF` for the RGA, via the corrected canonical route.** -/
theorem rga_eqJoinNF_of_canon2 (W : op_t → concrete_st → Prop)
    (hEnum : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ : List op_t),
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
        ∃ π₀ ρᵤ : List op_t,
          listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
          respects π₀ (loOnEq rgaEqEquiv' W vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
          CanonFoldOK [] init_st ρ₀ ∧
          CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ ∧
          listPermOf ρᵤ (ev₁ ∪ ev₂) ∧
          respects ρᵤ (loOnEq rgaEqEquiv' W vis (ev₁ ∪ ev₂)) ∧
          noopFeasible RGACondSig' ρᵤ init_st ∧
          CanonFoldOK [] init_st ρᵤ)
    (hCanon : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' W vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        CanonFoldOK [] init_st ρ₀ →
        CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ →
        CanonMatch (ρ₀ ++ π₀)
            (merge (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂))
          ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR init_st ρ₀) π₀)) :
    EqJoinLemma3C_NF RGACondSig' rgaEqEquiv' W :=
  rga_eqJoin_of_residualLit_NF2 W (rgaResidualLit2_of_canon W hEnum hCanon)

/-! ## Axiom audit -/

#print axioms rgaResidualLit2_of_canon
#print axioms rga_eqJoinNF_of_canon2

end Sal.ConditionedMRDTs.RGACorrectedResidual
