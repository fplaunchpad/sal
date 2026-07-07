import Sal.MRDTs.Metatheory.Conditioned.RGA_CanonConvergence
import Sal.MRDTs.Metatheory.Conditioned.RGA_EqJoin_NF
import Sal.MRDTs.Metatheory.Conditioned.RGA_Instance_NF

/-!
# The CORRECTED literal-fold residual — union re-enumerability instead of `noopFeasible π₀`

*Additive; modifies no existing file; 0 `sorry`.*

`RGA_HEnum_Refutation` proved the old residual shape unsatisfiable: `noopFeasible π₀` from the LCA
fold is impossible when an LCA delete is concurrent with a delta insert anchored on the deleted node
(the LCA-first shape `ρ₀ ++ π₀` pre-applies the kill; no ordering freedom within `π₀` can undo it).

The corrected residual replaces that clause with the natural induction invariant: **the merged state
is reachable by an honest (born-applicable) from-`init` delivery of the union** —

* `RgaEqJoinResidualLit2` — from the three born-applicable deliveries, produce `ρᵤ` enumerating
  `ev₁ ∪ ev₂`, `loOnEq`-respecting, `noopFeasible` from `init_st` (from-init there IS enough freedom:
  rehome-affected inserts can be delivered before their concurrent anchor-kills), whose fold equals
  the merge of the three literal folds.
* `rga_eqJoin_of_residualLit_NF2` — the corrected residual still discharges `EqJoinLemma3C_NF`
  verbatim: `ρᵤ` itself is the union's `IsCanonicalStateEqNF` witness (the old assembly's only use of
  `noopFeasible π₀` was to build that witness as `ρ₀ ++ π₀`).
* `canonFoldOK_concat` — the general two-list composition of the per-event discipline
  (`CanonFoldOK F s π₁` then `CanonFoldOK` continued from the prefix fold), the engine-side glue the
  corrected skeleton uses to run `canon_fold` mid-stream from the LCA.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGACorrectedResidual

open Sal.Emulation
open Sal.Metatheory.GenericEqQuotient (loOnEq EqJoinLemma3C_NF IsCanonicalStateEqNF fullClosureRel)
open Sal.Metatheory.RGAInstance (RGACondSig' rgaEqEquiv')
open Sal.Metatheory.RGAInstanceNF (rga_invCong)
open Sal.Metatheory.UpdateFeasibilityGate (noopFeasible)
open Sal.Metatheory.RGAEqJoinNF (mergeFold_transport)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonFoldOK CanonStepOK)

/-- **`CanonFoldOK` composes across concatenation.**  The per-event discipline along `π₁` from
`(F, s)`, continued along `π₂` from the extended prefix `(F ++ π₁, applySeqR s π₁)`, is the
discipline along `π₁ ++ π₂` from `(F, s)`.  The engine-side glue for running `canon_fold` from the
LCA fold: `CanonFoldOK [] init ρ₀` + `CanonFoldOK ρ₀ (fold ρ₀) π₀` ⟹ `CanonFoldOK [] init (ρ₀ ++ π₀)`. -/
theorem canonFoldOK_concat :
    ∀ (π₁ F : List op_t) (s : concrete_st) (π₂ : List op_t),
      CanonFoldOK F s π₁ → CanonFoldOK (F ++ π₁) (applySeqR s π₁) π₂ →
      CanonFoldOK F s (π₁ ++ π₂) := by
  intro π₁
  induction π₁ with
  | nil =>
    intro F s π₂ _ h2
    rw [List.append_nil] at h2
    exact h2
  | cons o rest ih =>
    intro F s π₂ h1 h2
    obtain ⟨hstep, hrest⟩ := h1
    refine ⟨hstep, ih (F ++ [o]) (do_ s o) π₂ hrest ?_⟩
    rw [show (F ++ [o]) ++ rest = F ++ o :: rest from by simp]
    exact h2

/-- **The corrected literal-fold merge residual.**  From the three born-applicable deliveries `ρ₀`
(LCA), `ρ₁`/`ρ₂` (branches), produce a `loOnEq`-respecting, from-`init` `noopFeasible` enumeration
`ρᵤ` of the UNION whose fold equals the RGA `merge` of the three literal folds.  The refuted
`noopFeasible π₀ (applySeqR init_st ρ₀)` clause is GONE — nothing is required to be born-applicable
at the LCA-first fold. -/
def RgaEqJoinResidualLit2 (W : op_t → concrete_st → Prop) : Prop :=
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
    ∃ ρᵤ : List op_t,
      listPermOf ρᵤ (ev₁ ∪ ev₂) ∧
      respects ρᵤ (loOnEq rgaEqEquiv' W vis (ev₁ ∪ ev₂)) ∧
      noopFeasible RGACondSig' ρᵤ init_st ∧
      eq (merge (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂))
        (applySeqR init_st ρᵤ)

/-- **`EqJoinLemma3C_NF` from the corrected residual.**  Mirror of
`rga_eqJoin_of_residualLit_NF`, with `ρᵤ` itself as the union's `IsCanonicalStateEqNF` witness —
no `ρ₀ ++ π₀` assembly, no `noopFeasible_append`, no feasibility at the LCA-first fold. -/
theorem rga_eqJoin_of_residualLit_NF2
    (W : op_t → concrete_st → Prop) (hRes : RgaEqJoinResidualLit2 W) :
    EqJoinLemma3C_NF RGACondSig' rgaEqEquiv' W := by
  intro vis events ev₁ ev₂ s₀ s₁ s₂ hI0 hI1 hI2 htr hir hdts hev1 hev2 hcl1 hcl2 hcs0 hcs1 hcs2
  obtain ⟨ρ₀, h₀p, h₀r, hnf₀, hfold0⟩ := hcs0
  obtain ⟨ρ₁, h₁p, h₁r, hnf₁, hfold1⟩ := hcs1
  obtain ⟨ρ₂, h₂p, h₂r, hnf₂, hfold2⟩ := hcs2
  obtain ⟨ρᵤ, hup, hur, hnfu, hlit⟩ :=
    hRes vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ htr hir hdts hev1 hev2 hcl1 hcl2
      h₀p h₀r hnf₀ h₁p h₁r hnf₁ h₂p h₂r hnf₂
  have hI0' : RGACondSig'.Inv (applySeqR init_st ρ₀) :=
    rga_invCong (rgaEqEquiv'.equiv.symm hfold0) hI0
  have hI1' : RGACondSig'.Inv (applySeqR init_st ρ₁) :=
    rga_invCong (rgaEqEquiv'.equiv.symm hfold1) hI1
  have hI2' : RGACondSig'.Inv (applySeqR init_st ρ₂) :=
    rga_invCong (rgaEqEquiv'.equiv.symm hfold2) hI2
  have hMF : eq (applySeqR init_st ρᵤ) (RGACondSig'.mergeL s₀ s₁ s₂) :=
    mergeFold_transport hI0' hI1' hI2' hI0 hI1 hI2 hfold0 hfold1 hfold2 hlit
  exact ⟨ρᵤ, hup, hur, hnfu, hMF⟩

/-! ## Axiom audit -/

#print axioms canonFoldOK_concat
#print axioms rga_eqJoin_of_residualLit_NF2

end Sal.Metatheory.RGACorrectedResidual
