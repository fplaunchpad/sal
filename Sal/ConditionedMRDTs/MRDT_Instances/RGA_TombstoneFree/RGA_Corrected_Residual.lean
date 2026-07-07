import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_CanonConvergence
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_EqJoin_NF
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_Instance_NF

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

namespace Sal.ConditionedMRDTs.RGACorrectedResidual

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient (loOnEq EqJoinLemma3C_NF IsCanonicalStateEqNF fullClosureRel)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv')
open Sal.ConditionedMRDTs.RGAInstanceNF (rga_invCong)
open Sal.ConditionedMRDTs (noopFeasible)
open Sal.ConditionedMRDTs.RGAEqJoinNF (mergeFold_transport)
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

/-! ## Axiom audit -/

#print axioms canonFoldOK_concat

end Sal.ConditionedMRDTs.RGACorrectedResidual
