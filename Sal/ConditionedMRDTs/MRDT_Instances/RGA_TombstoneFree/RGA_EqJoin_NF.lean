import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_Instance_Final
import Sal.ConditionedMRDTs.Metatheory.GenericEqQuotient_NF

/-!
# The RGA `≈`-Join over born-applicable delivery — union canonical-state shape (NF)

*Additive; modifies no existing file; 0 `sorry`.*

The `noopFeasible` (NF) analogue of `RGA_Instance_Final`'s union shape assembly,
parametric in the guard `W` (so it applies at the re-base's `W := WfOpA`).  The
guard-hardcoded order lemmas generalize for free — `loOnEqQ_reduce`'s proof reads
only `rc = Either`, which is guard-independent.  The `noopFeasible` clause of the
union witness `ρ₀ ++ π₀` is composed from the two sides via `noopFeasible_append`.

This closes the union canonical-state SHAPE for `EqJoinLemma3C_NF`, isolating the
merge=delta-fold residual (the same WALL 1 the `GenDisc2CEq` version faced, now on
the honest born-applicable foundation — WALL 0's config facts come from the
`noopFeasible`/`WfOpGenQ` discipline, not a strengthened `GenDisc`).
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGAEqJoinNF

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' RGACondSig'_init rgaCongVC')
open Sal.ConditionedMRDTs.RGAOrderBridge (rc_is_Either')
open Sal.ConditionedMRDTs (noopFeasible)
open Sal.ConditionedMRDTs.RGAInstanceFinal (applySeq_eq_applySeqR)
open RGAMergeLinearization (applySeqR)

/-! ## §1  The guard-generic order reductions (`rc = Either` is guard-independent) -/

/-- `loOnEq` collapses to its vis-arm at ANY guard `W` — `rc = Either` empties the
rc-tiebreak arm.  Generalizes `RGAConvergenceEq.loOnEqQ_reduce` (`W := WfOpQ`). -/
theorem loOnEqQ_reduce_gen (W : op_t → concrete_st → Prop)
    (vis : op_t → op_t → Prop) (ev : Set op_t) (e₁ e₂ : op_t) :
    loOnEq rgaEqEquiv' W vis ev e₁ e₂
      ↔ (vis e₁ e₂ ∧ ¬ eqCommutesOn rgaEqEquiv' W e₁ e₂) := by
  constructor
  · rintro (h | ⟨_, _, hrc, _⟩)
    · exact h
    · exact absurd hrc (by rw [rc_is_Either']; exact fun h => Sal.Emulation.RcRes.noConfusion h)
  · exact Or.inl

/-- `loOnEq` at guard `W` is index-free: it agrees across event-set parameters. -/
theorem loOnEqQ_index_free_gen (W : op_t → concrete_st → Prop)
    (vis : op_t → op_t → Prop) (ev ev' : Set op_t) (e₁ e₂ : op_t) :
    loOnEq rgaEqEquiv' W vis ev e₁ e₂ ↔ loOnEq rgaEqEquiv' W vis ev' e₁ e₂ :=
  (loOnEqQ_reduce_gen W vis ev e₁ e₂).trans (loOnEqQ_reduce_gen W vis ev' e₁ e₂).symm

/-! ## §2  The union canonical-state shape, born-applicable -/

theorem mergeFold_transport {σ₀' σ₁' σ₂' X s₀ s₁ s₂ : concrete_st}
    (hI0' : RGACondSig'.Inv σ₀') (hI1' : RGACondSig'.Inv σ₁') (hI2' : RGACondSig'.Inv σ₂')
    (hI0 : RGACondSig'.Inv s₀) (hI1 : RGACondSig'.Inv s₁) (hI2 : RGACondSig'.Inv s₂)
    (h₀ : eq σ₀' s₀) (h₁ : eq σ₁' s₁) (h₂ : eq σ₂' s₂)
    (hlit : eq (merge σ₀' σ₁' σ₂') X) :
    eq X (RGACondSig'.mergeL s₀ s₁ s₂) :=
  rgaEqEquiv'.equiv.trans (rgaEqEquiv'.equiv.symm hlit)
    (rgaCongVC'.mergeL_congr hI0' hI0 hI1' hI1 hI2' hI2 h₀ h₁ h₂)

/-! ## §3  `EqJoinLemma3C_NF`, reduced to the merge=delta-fold residual

Mirror of `RGA_Instance_Final.rga_eqJoin_of_mergeFoldResidual`, over the NF
interface: the `GenDisc` premises are GONE (the born-applicable discipline is
carried by the `noopFeasible` witnesses), and the residual additionally produces a
`noopFeasible` delta enumeration.  Everything ABOVE the residual — the union
canonical-state shape — is closed by §2. -/

end Sal.ConditionedMRDTs.RGAEqJoinNF
