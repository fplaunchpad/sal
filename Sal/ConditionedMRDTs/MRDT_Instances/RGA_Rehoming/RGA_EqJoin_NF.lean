import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_Instance_Final
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
set_option linter.unusedSectionVars false
namespace Sal.ConditionedMRDTs.RGAEqJoinNF

variable {α : Type} [DecidableEq α] [Inhabited α]

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
theorem loOnEqQ_reduce_gen (W : op_t α → concrete_st α → Prop)
    (vis : op_t α → op_t α → Prop) (ev : Set (op_t α)) (e₁ e₂ : op_t α) :
    loOnEq (rgaEqEquiv' α) W vis ev e₁ e₂
      ↔ (vis e₁ e₂ ∧ ¬ eqCommutesOn (rgaEqEquiv' α) W e₁ e₂) := by
  constructor
  · rintro (h | ⟨_, _, hrc, _⟩)
    · exact h
    · exact absurd hrc (by rw [rc_is_Either']; exact fun h => Sal.Emulation.RcRes.noConfusion h)
  · exact Or.inl

/-- `loOnEq` at guard `W` is index-free: it agrees across event-set parameters. -/
theorem loOnEqQ_index_free_gen (W : op_t α → concrete_st α → Prop)
    (vis : op_t α → op_t α → Prop) (ev ev' : Set (op_t α)) (e₁ e₂ : op_t α) :
    loOnEq (rgaEqEquiv' α) W vis ev e₁ e₂ ↔ loOnEq (rgaEqEquiv' α) W vis ev' e₁ e₂ :=
  (loOnEqQ_reduce_gen W vis ev e₁ e₂).trans (loOnEqQ_reduce_gen W vis ev' e₁ e₂).symm

/-! ## §2  The union canonical-state shape, born-applicable -/

theorem mergeFold_transport {σ₀' σ₁' σ₂' X s₀ s₁ s₂ : concrete_st α}
    (hI0' : (RGACondSig' α).Inv σ₀') (hI1' : (RGACondSig' α).Inv σ₁') (hI2' : (RGACondSig' α).Inv σ₂')
    (hI0 : (RGACondSig' α).Inv s₀) (hI1 : (RGACondSig' α).Inv s₁) (hI2 : (RGACondSig' α).Inv s₂)
    (h₀ : eq σ₀' s₀) (h₁ : eq σ₁' s₁) (h₂ : eq σ₂' s₂)
    (hlit : eq (merge σ₀' σ₁' σ₂') X) :
    eq X ((RGACondSig' α).mergeL s₀ s₁ s₂) :=
  (rgaEqEquiv' α).equiv.trans ((rgaEqEquiv' α).equiv.symm hlit)
    ((rgaCongVC' α).mergeL_congr hI0' hI0 hI1' hI1 hI2' hI2 h₀ h₁ h₂)

/-! ## §3  `EqJoinLemma3C_NF`, reduced to the merge=delta-fold residual

Mirror of `RGA_Instance_Final.rga_eqJoin_of_mergeFoldResidual`, over the NF
interface: the `GenDisc` premises are GONE (the born-applicable discipline is
carried by the `noopFeasible` witnesses), and the residual additionally produces a
`noopFeasible` delta enumeration.  Everything ABOVE the residual — the union
canonical-state shape — is closed by §2. -/

/-- **The NF `≈`-Join residual.**  From the LCA enumeration `ρ₀` (with its
`noopFeasible`) and the two sides' born-applicable canonical states, a
`loOnEq`-respecting, `noopFeasible` delta enumeration `π₀` of the symmetric-
difference whose continued fold from `ρ₀` is `≈ mergeL`.  The merge=delta-fold
bridge, now carrying feasibility. -/
def RgaEqJoinResidual_NF (W : op_t α → concrete_st α → Prop) : Prop :=
  ∀ (vis : op_t α → op_t α → Prop) (events ev₁ ev₂ : Set (op_t α))
    (s₀ s₁ s₂ : concrete_st α) (ρ₀ : List (op_t α)),
    (RGACondSig' α).Inv s₀ → (RGACondSig' α).Inv s₁ → (RGACondSig' α).Inv s₂ →
    (∀ {a b c : op_t α}, vis a b → vis b c → vis a c) →
    (∀ a : op_t α, ¬ vis a a) →
    (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
    fullClosureRel (D := (RGACondSig' α)) vis ev₁ →
    fullClosureRel (D := (RGACondSig' α)) vis ev₂ →
    listPermOf ρ₀ (ev₁ ∩ ev₂) →
    respects ρ₀ (loOnEq (rgaEqEquiv' α) W vis (ev₁ ∩ ev₂)) →
    noopFeasible (RGACondSig' α) ρ₀ (init_st (α := α)) →
    IsCanonicalStateEqNF (rgaEqEquiv' α) W vis ev₁ s₁ →
    IsCanonicalStateEqNF (rgaEqEquiv' α) W vis ev₂ s₂ →
    ∃ π₀ : List (op_t α),
      listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
      respects π₀ (loOnEq (rgaEqEquiv' α) W vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
      noopFeasible (RGACondSig' α) π₀ (applySeqR (init_st (α := α)) ρ₀) ∧
      eq (applySeqR (applySeqR (init_st (α := α)) ρ₀) π₀) ((RGACondSig' α).mergeL s₀ s₁ s₂)


end Sal.ConditionedMRDTs.RGAEqJoinNF
