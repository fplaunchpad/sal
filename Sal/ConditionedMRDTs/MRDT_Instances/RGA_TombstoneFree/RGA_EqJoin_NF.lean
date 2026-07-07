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

/-- **The NF union adapter.**  From the LCA enumeration `ρ₀`, a delta enumeration
`π₀`, the merge-fold fact `hMF`, AND the two sides' `noopFeasible` (`ρ₀` from
`init`, `π₀` from the LCA fold), the union's born-applicable canonical-state shape
follows.  The `IsCanonicalStateEq` shape is exactly `RGA_Instance_Final`'s; the new
content is the `noopFeasible` clause of `ρ₀ ++ π₀` via `noopFeasible_append`. -/
theorem isCanonicalStateEqNF_union_of_fold
    (W : op_t → concrete_st → Prop)
    (vis : op_t → op_t → Prop) (ev₁ ev₂ : Set op_t)
    (hcl₁ : fullClosureRel (D := RGACondSig') vis ev₁)
    (hcl₂ : fullClosureRel (D := RGACondSig') vis ev₂)
    (m : concrete_st) (ρ₀ π₀ : List op_t)
    (h₀p : listPermOf ρ₀ (ev₁ ∩ ev₂))
    (h₀r : respects ρ₀ (loOnEq rgaEqEquiv' W vis (ev₁ ∩ ev₂)))
    (hπp : listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)))
    (hπr : respects π₀ (loOnEq rgaEqEquiv' W vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))))
    (hnf₀ : noopFeasible RGACondSig' ρ₀ init_st)
    (hnfπ : noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀))
    (hMF : eq (applySeqR (applySeqR init_st ρ₀) π₀) m) :
    IsCanonicalStateEqNF rgaEqEquiv' W vis (ev₁ ∪ ev₂) m := by
  have hmemρ : ∀ a ∈ ρ₀, a ∈ ev₁ ∩ ev₂ := fun a ha => (h₀p.2 a).mp ha
  have hmemπ : ∀ a ∈ π₀, a ∈ (ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂) :=
    fun a ha => (hπp.2 a).mp ha
  refine ⟨ρ₀ ++ π₀, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · refine List.nodup_append.mpr ⟨h₀p.1, hπp.1, ?_⟩
    intro a ha b hb heq
    exact (hmemπ b hb).2 (heq ▸ hmemρ a ha)
  · intro a
    constructor
    · intro ha
      rcases List.mem_append.mp ha with h | h
      · exact Set.mem_union_left _ (hmemρ a h).1
      · exact (hmemπ a h).1
    · intro ha
      by_cases hI : a ∈ ev₁ ∩ ev₂
      · exact List.mem_append.mpr (Or.inl ((h₀p.2 a).mpr hI))
      · exact List.mem_append.mpr (Or.inr ((hπp.2 a).mpr ⟨ha, hI⟩))
  · refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
    · exact (respects_congr
        (fun a b => loOnEqQ_index_free_gen W vis (ev₁ ∩ ev₂) (ev₁ ∪ ev₂) a b)).mp h₀r
    · exact (respects_congr
        (fun a b => loOnEqQ_index_free_gen W vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))
          (ev₁ ∪ ev₂) a b)).mp hπr
    · intro a ha b hb hR
      have hva := ((loOnEqQ_reduce_gen W vis (ev₁ ∪ ev₂) b a).mp hR).1
      have haI := hmemρ a ha
      exact (hmemπ b hb).2 ⟨hcl₁ b a hva haI.1, hcl₂ b a hva haI.2⟩
  · -- the born-applicable clause: `ρ₀ ++ π₀` is `noopFeasible` from `init`
    refine noopFeasible_append hnf₀ ?_
    show noopFeasible RGACondSig' π₀ (applySeq RGACondSig'.toCRDTSig RGACondSig'.init ρ₀)
    rw [applySeq_eq_applySeqR, RGACondSig'_init]
    exact hnfπ
  · show rgaEqEquiv'.eqv
      (applySeq RGACondSig'.toCRDTSig RGACondSig'.init (ρ₀ ++ π₀)) m
    have hsplit : applySeq RGACondSig'.toCRDTSig RGACondSig'.init (ρ₀ ++ π₀)
        = applySeqR (applySeqR init_st ρ₀) π₀ := by
      rw [applySeq_eq_applySeqR, RGACondSig'_init]
      simp only [applySeqR, List.foldl_append]
    rw [hsplit]
    exact hMF

/-! ## §2.5  The `≈`-vs-literal reconciliation (`mergeFold_transport`)

The merge machinery (`eq_merge_two_sided_final`) needs the branches as LITERAL folds; the framework
supplies them only up to `≈`.  The born-applicable re-base resolves this: run the machinery on the
literal born-applicable folds `σ_i' ≈ s_i`, then transport to the `≈`-classes `s₀ s₁ s₂` by ONE
`merge`-congruence step.  This lemma is that transport — it confines the entire `≈`-vs-literal tension
to `mergeL_congr`.  See `WALL1_ANALYSIS.md`. -/

/-- **Transport the literal merge=fold to the `≈`-classes.**  Given the merge=fold identity for the
LITERAL folds `σ₀'/σ₁'/σ₂'` and `σ_i' ≈ s_i`, the same fold `X` equals `mergeL s₀ s₁ s₂` — because
`merge` is `≈`-congruent (`rgaCongVC'.mergeL_congr`). -/
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

/-- **The NF `≈`-Join residual.**  From the LCA enumeration `ρ₀` (with its
`noopFeasible`) and the two sides' born-applicable canonical states, a
`loOnEq`-respecting, `noopFeasible` delta enumeration `π₀` of the symmetric-
difference whose continued fold from `ρ₀` is `≈ mergeL`.  The merge=delta-fold
bridge, now carrying feasibility. -/
def RgaEqJoinResidual_NF (W : op_t → concrete_st → Prop) : Prop :=
  ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t)
    (s₀ s₁ s₂ : concrete_st) (ρ₀ : List op_t),
    RGACondSig'.Inv s₀ → RGACondSig'.Inv s₁ → RGACondSig'.Inv s₂ →
    (∀ {a b c : op_t}, vis a b → vis b c → vis a c) →
    (∀ a : op_t, ¬ vis a a) →
    (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
    fullClosureRel (D := RGACondSig') vis ev₁ →
    fullClosureRel (D := RGACondSig') vis ev₂ →
    listPermOf ρ₀ (ev₁ ∩ ev₂) →
    respects ρ₀ (loOnEq rgaEqEquiv' W vis (ev₁ ∩ ev₂)) →
    noopFeasible RGACondSig' ρ₀ init_st →
    IsCanonicalStateEqNF rgaEqEquiv' W vis ev₁ s₁ →
    IsCanonicalStateEqNF rgaEqEquiv' W vis ev₂ s₂ →
    ∃ π₀ : List op_t,
      listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
      respects π₀ (loOnEq rgaEqEquiv' W vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
      noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀) ∧
      eq (applySeqR (applySeqR init_st ρ₀) π₀) (RGACondSig'.mergeL s₀ s₁ s₂)

/-- **`EqJoinLemma3C_NF` from the NF residual.**  The union canonical-state shape
(§2) closes everything except `RgaEqJoinResidual_NF`.  No `GenDisc`, no
`GDSupply` — the born-applicable `noopFeasible` witnesses carry the discipline the
`GenDisc2CEq`-route needed a strengthened generation discipline for (WALL 0). -/
theorem rga_eqJoin_of_mergeFoldResidual_NF
    (W : op_t → concrete_st → Prop) (hRes : RgaEqJoinResidual_NF W) :
    EqJoinLemma3C_NF RGACondSig' rgaEqEquiv' W := by
  intro vis events ev₁ ev₂ s₀ s₁ s₂ hI0 hI1 hI2 htr hir _hdts hev1 hev2 hcl1 hcl2
    hcs0 hcs1 hcs2
  obtain ⟨ρ₀, h₀p, h₀r, hnf₀, _hfold0⟩ := hcs0
  obtain ⟨π₀, hπp, hπr, hnfπ, hMF⟩ :=
    hRes vis events ev₁ ev₂ s₀ s₁ s₂ ρ₀ hI0 hI1 hI2 htr hir hev1 hev2
      hcl1 hcl2 h₀p h₀r hnf₀ hcs1 hcs2
  exact isCanonicalStateEqNF_union_of_fold W vis ev₁ ev₂ hcl1 hcl2
    (RGACondSig'.mergeL s₀ s₁ s₂) ρ₀ π₀ h₀p h₀r hπp hπr hnf₀ hnfπ hMF

/-! ## §4  Axiom audit -/

#print axioms loOnEqQ_reduce_gen
#print axioms loOnEqQ_index_free_gen
#print axioms isCanonicalStateEqNF_union_of_fold
#print axioms rga_eqJoin_of_mergeFoldResidual_NF

end Sal.ConditionedMRDTs.RGAEqJoinNF
