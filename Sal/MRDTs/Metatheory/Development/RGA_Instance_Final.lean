import Sal.MRDTs.Metatheory.Development.RGA_ConvergenceEq

/-!
# The RGA capstone, over `WfOpQ` — assembly + the honestly-pinned Join residual

*Additive; modifies no existing file; 0 `sorry`.*

`RGA_Instance.lean` threaded TWO hypotheses into its capstone: `hP : InvPres
RGACondSig' WfOp` (§5, unprovable at `WfOp`) and `hJoinEq` (§7, blocked on the
`loOnA`/`loOnEq` order mismatch and the merge `hin` residual).  Since then:
`RGA_InvUpdateQ` closed the FULL `InvPres` at the strengthened guard `WfOpQ`
(`rgaInvPresQ`, with `rga_wfOpReachableQ` at `WfOpGenQ`), `RGA_ConvergenceEq`
re-derived convergence over the framework's own order `loOnEq rgaEqEquiv' WfOpQ`
(no order mismatch left), and `RGA_HinFilterEq` closed the merge bridge's `hin`.

This file re-bases the whole wiring on `WfOpQ`:

* **§1** `rgaInvInvVCQ : InvInvVC RGACondSig' rgaEqEquiv' WfOpQ` — `WfOp`'s
  `wf_congr` re-proved for the strengthened guard (its extra conjuncts are
  `resolve`-driven, hence `≈`-invariant via `resolve_dom_eq`).
* **§2** raw folds of `Nodup`/distinct-ts/`WfOpGenQ` enumerations carry `qInv`
  (`qInv_fold`), seating merge congruence at fold states.
* **§3** the **union adapter** `isCanonicalStateEq_union_of_fold`:
  `IsCanonicalStateEq`'s ∃/order shape IS reachable from a merge-fold fact —
  prefix the LCA enumeration, use `loOnEqQ_reduce` (the RGA's `loOnEq` is
  index-free) and full closure (no `loOnEq`-edge points from the delta back
  into the LCA set).  The shape match is CLEAN; no order translation remains.
* **§4** `rga_eqJoin_of_oracle` — the `≈`-Join with THREE premises beyond
  `EqJoinLemma3C`'s signature: distinct timestamps on `ev₁ ∪ ev₂`, `WfOpGenQ`
  on `ev₁ ∪ ev₂`, and `MergeFoldOracle` (the merge-fold identity
  `eq_merge_two_sided_eq` would discharge given its `hD`/`hB`/`hBE`/`hcm`/
  `hbridge`/`hMSR` package).  These pin EXACTLY what still separates the RGA
  from the unconditioned `EqJoinLemma3C` — see the STATUS block.
* **§5** the capstone `RGA_is_RA_linearizable`, `RA_linearizable_up_to_eq`
  wired with the five CONCRETE `WfOpQ`-VCs; `hJoinEq` is its one remaining
  non-execution hypothesis.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGAInstanceFinal

open Sal.Emulation
open Sal.Metatheory.GenericEqQuotient
open Sal.Metatheory.RGAInstance (RGACondSig' rgaEqEquiv' rgaCongVC'
  rga_inv_init' RGACondSig'_update RGACondSig'_mergeL RGACondSig'_init)
open Sal.Metatheory.RGAInvUpdateQ (WfOpQ WfOpGenQ rgaInvPresQ rga_wfOpReachableQ)
open Sal.Metatheory.RGAConvergenceEq (loOnEqQ_reduce)
open RGAMergeLinearization (applySeqR)

/-! ## §1  `InvInvVC` over the strengthened guard `WfOpQ`

`RGA_Instance.rgaInvInvVC'` is stated at `W := WfOp`; the metatheorem must be
instantiated at ONE `W` throughout, and `InvPres` only exists at `WfOpQ`.  The
`Ins` extra (`resolve s (a :: pre) < t`) and the `Del` extras (`resolve`-valued)
descend through `≈` exactly like `WfOp`'s conjuncts: `contains` via `(h t).1`,
`resolve` via `resolve_dom_eq`. -/

/-- `InvInvVC RGACondSig' rgaEqEquiv' WfOpQ` — full, both fields. -/
theorem rgaInvInvVCQ : InvInvVC RGACondSig' rgaEqEquiv' WfOpQ where
  wf_congr := by
    intro o s s' _ _ h
    obtain ⟨t, r, ao⟩ := o
    cases ao with
    | Ins e pre a =>
      show ((t ≠ 0 ∧ contains s t = false) ∧ resolve s (a :: pre) < t)
        ↔ ((t ≠ 0 ∧ contains s' t = false) ∧ resolve s' (a :: pre) < t)
      rw [(h t).1, resolve_dom_eq s s' (a :: pre) (fun c _ => (h c).1)]
    | Del pre x =>
      show (resolve s pre ≠ x ∧ (resolve s pre = 0 ∨ resolve s pre < x))
        ↔ (resolve s' pre ≠ x ∧ (resolve s' pre = 0 ∨ resolve s' pre < x))
      rw [resolve_dom_eq s s' pre (fun c _ => (h c).1)]
  applicable_congr := by
    intro o s s' _ _ h
    exact and_congr (RGAEqQuotient.accurate_eq_iff o h)
      (RGAEqQuotient.fresh_ts_eq_iff o h)

#print axioms rgaInvInvVCQ

/-! ## §2  `qInv` at raw folds of genuine enumerations -/

/-- The framework's `applySeq` on `RGACondSig'` IS the RGA's raw `applySeqR`. -/
theorem applySeq_eq_applySeqR (s : concrete_st) (ρ : List op_t) :
    applySeq RGACondSig'.toCRDTSig s ρ = applySeqR s ρ := by
  induction ρ generalizing s with
  | nil => rfl
  | cons o ρ ih => exact ih (do_ s o)

/-- Raw folds of `Nodup`, distinct-ts, `WfOpGenQ` enumerations land in `qInv`:
`rga_wfOpReachableQ` seats `WfOpQ` at every prefix, `rgaInvPresQ` steps. -/
theorem qInv_fold (ρ : List op_t) (hnd : ρ.Nodup)
    (hts : ∀ a ∈ ρ, ∀ b ∈ ρ, a ≠ b → Op.time a ≠ Op.time b)
    (hgen : ∀ o ∈ ρ, WfOpGenQ o) :
    RGACondSig'.Inv (applySeqR init_st ρ) := by
  have h := rgaInvPresQ.inv_applySeq_of_wfChain rga_inv_init'
    (rga_wfOpReachableQ ρ hnd hts hgen)
  rwa [applySeq_eq_applySeqR] at h

#print axioms qInv_fold

/-! ## §3  The union adapter: `IsCanonicalStateEq`'s ∃/order shape is CLEAN

`IsCanonicalStateEq … (ev₁ ∪ ev₂) m` demands ONE `loOnEq`-respecting
enumeration of the union folding raw from `init_st` to `≈ m`.  Given the LCA
enumeration `ρ₀` (of `ev₁ ∩ ev₂`) and a delta enumeration `π₀` whose continued
fold is `≈ m`, the witness is literally `ρ₀ ++ π₀`:

* `loOnEq rgaEqEquiv' WfOpQ` is INDEX-FREE (`loOnEqQ_reduce`: `rc ≡ Either`
  empties the tiebreak arm), so `respects` transports across event-set indexes;
* full closure of `ev₁`/`ev₂` kills every cross edge — a `loOnEq`-edge is a
  vis-edge, and a vis-edge from the delta into the LCA set would pull the delta
  event into `ev₁ ∩ ev₂`.

No order translation, no re-enumeration: the shape match is clean. -/

/-- `loOnEq rgaEqEquiv' WfOpQ` does not read its event-set index. -/
theorem loOnEqQ_index_free (vis : op_t → op_t → Prop) (ev ev' : Set op_t)
    (e₁ e₂ : op_t) :
    loOnEq rgaEqEquiv' WfOpQ vis ev e₁ e₂
      ↔ loOnEq rgaEqEquiv' WfOpQ vis ev' e₁ e₂ :=
  (loOnEqQ_reduce vis ev e₁ e₂).trans (loOnEqQ_reduce vis ev' e₁ e₂).symm

/-- **The union adapter.**  From the LCA enumeration, a delta enumeration, and
the merge-fold fact, the union's canonical-state shape follows. -/
theorem isCanonicalStateEq_union_of_fold
    (vis : op_t → op_t → Prop) (ev₁ ev₂ : Set op_t)
    (hcl₁ : fullClosureRel (D := RGACondSig') vis ev₁)
    (hcl₂ : fullClosureRel (D := RGACondSig') vis ev₂)
    (m : concrete_st) (ρ₀ π₀ : List op_t)
    (h₀p : listPermOf ρ₀ (ev₁ ∩ ev₂))
    (h₀r : respects ρ₀ (loOnEq rgaEqEquiv' WfOpQ vis (ev₁ ∩ ev₂)))
    (hπp : listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)))
    (hπr : respects π₀ (loOnEq rgaEqEquiv' WfOpQ vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))))
    (hMF : eq (applySeqR (applySeqR init_st ρ₀) π₀) m) :
    IsCanonicalStateEq rgaEqEquiv' WfOpQ vis (ev₁ ∪ ev₂) m := by
  have hmemρ : ∀ a ∈ ρ₀, a ∈ ev₁ ∩ ev₂ := fun a ha => (h₀p.2 a).mp ha
  have hmemπ : ∀ a ∈ π₀, a ∈ (ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂) :=
    fun a ha => (hπp.2 a).mp ha
  refine ⟨ρ₀ ++ π₀, ⟨?_, ?_⟩, ?_, ?_⟩
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
        (fun a b => loOnEqQ_index_free vis (ev₁ ∩ ev₂) (ev₁ ∪ ev₂) a b)).mp h₀r
    · exact (respects_congr
        (fun a b => loOnEqQ_index_free vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))
          (ev₁ ∪ ev₂) a b)).mp hπr
    · intro a ha b hb hR
      have hva := ((loOnEqQ_reduce vis (ev₁ ∪ ev₂) b a).mp hR).1
      have haI := hmemρ a ha
      exact (hmemπ b hb).2 ⟨hcl₁ b a hva haI.1, hcl₂ b a hva haI.2⟩
  · show rgaEqEquiv'.eqv
      (applySeq RGACondSig'.toCRDTSig RGACondSig'.init (ρ₀ ++ π₀)) m
    have hsplit : applySeq RGACondSig'.toCRDTSig RGACondSig'.init (ρ₀ ++ π₀)
        = applySeqR (applySeqR init_st ρ₀) π₀ := by
      rw [applySeq_eq_applySeqR, RGACondSig'_init]
      simp only [applySeqR, List.foldl_append]
    rw [hsplit]
    exact hMF

#print axioms isCanonicalStateEq_union_of_fold

end Sal.Metatheory.RGAInstanceFinal
