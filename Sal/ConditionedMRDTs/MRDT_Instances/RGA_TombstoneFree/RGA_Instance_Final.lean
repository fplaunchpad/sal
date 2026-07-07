import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_ConvergenceEq

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

namespace Sal.ConditionedMRDTs.RGAInstanceFinal

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' rgaCongVC'
  rga_inv_init' RGACondSig'_update RGACondSig'_mergeL RGACondSig'_init)
open Sal.ConditionedMRDTs.RGAInvUpdateQ (WfOpQ WfOpGenQ rgaInvPresQ rga_wfOpReachableQ)
open Sal.ConditionedMRDTs.RGAConvergenceEq (loOnEqQ_reduce)
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

/-! ## §4  The `≈`-Join `EqJoinLemma3C`, reduced to the merge=delta-fold residual

`EqJoinLemma3C RGACondSig' rgaEqEquiv' WfOpQ GenDisc` (its NEW `GenDisc`-carrying
form, GenericEqQuotient §4) demands `IsCanonicalStateEq (ev₁∪ev₂) (mergeL s₀ s₁ s₂)`
from the three side canonical states, full closure, and `GenDisc` on the two sides
and their union.  §3's `isCanonicalStateEq_union_of_fold` already discharges the
ENTIRE `IsCanonicalStateEq` *shape* assembly (nodup/perm of `ρ₀ ++ π₀`, the
`respects` append via `loOnEqQ_index_free` + full-closure cross-edge kill, the raw
`foldl_append` split) from ONE merge-fold fact `hMF`.  So the join reduces to
producing, from the LCA enumeration `ρ₀` (extracted from the intersection-side
canonical state), a `loOnEq`-respecting delta enumeration `π₀` of
`(ev₁∪ev₂)\(ev₁∩ev₂)` whose continued fold from the LCA-fold rep is `≈ mergeL`.

`RgaEqJoinResidual` names EXACTLY that remaining content.  Everything ABOVE it —
the union canonical-state shape — is closed here; nothing below it is smuggled in.
See the STATUS block for why the residual is not (yet) discharge-able from
`EqJoinLemma3C`'s hypotheses with the current swap-free machinery. -/

/-- **The precisely-located `≈`-Join residual.**  Given the intersection-side
LCA enumeration `ρ₀`, the merge is `≈`-equal to the fold of SOME `loOnEq`-respecting
delta enumeration `π₀` of `(ev₁∪ev₂)\(ev₁∩ev₂)` continued from `applySeqR init_st ρ₀`.
This is the merge=delta-fold bridge from the LCA (`eq (mergeL s₀ s₁ s₂)
(applySeqR (fold ρ₀) π₀)`) PLUS existence/goodness of the delta enumeration. -/
def RgaEqJoinResidual
    (GenDisc : (op_t → op_t → Prop) → Set op_t → Prop) : Prop :=
  ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t)
    (s₀ s₁ s₂ : concrete_st) (ρ₀ : List op_t),
    RGACondSig'.Inv s₀ → RGACondSig'.Inv s₁ → RGACondSig'.Inv s₂ →
    (∀ {a b c : op_t}, vis a b → vis b c → vis a c) →
    (∀ a : op_t, ¬ vis a a) →
    (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
    fullClosureRel (D := RGACondSig') vis ev₁ →
    fullClosureRel (D := RGACondSig') vis ev₂ →
    GenDisc vis ev₁ → GenDisc vis ev₂ → GenDisc vis (ev₁ ∪ ev₂) →
    listPermOf ρ₀ (ev₁ ∩ ev₂) →
    respects ρ₀ (loOnEq rgaEqEquiv' WfOpQ vis (ev₁ ∩ ev₂)) →
    IsCanonicalStateEq rgaEqEquiv' WfOpQ vis ev₁ s₁ →
    IsCanonicalStateEq rgaEqEquiv' WfOpQ vis ev₂ s₂ →
    ∃ π₀ : List op_t,
      listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
      respects π₀ (loOnEq rgaEqEquiv' WfOpQ vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
      eq (applySeqR (applySeqR init_st ρ₀) π₀) (RGACondSig'.mergeL s₀ s₁ s₂)

/-- **The `≈`-Join from the residual.**  The union canonical-state shape is closed
by §3; the ONLY input beyond `EqJoinLemma3C`'s own hypotheses is
`RgaEqJoinResidual` (the merge=delta-fold bridge).  Parametric in `GenDisc`, so it
holds for any generation-discipline instantiation, including the intended
`GenDisc2CEq`-family. -/
theorem rga_eqJoin_of_mergeFoldResidual
    (GenDisc : (op_t → op_t → Prop) → Set op_t → Prop)
    (hRes : RgaEqJoinResidual GenDisc) :
    EqJoinLemma3C RGACondSig' rgaEqEquiv' WfOpQ GenDisc := by
  intro vis events ev₁ ev₂ s₀ s₁ s₂ hI0 hI1 hI2 htr hir hev1 hev2 hcl1 hcl2
    hgd1 hgd2 hgdU hcs0 hcs1 hcs2
  obtain ⟨ρ₀, h₀p, h₀r, _hfold0⟩ := hcs0
  obtain ⟨π₀, hπp, hπr, hMF⟩ :=
    hRes vis events ev₁ ev₂ s₀ s₁ s₂ ρ₀ hI0 hI1 hI2 htr hir hev1 hev2
      hcl1 hcl2 hgd1 hgd2 hgdU h₀p h₀r hcs1 hcs2
  exact isCanonicalStateEq_union_of_fold vis ev₁ ev₂ hcl1 hcl2
    (RGACondSig'.mergeL s₀ s₁ s₂) ρ₀ π₀ h₀p h₀r hπp hπr hMF

#print axioms rga_eqJoin_of_mergeFoldResidual

/- ═══════════════════════════════════════════════════════════════════════════
   STATUS — `rga_EqJoinLemma3C` is NOT constructed; the residual is located EXACTLY.

   CLOSED here (kernel-clean, [propext, Classical.choice, Quot.sound]):

   • The ENTIRE union canonical-state SHAPE.  `isCanonicalStateEq_union_of_fold`
     (§3) + `rga_eqJoin_of_mergeFoldResidual` (§4) discharge every part of
     `EqJoinLemma3C`'s conclusion EXCEPT `RgaEqJoinResidual`: the `ρ₀`-extraction
     from the intersection-side canonical state, the `nodup`/`perm` of `ρ₀ ++ π₀`,
     the `respects`-append (via `loOnEqQ_index_free` + full-closure cross-edge kill),
     and the raw `foldl_append` split.  Nothing below `RgaEqJoinResidual` is smuggled.

   THE RESIDUAL (`RgaEqJoinResidual`), and why it is a genuine WALL, not mechanization
   debt.  Its core obligation is the merge=delta-fold bridge from the LCA:
       `eq (applySeqR (applySeqR init_st ρ₀) π₀) (mergeL s₀ s₁ s₂)`
   which — swapping `applySeqR init_st ρ₀ ≈ s₀` under merge congruence
   (`rgaCongVC'.mergeL_congr`) — is `eq (mergeL s₀ s₁ s₂) (applySeqR s₀ π₀)`, the
   classic bridge from `l := s₀`.  The swap-free toolkit
   (`merge_fold_indep_canon` ← `eq_merge2_of_branchInv2` ← `branchInv2_of_pieces`)
   is blocked at TWO independent points:

   • WALL 0 — no execution model from the abstract `vis`.  `EqJoinLemma3C` hands only
     `vis` trans/irrefl, `Inv sᵢ`, `fullClosureRel`, and `GenDisc`.  But
     `merge_fold_indep_canon`, `canonFoldOK_of_loOnEq`, and even the EXISTENCE of the
     delta enumeration `π₀` (`ConditionedExecutionModel`'s topological-extension lemma,
     stated for `loOnA D Cfg`, not `loOnEq`) all require a `ConditionedConfiguration`
     carrying `distinct_ts`, `causal_mono` (`vis a b → a.1 < b.1`), `BackClosed`, and
     nonzero ids — NONE of which are `EqJoinLemma3C` hypotheses.  They can only enter
     through a strengthened `GenDisc` (the `GenDisc2CEq`-family, re-exposed to carry a
     config witness); `rga_eqJoin_of_mergeFoldResidual` is deliberately parametric in
     `GenDisc` so that choice is orthogonal to the shape assembly proved here.

   • WALL 1 — the four branch pieces `hD`/`hB`/`hBE`/`hBN` (`branchInv2_of_pieces`).
     Even granting WALL 0's config, the reference-fold bridge `href` needs, at
     `l := s₀`, `a := s₁`, `b := s₂` and a reference delta fold `applySeqR l π₀`:
       – `hD` (`survivors l a b = contains (applySeqR l π₀)`): OR-set = live-set
         induction — `RGA_MergeThreadDischarge` STATUS: "not yet mechanized here".
       – `hB` (`BranchInv l (applySeqR l π₀)`): threadable per-`Del` by
         `branchInv_doDel_crossBranch_sub`, but only once `π₀`'s events are pinned to
         the branch `Ins`/`Del` with `RecPathFaithful` — "not yet mechanized here".
       – `hBE` (branch-new element): "not yet mechanized here".
       – `hBN` (branch-new anchor, GAP-1): reduces (`hBN_of_foldChain` →
         `foldChain_of_canon` → `canonBirthBridge_of_branchChain`) to `CanonMatch F
         (applySeqR l π₀)` + branch-`LiveChain` inputs (`hlive`/`hsurv`/`hsplit`) that
         `birthAnc l a b k = anc(branch) k` carries its branch's live recorded chain.
         The cross-forest reconciliation lemma (`resolve_climb_start`) IS closed, but
         those branch-`LiveChain` inputs require `s₁`, `s₂` to be LITERAL canonical
         states of their branch enumerations with the specific recorded inserts —
         content `IsCanonicalStateEq` supplies only up to `≈`, and the survivor/anchor
         projections needed are NOT `≈`-invariant in the combined-forest form.

   VERDICT.  The `≈`/order rebasing (`RGA_ConvergenceEq`) removed the OLD §7 order
   mismatch, and `merge_fold_indep_canon` removed the swap oracle — the two blockers
   RGA_Instance §7 named.  What remains is `RgaEqJoinResidual`: WALL 0 (execution
   model into `GenDisc`) + WALL 1 (the `hD`/`hB`/`hBE`/`hBN` branch-canon assembly,
   `hBN` the sharp GAP-1).  `rga_EqJoinLemma3C` is therefore reduced, not closed —
   `rga_eqJoin_of_mergeFoldResidual GenDisc hRes` produces it the moment `hRes` lands.
   ═══════════════════════════════════════════════════════════════════════════ -/

end Sal.ConditionedMRDTs.RGAInstanceFinal
