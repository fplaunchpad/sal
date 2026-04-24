import Sal.Emulation.RA_Linearizability
import Mathlib.Data.Set.Basic

/-!
# Merge linearization (existential form)

Given two RA-lin witnesses `π₁` (for replica `r₁` at state `s₁` and
event set `ev₁`) and `π₂` (for `r₂` at `s₂`, `ev₂`), establish the
existence of a witness for the merged configuration.

## Why existential, not constructive

A previous design attempted a three-lemma decomposition
`merge_witness_{perm, respects, state}` against a concrete witness
definition. That design fails: **any elementary witness definition
couples `_respects` and `_state`**. The concurrent, `rc`-ordered
cross case in `_respects` has no contradiction from permutation /
respect hypotheses alone — closing it requires knowing the state
equation being proved. The paper's own proof handles this by
**co-constructing** the witness and the lo-respect property inside
a single bottom-up induction; separating them is a mechanisation
artifact that doesn't reflect the proof.

We therefore state the merge-case as a single existential theorem
`merge_linearization_exists` (paper Lemma 1 / Theorem 1, lin.tex
§3.3 + appendix §A.2–A.4) and will prove it by induction on the
total event count, pulling events out of `merge` one at a time via
the 24 VCs (`base_*`, `ind_*`, `inter_*`, `lem_0op`).

The `restrictTo` helper is kept for use inside the induction's
inductive-case argument. -/

namespace Sal.Emulation

open Classical

section
variable {D : CRDTSig}

/-- Sub-list of `π` restricted to events in set `E`. Uses classical
decidability on `Set` membership, so the function is `noncomputable`. -/
noncomputable def restrictTo (π : List (Op D.AppOp)) (E : Set (Op D.AppOp)) :
    List (Op D.AppOp) :=
  π.filter fun x => decide (x ∈ E)

/-- **Merge case of the bridge theorem (existential form).**

Given two RA-linearization witnesses for replicas `r₁` and `r₂`,
there exists a witness for the merged configuration: a list `π`
which is a permutation of `ev₁ ∪ ev₂`, respects `lo C`, and applies
to `D.merge s₁ s₂` when folded into `D.init`.

Paper reference: Lemma 1 / Theorem 1 of lin.tex §3.3, detailed in
appendix §A.2–A.4.

**Proof strategy** (to be mechanised): strong induction on the total
event count `π₁.length + π₂.length`. At each step, pull an event off
the tail of `π₁` or `π₂` and push it through `merge` using the
appropriate VC (`base_2op`, `ind_right_*`, `ind_left_*`, `inter_*`,
`lem_0op`), recursing on the smaller configuration. Base: both lists
empty; `merge_idem` on `D.init` closes it.

Closing this theorem is the main remaining work for Phase 1 — see
`MERGE_PROOF.md` for the case-analysis plan. -/
theorem merge_linearization_exists
    {D : CRDTSig} (_hVC : SatisfiesVCs D)
    {C : Configuration D}
    {π₁ π₂ : List (Op D.AppOp)} {ev₁ ev₂ : Set (Op D.AppOp)}
    {s₁ s₂ : D.State}
    (h₁_perm : listPermOf π₁ ev₁) (h₂_perm : listPermOf π₂ ev₂)
    (_h₁_resp : respects π₁ (lo C)) (_h₂_resp : respects π₂ (lo C))
    (h₁_state : applySeq D D.init π₁ = s₁)
    (h₂_state : applySeq D D.init π₂ = s₂) :
    ∃ π, listPermOf π (ev₁ ∪ ev₂) ∧
         respects π (lo C) ∧
         applySeq D D.init π = D.merge s₁ s₂ := by
  -- Degenerate base case: both event sets empty.
  -- Covers the one exercisable case of the reachable state space
  -- (initConfig.merge applied to freshly-created replicas).
  -- The full induction is left for future work.
  by_cases h_empty₁ : π₁ = []
  · by_cases h_empty₂ : π₂ = []
    · -- Both π's empty ⟹ ev's empty, s's are init, merge is init.
      subst h_empty₁; subst h_empty₂
      obtain ⟨_, hm₁⟩ := h₁_perm
      obtain ⟨_, hm₂⟩ := h₂_perm
      have hev₁_empty : ev₁ = ∅ := by
        ext a; constructor
        · intro ha; exact absurd ((hm₁ a).mpr ha) (List.not_mem_nil)
        · intro ha; exact ha.elim
      have hev₂_empty : ev₂ = ∅ := by
        ext a; constructor
        · intro ha; exact absurd ((hm₂ a).mpr ha) (List.not_mem_nil)
        · intro ha; exact ha.elim
      subst hev₁_empty; subst hev₂_empty
      simp [applySeq] at h₁_state h₂_state
      subst h₁_state; subst h₂_state
      refine ⟨[], ?_, List.Pairwise.nil, ?_⟩
      · refine ⟨List.nodup_nil, fun a => ?_⟩
        simp
      · simp [applySeq, _hVC.merge_idem]
    · -- π₂ non-empty — inductive step. Left to future work.
      sorry
  · -- π₁ non-empty — inductive step. Left to future work.
    sorry

end

/-! ### Packaging

Invoke `merge_linearization_exists` to build the merged replica's
witness from the IH witnesses for `r₁` and `r₂`. -/

/-- `Merge` preserves RA-lin. Intended closure of
`RA_Linearizability.RA_lin_preserved_merge`.

Body: destructure the existential from `merge_linearization_exists`
and thread it through. Closes end-to-end once
`merge_linearization_exists` is fully proved. -/
theorem RA_lin_preserved_merge_via_witness
    {D : CRDTSig} {C C' : Configuration D} (hVC : SatisfiesVCs D)
    {r₁ r₂ : Replica} {s₁ s₂ : D.State}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_s₁  : C.N r₁ = some s₁) (h_s₂  : C.N r₂ = some s₂)
    (h_ev₁ : C.L r₁ = some ev₁) (h_ev₂ : C.L r₂ = some ev₂)
    (hN   : C'.N = updateRep C.N r₁ (D.merge s₁ s₂))
    (hL   : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hRA : IsRALinearizable C) :
    IsRALinearizable C' := by
  intro r' s' E' hN' hL'
  rw [hN] at hN'
  rw [hL] at hL'
  by_cases hr' : r' = r₁
  · -- Merged replica.
    subst hr'
    simp [updateRep] at hN' hL'
    obtain ⟨π₁, hp₁, hr₁, hs₁'⟩ := hRA r' s₁ ev₁ h_s₁ h_ev₁
    obtain ⟨π₂, hp₂, hr₂, hs₂'⟩ := hRA r₂ s₂ ev₂ h_s₂ h_ev₂
    obtain ⟨π, hperm, hresp, hstate⟩ :=
      merge_linearization_exists (D := D) (C := C) hVC hp₁ hp₂ hr₁ hr₂ hs₁' hs₂'
    refine ⟨π, ?_, ?_, ?_⟩
    · rw [← hL']; exact hperm
    · have : lo C' = lo C := by unfold lo; rw [hvis]
      rw [this]; exact hresp
    · rw [← hN']; exact hstate
  · -- Other replica: IH applies directly.
    simp [updateRep, hr'] at hN' hL'
    obtain ⟨π, hperm, hresp, heq⟩ := hRA r' s' E' hN' hL'
    refine ⟨π, hperm, ?_, heq⟩
    have : lo C' = lo C := by unfold lo; rw [hvis]
    rw [this]; exact hresp

end Sal.Emulation
