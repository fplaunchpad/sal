import Sal.Emulation.RA_Linearizability
import Mathlib.Data.Set.Basic

/-!
# Merge linearization: bottom-up construction of the `merge_witness`

Building out `RA_lin_preserved_merge` following `MERGE_PROOF.md` +
the Sal paper's `lemmas.tex` §4.1.

Given two RA-lin witnesses `π₁` (for replica `r₁` at state `s₁` and
event set `ev₁`) and `π₂` (for `r₂` at `s₂`, `ev₂`), construct a
witness `merge_witness π₁ π₂` for the merged configuration.

Strategy is the paper's bottom-up template, specialised to 2-way
merge:

* Decompose `ev₁ ∪ ev₂` into `L_top = ev₁ ∩ ev₂`, `L₁ = ev₁ \ L_top`,
  `L₂ = ev₂ \ L_top`.
* Build `merge_witness` as `π_top ++ π₁' ++ π₂'` where
  * `π_top` is a permutation of `L_top` (respecting `lo`).
  * `π₁'` is the sub-list of `π₁` restricted to `L₁`.
  * `π₂'` is the sub-list of `π₂` restricted to `L₂`.
* The three supporting lemmas:
  * `merge_witness_perm` — the result is a permutation of `ev₁ ∪ ev₂`.
  * `merge_witness_respects` — respects `lo C` (which equals `lo C'`
    since merge doesn't change vis).
  * `merge_witness_state` — yields `merge(s₁, s₂)`.

This file scaffolds the definitions and states the three supporting
lemmas; `merge_witness_state` is the load-bearing proof (uses the 24
VCs). Closing it is the bulk of the remaining work.
-/

namespace Sal.Emulation

open Classical

section
variable {D : CRDTSig}

/-- Sub-list of `π` restricted to events in set `E`. Uses classical
decidability on `Set` membership, so the function is `noncomputable`. -/
noncomputable def restrictTo (π : List (Op D.AppOp)) (E : Set (Op D.AppOp)) :
    List (Op D.AppOp) :=
  π.filter fun x => decide (x ∈ E)

/-- Combined permutation witnessing `ev₁ ∪ ev₂`: use `π₁` verbatim
(covers `ev₁`), then append the sublist of `π₂` restricted to events
only at `r₂` (covers `ev₂ \ ev₁`).

This preserves `π₁`'s internal ordering (important for `respects`) and
keeps `π₂`'s sub-list ordering intact. Since `π₁` already includes the
common-ancestor events (`ev₁ ∩ ev₂`), there's no double counting. -/
noncomputable def merge_witness (π₁ π₂ : List (Op D.AppOp))
    (ev₁ ev₂ : Set (Op D.AppOp)) : List (Op D.AppOp) :=
  π₁ ++ restrictTo π₂ (ev₂ \ ev₁)

/-! ### Supporting lemmas (scaffolded) -/

/-- The `merge_witness` is a permutation of `ev₁ ∪ ev₂`. Follows from
`π₁ ≡ ev₁`, `π₂ ≡ ev₂` (up to permutation), and the fact that
`ev₁ ∪ (ev₂ \ ev₁) = ev₁ ∪ ev₂`. -/
theorem merge_witness_perm
    {π₁ π₂ : List (Op D.AppOp)} {ev₁ ev₂ : Set (Op D.AppOp)}
    (h₁ : listPermOf π₁ ev₁) (h₂ : listPermOf π₂ ev₂) :
    listPermOf (merge_witness π₁ π₂ ev₁ ev₂) (ev₁ ∪ ev₂) := by
  obtain ⟨hn₁, hm₁⟩ := h₁
  obtain ⟨hn₂, hm₂⟩ := h₂
  have R_nodup : (restrictTo π₂ (ev₂ \ ev₁)).Nodup := by
    unfold restrictTo; exact hn₂.filter _
  have mem_R : ∀ a, a ∈ restrictTo π₂ (ev₂ \ ev₁) ↔ a ∈ ev₂ ∧ a ∉ ev₁ := by
    intro a; unfold restrictTo
    simp only [List.mem_filter, decide_eq_true_eq, Set.mem_diff]
    constructor
    · rintro ⟨_, h, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨(hm₂ a).mpr h, h, h'⟩
  refine ⟨?_, ?_⟩
  · -- Nodup (π₁ ++ restrictTo π₂ (ev₂ \ ev₁))
    unfold merge_witness
    rw [List.nodup_append]
    refine ⟨hn₁, R_nodup, ?_⟩
    intro a ha b hb hab
    rw [mem_R b] at hb
    subst hab
    exact hb.2 ((hm₁ a).mp ha)
  · -- Membership
    intro a
    unfold merge_witness
    rw [List.mem_append, mem_R a, hm₁ a, Set.mem_union]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr h
    · intro h
      rcases h with h | h
      · exact Or.inl h
      · by_cases h' : a ∈ ev₁
        · exact Or.inl h'
        · exact Or.inr ⟨h, h'⟩

/-- The `merge_witness` respects `lo C`. Split via `List.pairwise_append`
into three obligations:

1. `π₁.Pairwise (¬ lo C · ·)` — directly from `h₁_resp`.
2. `(restrictTo π₂ _).Pairwise ...` — from `h₂_resp` via filter-sublist.
3. Cross case: for `a ∈ π₁` (so `a ∈ ev₁`) and `b ∈ restrictTo π₂ (ev₂ \ ev₁)`
   (so `b ∈ ev₂ ∧ b ∉ ev₁`), show `¬ lo C b a`.

The cross case unfolds `lo` into two disjuncts:

* **Disjunct 1** (`C.vis b a ∧ ¬ commutes b a`): closed via
  `C.vis_causal` — `vis b a` + `a ∈ ev₁` implies `b ∈ ev₁`,
  contradicting `b ∉ ev₁`.

* **Disjunct 2** (`¬ vis b a ∧ ¬ vis a b ∧ rc b a = Fst_then_snd ∧
  ¬ ∃ e₃, vis a e₃ ∧ ¬ commutes a e₃`): **NOT YET CLOSED.** The
  concurrent, rc-ordered case has no elementary contradiction from
  just the permutation/respect hypotheses. Any closure strategy has
  to invoke `SatisfiesVCs` (specifically `rc_non_comm`, `cond_comm`)
  and likely requires knowing the joint structure of π₁ and π₂ — i.e.
  it is coupled to `merge_witness_state`. See `MERGE_PROOF.md` for the
  status analysis. -/
theorem merge_witness_respects
    {C : Configuration D} {r₁ : Replica}
    {π₁ π₂ : List (Op D.AppOp)} {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_ev₁ : C.L r₁ = some ev₁)
    (h₁_perm : listPermOf π₁ ev₁) (_h₂_perm : listPermOf π₂ ev₂)
    (h₁_resp : respects π₁ (lo C)) (h₂_resp : respects π₂ (lo C)) :
    respects (merge_witness π₁ π₂ ev₁ ev₂) (lo C) := by
  unfold merge_witness respects
  rw [List.pairwise_append]
  refine ⟨h₁_resp, ?_, ?_⟩
  · -- Within restrictTo π₂ (ev₂ \ ev₁): filter preserves Pairwise.
    unfold restrictTo
    exact h₂_resp.filter _
  · -- Cross case: a ∈ π₁, b ∈ restrictTo π₂ (ev₂ \ ev₁). Show ¬ lo C b a.
    intro a ha b hb
    have hb_mem : b ∈ ev₂ ∧ b ∉ ev₁ := by
      unfold restrictTo at hb
      simp only [List.mem_filter, decide_eq_true_eq, Set.mem_diff] at hb
      exact hb.2
    have ha_ev₁ : a ∈ ev₁ := (h₁_perm.2 a).mp ha
    intro hlo
    unfold lo at hlo
    rcases hlo with ⟨hvis, _⟩ | ⟨_hnv₁, _hnv₂, _hrc, _hnex⟩
    · -- Disjunct 1: causal closure rules out vis b a with a ∈ ev₁, b ∉ ev₁.
      exact hb_mem.2 (C.vis_causal hvis h_ev₁ ha_ev₁)
    · -- Disjunct 2: concurrent + rc-ordered. See docstring.
      sorry

/-- Applying the `merge_witness` to `σ₀` yields `D.merge s₁ s₂`. The
load-bearing lemma. Uses the 24 VCs from `SatisfiesVCs` to iteratively
push events through `merge`.

Proof structure (paper lemmas.tex Theorem 1):
1. Start from `D.merge s₁ s₂ = D.merge (applySeq σ₀ π₁) (applySeq σ₀ π₂)`.
2. Use `merge_idem` to equate with `D.merge l s₁ s₂` for any appropriate
   `l` (in the CRDT 2-way case, absorbed into the rewriting below).
3. Apply the bottom-up rules (`base_1op`, `ind_*`, `inter_*`, `lem_0op`)
   to pull events out one at a time, matching the structure of
   `merge_witness`.
4. Base: all events pulled out → `D.merge σ₀ σ₀ = σ₀`; witness
   reconstructs. -/
theorem merge_witness_state
    {π₁ π₂ : List (Op D.AppOp)} {ev₁ ev₂ : Set (Op D.AppOp)}
    {s₁ s₂ : D.State}
    (_hVC : SatisfiesVCs D)
    (_h₁_perm : listPermOf π₁ ev₁) (_h₂_perm : listPermOf π₂ ev₂)
    (_h₁_state : applySeq D D.init π₁ = s₁)
    (_h₂_state : applySeq D D.init π₂ = s₂) :
    applySeq D D.init (merge_witness π₁ π₂ ev₁ ev₂) = D.merge s₁ s₂ := by
  sorry

end

/-! ### Packaging

Assemble the three supporting lemmas into `RA_lin_preserved_merge`.
Once all three are closed, this theorem closes without further work. -/

/-- `Merge` preserves RA-lin. This is the intended closure of
`RA_Linearizability.RA_lin_preserved_merge`, using `merge_witness`
from this file.

Body: given the IH witnesses for `r₁` and `r₂`, construct
`merge_witness` and invoke the three supporting lemmas.

The current signature matches `RA_lin_preserved_merge` in
`RA_Linearizability.lean`, so replacing the existing stubbed theorem
with a call to this one is a single-line swap once the supporting
lemmas are closed. -/
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
  · -- Merged replica: build witness from IH witnesses for r₁ and r₂.
    subst hr'
    simp [updateRep] at hN' hL'
    obtain ⟨π₁, hp₁, hr₁, hs₁'⟩ := hRA r' s₁ ev₁ h_s₁ h_ev₁
    obtain ⟨π₂, hp₂, hr₂, hs₂'⟩ := hRA r₂ s₂ ev₂ h_s₂ h_ev₂
    refine ⟨merge_witness π₁ π₂ ev₁ ev₂, ?_, ?_, ?_⟩
    · -- listPermOf — needs `ev₁ ∪ ev₂ = E'` via hL'
      have := merge_witness_perm (D := D) hp₁ hp₂
      rwa [hL'] at this
    · -- respects lo C' = lo C (vis unchanged via hvis)
      have : lo C' = lo C := by unfold lo; rw [hvis]
      rw [this]
      exact merge_witness_respects h_ev₁ hp₁ hp₂ hr₁ hr₂
    · -- state
      rw [← hN']
      exact merge_witness_state hVC hp₁ hp₂ hs₁' hs₂'
  · -- Other replica: IH applies directly.
    simp [updateRep, hr'] at hN' hL'
    obtain ⟨π, hperm, hresp, heq⟩ := hRA r' s' E' hN' hL'
    refine ⟨π, hperm, ?_, heq⟩
    have : lo C' = lo C := by unfold lo; rw [hvis]
    rw [this]; exact hresp

end Sal.Emulation
