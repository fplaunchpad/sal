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

/-- Combined permutation: the common events from `π₁`, followed by
`π₁`'s unique events, followed by `π₂`'s unique events.

Using `π₁`'s ordering for the common events (both `π₁` and `π₂`
witness permutations of `ev₁` and `ev₂` respectively, so `π₁ ∩ π₂`
gives both; we pick `π₁`'s version). -/
noncomputable def merge_witness (π₁ π₂ : List (Op D.AppOp))
    (ev₁ ev₂ : Set (Op D.AppOp)) : List (Op D.AppOp) :=
  restrictTo π₁ (ev₁ ∩ ev₂) ++
    restrictTo π₁ (ev₁ \ ev₂) ++
    restrictTo π₂ (ev₂ \ ev₁)

/-! ### Supporting lemmas (scaffolded) -/

/-- The `merge_witness` is a permutation of `ev₁ ∪ ev₂`. Follows from
`π₁` being a permutation of `ev₁` and `π₂` of `ev₂`, plus the
standard set-theoretic decomposition `ev₁ ∪ ev₂ = (ev₁ ∩ ev₂) ∪
(ev₁ \ ev₂) ∪ (ev₂ \ ev₁)`. -/
theorem merge_witness_perm
    {π₁ π₂ : List (Op D.AppOp)} {ev₁ ev₂ : Set (Op D.AppOp)}
    (h₁ : listPermOf π₁ ev₁) (h₂ : listPermOf π₂ ev₂) :
    listPermOf (merge_witness π₁ π₂ ev₁ ev₂) (ev₁ ∪ ev₂) := by
  obtain ⟨hn₁, hm₁⟩ := h₁
  obtain ⟨hn₂, hm₂⟩ := h₂
  -- Three building blocks — the restrictTo parts.
  have A_nodup : (restrictTo π₁ (ev₁ ∩ ev₂)).Nodup := by
    unfold restrictTo; exact hn₁.filter _
  have B_nodup : (restrictTo π₁ (ev₁ \ ev₂)).Nodup := by
    unfold restrictTo; exact hn₁.filter _
  have C_nodup : (restrictTo π₂ (ev₂ \ ev₁)).Nodup := by
    unfold restrictTo; exact hn₂.filter _
  have mem_A : ∀ a, a ∈ restrictTo π₁ (ev₁ ∩ ev₂) ↔ a ∈ ev₁ ∧ a ∈ ev₂ := by
    intro a; unfold restrictTo
    simp only [List.mem_filter, decide_eq_true_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨_, h, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨(hm₁ a).mpr h, h, h'⟩
  have mem_B : ∀ a, a ∈ restrictTo π₁ (ev₁ \ ev₂) ↔ a ∈ ev₁ ∧ a ∉ ev₂ := by
    intro a; unfold restrictTo
    simp only [List.mem_filter, decide_eq_true_eq, Set.mem_diff]
    constructor
    · rintro ⟨_, h, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨(hm₁ a).mpr h, h, h'⟩
  have mem_C : ∀ a, a ∈ restrictTo π₂ (ev₂ \ ev₁) ↔ a ∈ ev₂ ∧ a ∉ ev₁ := by
    intro a; unfold restrictTo
    simp only [List.mem_filter, decide_eq_true_eq, Set.mem_diff]
    constructor
    · rintro ⟨_, h, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨(hm₂ a).mpr h, h, h'⟩
  refine ⟨?_, ?_⟩
  · -- Nodup (A ++ B ++ C)
    unfold merge_witness
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨A_nodup, B_nodup, ?_⟩, C_nodup, ?_⟩
    · -- A disjoint B: a ∈ A ⟹ a ∈ ev₂; a ∈ B ⟹ a ∉ ev₂.
      intro a haA b hbB hab
      rw [(mem_B b)] at hbB
      subst hab
      exact hbB.2 ((mem_A a).mp haA).2
    · -- (A ++ B) disjoint C
      intro a hab c hcC hac
      rw [List.mem_append] at hab
      rw [(mem_C c)] at hcC
      subst hac
      rcases hab with h | h
      · -- a ∈ A: a ∈ ev₁
        exact hcC.2 ((mem_A a).mp h).1
      · -- a ∈ B: a ∈ ev₁
        exact hcC.2 ((mem_B a).mp h).1
  · -- Membership
    intro a
    unfold merge_witness
    rw [List.mem_append, List.mem_append]
    rw [mem_A a, mem_B a, mem_C a, Set.mem_union]
    constructor
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inl h
      · exact Or.inr h
    · intro h
      rcases h with h | h
      · by_cases h' : a ∈ ev₂
        · exact Or.inl (Or.inl ⟨h, h'⟩)
        · exact Or.inl (Or.inr ⟨h, h'⟩)
      · by_cases h' : a ∈ ev₁
        · exact Or.inl (Or.inl ⟨h', h⟩)
        · exact Or.inr ⟨h, h'⟩

/-- The `merge_witness` respects `lo C` (the vis-unchanged assumption
is baked in: at the merge step `C'.vis = C.vis`, so `lo C' = lo C`
on the merged event set).

The argument uses:
* Within each of the three parts (π₁|_top, π₁|_L₁, π₂|_L₂):
  the IH `respects` is preserved by `List.filter`.
* Between parts: the standard "L₁^b before L_top^a before L₁^a"
  structure from the paper (lemmas.tex Lemma 1 / Lemma 2). Requires
  `rcNonComm` and `condComm` hypotheses (i.e. `SatisfiesVCs`). -/
theorem merge_witness_respects
    {C : Configuration D}
    {π₁ π₂ : List (Op D.AppOp)} {ev₁ ev₂ : Set (Op D.AppOp)}
    (_h₁_resp : respects π₁ (lo C)) (_h₂_resp : respects π₂ (lo C)) :
    respects (merge_witness π₁ π₂ ev₁ ev₂) (lo C) := by
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
      exact merge_witness_respects hr₁ hr₂
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
