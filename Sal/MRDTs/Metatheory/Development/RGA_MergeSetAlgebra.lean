import Sal.MRDTs.Metatheory.Conditioned.RGA_CanonMatch_Reachable

/-!
# Merge set-algebra — `insertedIn`/`deletedIn`/`survP` monotonicity

*Additive; modifies no existing file; 0 `sorry`.*

The event-set plumbing behind the merge leaves. `insertedIn`/`deletedIn` are monotone in the enumerated
event set (via `listPermOf` + set inclusion), and from that the branch-vs-union survivor relations
(`survP ρ₀ ∧ survP F ⟹ survP ρ₁`, i.e. an LCA-live survivor is branch-live) fall out. Instantiated at
`E₀ = ev₁∩ev₂ ⊆ E₁ = ev₁ ⊆ Eu = ev₁∪ev₂`, these discharge `hsurv01` (the corrected σ₀'-live-survivor ⟹
σ₁'-live fact in `hFiltEq_of_branchInv`) and the subset clauses of `hcaus`.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGAMergeSetAlgebra

open Sal.Emulation
open RGACanonConvergence (insertedIn deletedIn survP)

/-- `insertedIn` is monotone in the enumerated event set. -/
theorem insertedIn_mono (π π' : List op_t) (E E' : Set op_t)
    (hπ : listPermOf π E) (hπ' : listPermOf π' E') (hsub : E ⊆ E') (c : ℕ)
    (h : insertedIn π c) : insertedIn π' c := by
  obtain ⟨r, e, p, a, hin⟩ := h
  exact ⟨r, e, p, a, (hπ'.2 _).mpr (hsub ((hπ.2 _).mp hin))⟩

/-- `deletedIn` is monotone in the enumerated event set. -/
theorem deletedIn_mono (π π' : List op_t) (E E' : Set op_t)
    (hπ : listPermOf π E) (hπ' : listPermOf π' E') (hsub : E ⊆ E') (c : ℕ)
    (h : deletedIn π c) : deletedIn π' c := by
  obtain ⟨t, r, p, hin⟩ := h
  exact ⟨t, r, p, (hπ'.2 _).mpr (hsub ((hπ.2 _).mp hin))⟩

/-- **An LCA-live survivor is branch-live.**  `survP ρ₀ c` (inserted in the LCA `E₀ ⊆ E₁`) gives
`insertedIn ρ₁ c`; `survP F c` (not deleted in the union `Eu ⊇ E₁`) gives `¬ deletedIn ρ₁ c`; hence
`survP ρ₁ c`. This is exactly `hsurv01` once the branch canons rewrite `contains σᵢ'` to `survP ρᵢ`. -/
theorem survP_branch_of_lca_union (ρ₀ ρ₁ F : List op_t) (E₀ E₁ Eu : Set op_t)
    (h0p : listPermOf ρ₀ E₀) (h1p : listPermOf ρ₁ E₁) (hFp : listPermOf F Eu)
    (hsub01 : E₀ ⊆ E₁) (hsub1u : E₁ ⊆ Eu) (c : ℕ)
    (hs0 : survP ρ₀ c) (hsF : survP F c) : survP ρ₁ c :=
  ⟨insertedIn_mono ρ₀ ρ₁ E₀ E₁ h0p h1p hsub01 c hs0.1,
    fun hdel1 => hsF.2 (deletedIn_mono ρ₁ F E₁ Eu h1p hFp hsub1u c hdel1)⟩

/-- `insertedIn` distributes over list append. -/
theorem insertedIn_append (π₁ π₂ : List op_t) (c : ℕ) :
    insertedIn (π₁ ++ π₂) c ↔ insertedIn π₁ c ∨ insertedIn π₂ c := by
  constructor
  · rintro ⟨r, e, p, a, hin⟩
    rcases List.mem_append.mp hin with h | h
    · exact Or.inl ⟨r, e, p, a, h⟩
    · exact Or.inr ⟨r, e, p, a, h⟩
  · rintro (⟨r, e, p, a, hin⟩ | ⟨r, e, p, a, hin⟩)
    · exact ⟨r, e, p, a, List.mem_append.mpr (Or.inl hin)⟩
    · exact ⟨r, e, p, a, List.mem_append.mpr (Or.inr hin)⟩

/-- `deletedIn` distributes over list append. -/
theorem deletedIn_append (π₁ π₂ : List op_t) (c : ℕ) :
    deletedIn (π₁ ++ π₂) c ↔ deletedIn π₁ c ∨ deletedIn π₂ c := by
  constructor
  · rintro ⟨t, r, p, hin⟩
    rcases List.mem_append.mp hin with h | h
    · exact Or.inl ⟨t, r, p, h⟩
    · exact Or.inr ⟨t, r, p, h⟩
  · rintro (⟨t, r, p, hin⟩ | ⟨t, r, p, hin⟩)
    · exact ⟨t, r, p, List.mem_append.mpr (Or.inl hin)⟩
    · exact ⟨t, r, p, List.mem_append.mpr (Or.inr hin)⟩

/-- **Membership transfer.**  Through a `listPermOf`, `insertedIn` reads off the event *set*. -/
theorem insertedIn_perm_iff (π : List op_t) (E : Set op_t) (hπ : listPermOf π E) (c : ℕ) :
    insertedIn π c ↔ ∃ r e p a, (c, r, .Ins e p a) ∈ E := by
  constructor
  · rintro ⟨r, e, p, a, hin⟩; exact ⟨r, e, p, a, (hπ.2 _).mp hin⟩
  · rintro ⟨r, e, p, a, hin⟩; exact ⟨r, e, p, a, (hπ.2 _).mpr hin⟩

theorem deletedIn_perm_iff (π : List op_t) (E : Set op_t) (hπ : listPermOf π E) (c : ℕ) :
    deletedIn π c ↔ ∃ t r p, (t, r, .Del p c) ∈ E := by
  constructor
  · rintro ⟨t, r, p, hin⟩; exact ⟨t, r, p, (hπ.2 _).mp hin⟩
  · rintro ⟨t, r, p, hin⟩; exact ⟨t, r, p, (hπ.2 _).mpr hin⟩

#print axioms insertedIn_mono
#print axioms deletedIn_mono
#print axioms survP_branch_of_lca_union
#print axioms insertedIn_append
#print axioms deletedIn_append

end Sal.Metatheory.RGAMergeSetAlgebra
