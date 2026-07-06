import Sal.MRDTs.Metatheory.Development.RGA_CanonMatch_Reachable

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

#print axioms insertedIn_mono
#print axioms deletedIn_mono
#print axioms survP_branch_of_lca_union

end Sal.Metatheory.RGAMergeSetAlgebra
