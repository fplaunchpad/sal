import Sal.MRDTs.Metatheory.Development.RGA_Skeleton3

/-!
# Skeleton 3 leaf reduction — `hCanon` from `hMergeInputs` alone

*Additive; modifies no existing file; 0 `sorry`.*

In the H-world the witnesses CARRY the engine discipline (`CanonFoldOK [] init_st ρᵢ`), so every
`CanonMatch` derives directly (`canon_fold` + `canonMatch_of_canonInv`) — **no `EngineReady`, no
`RefEdge`, no `hReady` leg anywhere**:

* `canonMatch_of_canonFoldOK` — a disciplined enumeration folds to its canonical state.
* `hFoldCanon3` — all four `CanonMatch`es of the Skeleton-3 chain from its own premises
  (branches direct; the union via `canonFoldOK_concat`).
* `hCanon_of_leaves3` — Skeleton 3's `hCanon` from `hMergeInputs` alone (the merge glue's leaf
  bundle; the sole remaining deep residual of the merge half is `BranchInv`-I4 inside it).
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.Metatheory.RGASkeleton3

open Sal.Emulation
open Sal.Metatheory.GenericEqQuotient
open Sal.Metatheory.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA)
open Sal.Metatheory.RGAMergeCanon (canonMatch_merge_of_inputs)
open Sal.Metatheory.RGACorrectedResidual (canonFoldOK_concat)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonMatch CanonFoldOK CanonInv canon_fold canonInv_init
  canonMatch_of_canonInv survP insertedIn deletedIn)
open RGAMergeFoldChain (CanonBirthBridge)

/-- **A disciplined enumeration folds to its canonical state.**  The H-witness clause is exactly
the engine's input: run `canon_fold` from `init` and project. -/
theorem canonMatch_of_canonFoldOK (ρ : List op_t) (h : CanonFoldOK [] init_st ρ) :
    CanonMatch ρ (applySeqR init_st ρ) := by
  have hci := canon_fold ρ [] init_st canonInv_init h
  rw [List.nil_append] at hci
  exact canonMatch_of_canonInv ρ _ hci

/-- **All four `CanonMatch`es from the Skeleton-3 disciplines** — no `EngineReady` anywhere. -/
theorem hFoldCanon3 (ρ₀ ρ₁ ρ₂ π₀ : List op_t)
    (h₀OK : CanonFoldOK [] init_st ρ₀)
    (h₁OK : CanonFoldOK [] init_st ρ₁)
    (h₂OK : CanonFoldOK [] init_st ρ₂)
    (hπOK : CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀) :
    CanonMatch ρ₀ (applySeqR init_st ρ₀) ∧ CanonMatch ρ₁ (applySeqR init_st ρ₁)
      ∧ CanonMatch ρ₂ (applySeqR init_st ρ₂)
      ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR init_st ρ₀) π₀) := by
  refine ⟨canonMatch_of_canonFoldOK ρ₀ h₀OK, canonMatch_of_canonFoldOK ρ₁ h₁OK,
    canonMatch_of_canonFoldOK ρ₂ h₂OK, ?_⟩
  have hcat : CanonFoldOK [] init_st (ρ₀ ++ π₀) :=
    canonFoldOK_concat ρ₀ [] init_st π₀ h₀OK hπOK
  have hcm := canonMatch_of_canonFoldOK (ρ₀ ++ π₀) hcat
  have happ : applySeqR init_st (ρ₀ ++ π₀) = applySeqR (applySeqR init_st ρ₀) π₀ := by
    simp only [applySeqR, List.foldl_append]
  rw [happ] at hcm
  exact hcm

/-- **Skeleton 3's `hCanon` from the merge-glue leaves alone.**  The fold half and the three
branch `CanonMatch`es are DERIVED from the carried disciplines (`hFoldCanon3`); the merge half is
`canonMatch_merge_of_inputs` fed the `hMergeInputs` bundle. -/
theorem hCanon_of_leaves3
    (hMergeInputs : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        CanonFoldOK [] init_st ρ₀ → CanonFoldOK [] init_st ρ₁ → CanonFoldOK [] init_st ρ₂ →
        CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ →
        (∀ y, contains (applySeqR init_st ρ₀) y = true → y ≠ 0 → anc (applySeqR init_st ρ₀) y < y)
        ∧ (∀ y, contains (applySeqR init_st ρ₀) y = true →
            (anc (applySeqR init_st ρ₀) y = 0 ∨ contains (applySeqR init_st ρ₀) (anc (applySeqR init_st ρ₀) y) = true))
        ∧ contains (applySeqR init_st ρ₀) 0 = false
        ∧ (∀ c, (insertedIn ρ₀ c ↔ insertedIn ρ₁ c ∧ insertedIn ρ₂ c)
            ∧ (deletedIn ρ₁ c → insertedIn ρ₁ c) ∧ (deletedIn ρ₂ c → insertedIn ρ₂ c)
            ∧ (deletedIn ρ₀ c → deletedIn ρ₁ c) ∧ (deletedIn ρ₀ c → deletedIn ρ₂ c)
            ∧ (insertedIn (ρ₀ ++ π₀) c ↔ insertedIn ρ₁ c ∨ insertedIn ρ₂ c)
            ∧ (deletedIn (ρ₀ ++ π₀) c ↔ deletedIn ρ₁ c ∨ deletedIn ρ₂ c))
        ∧ (∀ (t r e a : ℕ) (p : List ℕ),
            (t, r, .Ins e p a) ∈ ρ₀ ++ π₀ → survP (ρ₀ ++ π₀) t →
            (contains (applySeqR init_st ρ₀) t = true → (t, r, .Ins e p a) ∈ ρ₀)
            ∧ (contains (applySeqR init_st ρ₁) t = true → (t, r, .Ins e p a) ∈ ρ₁)
            ∧ (contains (applySeqR init_st ρ₂) t = true → (t, r, .Ins e p a) ∈ ρ₂)
            ∧ (contains (applySeqR init_st ρ₀) t = true ∨ contains (applySeqR init_st ρ₁) t = true
                ∨ contains (applySeqR init_st ρ₂) t = true))
        ∧ (∀ (t r e a : ℕ) (p : List ℕ),
            (t, r, .Ins e p a) ∈ ρ₀ ++ π₀ → survP (ρ₀ ++ π₀) t →
            CanonBirthBridge (applySeqR init_st ρ₀) (ρ₀ ++ π₀)
                (birthAnc (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂) t) (a :: p)
            ∧ (birthAnc (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂) t = 0
                ∨ survivors (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂)
                    (birthAnc (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂) t) = true))) :
    ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        CanonFoldOK [] init_st ρ₀ → CanonFoldOK [] init_st ρ₁ → CanonFoldOK [] init_st ρ₂ →
        CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ →
        CanonMatch (ρ₀ ++ π₀)
            (merge (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂))
          ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR init_st ρ₀) π₀) := by
  intro vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ htr hir hdts hev1 hev2 hcl1 hcl2 h0p h1p h2p hπp hπr
    h₀OK h₁OK h₂OK hπOK
  obtain ⟨hcm0, hcm1, hcm2, hfold⟩ := hFoldCanon3 ρ₀ ρ₁ ρ₂ π₀ h₀OK h₁OK h₂OK hπOK
  obtain ⟨Hdec, Hstay, h0, hcaus, hins_branch, hbridge⟩ :=
    hMergeInputs vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ htr hir hdts hev1 hev2 hcl1 hcl2
      h0p h1p h2p hπp hπr h₀OK h₁OK h₂OK hπOK
  exact ⟨canonMatch_merge_of_inputs (applySeqR init_st ρ₀) (applySeqR init_st ρ₁)
      (applySeqR init_st ρ₂) ρ₀ π₀ ρ₁ ρ₂ hcm0 hcm1 hcm2 Hdec Hstay h0 hcaus hins_branch hbridge,
    hfold⟩

/-! ## Axiom audit -/

#print axioms canonMatch_of_canonFoldOK
#print axioms hFoldCanon3
#print axioms hCanon_of_leaves3

end Sal.Metatheory.RGASkeleton3
