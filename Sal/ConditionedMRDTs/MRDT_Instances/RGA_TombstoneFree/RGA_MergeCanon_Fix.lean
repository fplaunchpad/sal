import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_MergeCanon

/-!
# Merge-canon correction — the birth-anchor 0-or-survivor premise, weakened and DERIVED

*Additive; modifies no existing file; 0 `sorry`.*

`canonMatch_merge_of_inputs` carries the per-survivor premise `hbwsurv : birthAnc = 0 ∨ survivors
birthAnc` — which is FALSE in general (criss-cross rehoming: node 7's birth anchor is the LCA node
2, deleted in the other branch, hence dead in the merge; see `AgentNotes.md`).  Inspection of
`merge_anc_clause` shows the premise fires ONLY in the `¬ contains σ₀' bw` branch (the climb
fixpoint) — and THERE it is derivable: a birth anchor read off a branch-final state is live at that
branch (`wf`), so a non-LCA birth anchor is a branch-born survivor (`da ∖ dl ⊆ I`), and an LCA-read
birth anchor under `¬ contains σ₀'` is the root (`Hstay`).

* `merge_anc_clause'` — the anchor clause with the CONDITIONAL premise.
* `bwsurv_of_wf` — the derivation of that premise from the branch `wf` facts.
* `canonMatch_merge_of_inputs'` — the corrected glue: the bridge bundle needs ONLY
  `CanonBirthBridge` per survivor; the 0-or-survivor conjunct is GONE (derived). -/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
namespace Sal.ConditionedMRDTs.RGAMergeCanon

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.Emulation
open RGACanonConvergence (CanonMatch canonAnc survP insertedIn deletedIn resolve_eq_canonAnc)
open RGAMergeLinearization (contains_eq_domain)
open RGAMergeFoldChain (CanonBirthBridge)
open RGAMergeBranchNew (resolve_climb_start)

/-- **The anchor clause, conditional-premise form.**  As `merge_anc_clause`, but the
0-or-survivor fact is required only where it is used: off the LCA forest. -/
theorem merge_anc_clause'
    (σ₀' σ₁' σ₂' : concrete_st α) (F : List (op_t α)) (t a : ℕ) (p : List ℕ)
    (Hdec : ∀ y, contains σ₀' y = true → y ≠ 0 → anc σ₀' y < y)
    (Hstay : ∀ y, contains σ₀' y = true → (anc σ₀' y = 0 ∨ contains σ₀' (anc σ₀' y) = true))
    (h0 : contains σ₀' 0 = false)
    (hdom : ∀ c, contains (merge σ₀' σ₁' σ₂') c = true ↔ survP F c)
    (hbridge : CanonBirthBridge σ₀' F (birthAnc σ₀' σ₁' σ₂' t) (a :: p))
    (hbwsurv : contains σ₀' (birthAnc σ₀' σ₁' σ₂' t) = false →
        (birthAnc σ₀' σ₁' σ₂' t = 0
          ∨ survivors σ₀' σ₁' σ₂' (birthAnc σ₀' σ₁' σ₂' t) = true)) :
    anc (merge σ₀' σ₁' σ₂') t = canonAnc F (a :: p) := by
  rw [anc_merge]
  set bw := birthAnc σ₀' σ₁' σ₂' t with hbwdef
  obtain ⟨hbin, hbout⟩ := hbridge
  have hdmerge : domain (merge σ₀' σ₁' σ₂') = survivors σ₀' σ₁' σ₂' := by
    funext k; rw [← contains_eq_domain]; exact contains_merge σ₀' σ₁' σ₂' k
  by_cases hlw : contains σ₀' bw = true
  · obtain ⟨cw, hpath, hceq⟩ := hbin hlw
    have hrcs := resolve_climb_start σ₀' (merge σ₀' σ₁' σ₂') Hdec Hstay h0 bw cw hlw hpath
    rw [hdmerge] at hrcs
    rw [← hrcs, resolve_eq_canonAnc F (merge σ₀' σ₁' σ₂') hdom (bw :: cw), hceq]
  · have hlwf : contains σ₀' bw = false := by
      cases h : contains σ₀' bw with
      | true => exact absurd h hlw
      | false => rfl
    rw [climb_fixpoint (fun y => anc σ₀' y) (survivors σ₀' σ₁' σ₂') bw (hbwsurv hlwf)]
    exact (hbout hlwf).symm

/-- A branch-born, branch-live node is a survivor. -/
theorem survivors_of_branch (σ₀' σ₁' σ₂' : concrete_st α) (c : ℕ)
    (hnl : contains σ₀' c = false)
    (hbr : contains σ₁' c = true ∨ contains σ₂' c = true) :
    survivors σ₀' σ₁' σ₂' c = true := by
  cases h1 : contains σ₁' c <;> cases h2 : contains σ₂' c <;>
    simp_all [survivors, union, intersection, difference]

/-- **The 0-or-survivor fact, derived.**  The birth anchor is read off the state where the
survivor lives; `Hstay`/`wf` make it root-or-live THERE; a non-LCA live anchor of a branch state
is branch-born-or… in every case, off the LCA it is `0` or a survivor. -/
theorem bwsurv_of_wf (σ₀' σ₁' σ₂' : concrete_st α) (t : ℕ)
    (Hstay : ∀ y, contains σ₀' y = true → (anc σ₀' y = 0 ∨ contains σ₀' (anc σ₀' y) = true))
    (hwf1 : ∀ y, contains σ₁' y = true → (anc σ₁' y = 0 ∨ contains σ₁' (anc σ₁' y) = true))
    (hwf2 : ∀ y, contains σ₂' y = true → (anc σ₂' y = 0 ∨ contains σ₂' (anc σ₂' y) = true))
    (hin : contains σ₀' t = true ∨ contains σ₁' t = true ∨ contains σ₂' t = true)
    (hnl : contains σ₀' (birthAnc σ₀' σ₁' σ₂' t) = false) :
    birthAnc σ₀' σ₁' σ₂' t = 0 ∨ survivors σ₀' σ₁' σ₂' (birthAnc σ₀' σ₁' σ₂' t) = true := by
  unfold birthAnc at hnl ⊢
  by_cases h0t : contains σ₀' t = true
  · rw [if_pos h0t] at hnl ⊢
    rcases Hstay t h0t with h | h
    · exact Or.inl h
    · rw [h] at hnl; exact absurd hnl (by simp)
  · rw [if_neg h0t] at hnl ⊢
    by_cases h1t : contains σ₁' t = true
    · rw [if_pos h1t] at hnl ⊢
      rcases hwf1 t h1t with h | h
      · exact Or.inl h
      · exact Or.inr (survivors_of_branch σ₀' σ₁' σ₂' _ hnl (Or.inl h))
    · rw [if_neg h1t] at hnl ⊢
      have h2t : contains σ₂' t = true := by
        rcases hin with h | h | h
        · exact absurd h h0t
        · exact absurd h h1t
        · exact h
      rcases hwf2 t h2t with h | h
      · exact Or.inl h
      · exact Or.inr (survivors_of_branch σ₀' σ₁' σ₂' _ hnl (Or.inr h))

/-- **The corrected merge glue.**  As `canonMatch_merge_of_inputs`, with the birth-anchor
0-or-survivor conjunct REMOVED from the bridge bundle (it is derived from the branch `wf` facts),
so the per-survivor leaf is `CanonBirthBridge` alone. -/
theorem canonMatch_merge_of_inputs'
    (σ₀' σ₁' σ₂' : concrete_st α) (ρ₀ π₀ ρ₁ ρ₂ : List (op_t α))
    (hcm0 : CanonMatch ρ₀ σ₀') (hcm1 : CanonMatch ρ₁ σ₁') (hcm2 : CanonMatch ρ₂ σ₂')
    (Hdec : ∀ y, contains σ₀' y = true → y ≠ 0 → anc σ₀' y < y)
    (Hstay : ∀ y, contains σ₀' y = true → (anc σ₀' y = 0 ∨ contains σ₀' (anc σ₀' y) = true))
    (hwf1 : ∀ y, contains σ₁' y = true → (anc σ₁' y = 0 ∨ contains σ₁' (anc σ₁' y) = true))
    (hwf2 : ∀ y, contains σ₂' y = true → (anc σ₂' y = 0 ∨ contains σ₂' (anc σ₂' y) = true))
    (h0 : contains σ₀' 0 = false)
    (hcaus : ∀ c, (insertedIn ρ₀ c ↔ insertedIn ρ₁ c ∧ insertedIn ρ₂ c)
        ∧ (deletedIn ρ₁ c → insertedIn ρ₁ c) ∧ (deletedIn ρ₂ c → insertedIn ρ₂ c)
        ∧ (deletedIn ρ₀ c → deletedIn ρ₁ c) ∧ (deletedIn ρ₀ c → deletedIn ρ₂ c)
        ∧ (insertedIn (ρ₀ ++ π₀) c ↔ insertedIn ρ₁ c ∨ insertedIn ρ₂ c)
        ∧ (deletedIn (ρ₀ ++ π₀) c ↔ deletedIn ρ₁ c ∨ deletedIn ρ₂ c))
    (hins_branch : ∀ (t r : ℕ) (e : α) (a : ℕ) (p : List ℕ),
        (t, r, .Ins e p a) ∈ ρ₀ ++ π₀ → survP (ρ₀ ++ π₀) t →
        (contains σ₀' t = true → (t, r, .Ins e p a) ∈ ρ₀)
        ∧ (contains σ₁' t = true → (t, r, .Ins e p a) ∈ ρ₁)
        ∧ (contains σ₂' t = true → (t, r, .Ins e p a) ∈ ρ₂)
        ∧ (contains σ₀' t = true ∨ contains σ₁' t = true ∨ contains σ₂' t = true))
    (hbridge : ∀ (t r : ℕ) (e : α) (a : ℕ) (p : List ℕ),
        (t, r, .Ins e p a) ∈ ρ₀ ++ π₀ → survP (ρ₀ ++ π₀) t →
        CanonBirthBridge σ₀' (ρ₀ ++ π₀) (birthAnc σ₀' σ₁' σ₂' t) (a :: p)) :
    CanonMatch (ρ₀ ++ π₀) (merge σ₀' σ₁' σ₂') := by
  have hdomain : ∀ c, contains (merge σ₀' σ₁' σ₂') c = true ↔ survP (ρ₀ ++ π₀) c := by
    intro c
    obtain ⟨hI0, hD1I, hD2I, hD01, hD02, hIu, hDu⟩ := hcaus c
    exact merge_domain_clause σ₀' σ₁' σ₂' ρ₀ π₀ ρ₁ ρ₂ c
      (hcm0.1 c) (hcm1.1 c) (hcm2.1 c) hI0 hD1I hD2I hD01 hD02 hIu hDu
  refine merge_canonMatch σ₀' σ₁' σ₂' (ρ₀ ++ π₀) hdomain ?_ ?_
  · intro t r e a p hins hsv
    obtain ⟨hs0, hs1, hs2, hib⟩ := hins_branch t r e a p hins hsv
    exact merge_el_clause σ₀' σ₁' σ₂' ρ₀ ρ₁ ρ₂ t r e a p hcm0 hcm1 hcm2 hs0 hs1 hs2 hib
  · intro t r e a p hins hsv
    have hbr := hbridge t r e a p hins hsv
    have hib := (hins_branch t r e a p hins hsv).2.2.2
    exact merge_anc_clause' σ₀' σ₁' σ₂' (ρ₀ ++ π₀) t a p Hdec Hstay h0 hdomain hbr
      (fun hnl => bwsurv_of_wf σ₀' σ₁' σ₂' t Hstay hwf1 hwf2 hib hnl)

/-! ## Axiom audit -/

#print axioms merge_anc_clause'
#print axioms bwsurv_of_wf
#print axioms canonMatch_merge_of_inputs'

end Sal.ConditionedMRDTs.RGAMergeCanon
