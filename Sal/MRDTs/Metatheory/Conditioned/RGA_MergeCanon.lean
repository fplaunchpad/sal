import Sal.MRDTs.Metatheory.Conditioned.RGA_CanonMatch_Reachable

/-!
# The MERGE half of `hCanon` — `CanonMatch (ρ₀++π₀) (merge σ₀' σ₁' σ₂')`

*Additive; modifies no existing file; 0 `sorry`.*

The RGA-specific fact: the OR-set merge computes the canonical state of the union events. Two clauses:
* **domain** (`merge_domain_clause`): `contains (merge …) = survP (ρ₀++π₀)` — the OR-set = union
  survivor set. A Boolean/causal identity: OR-set survival over the branch survivor sets equals union
  survival, using id-uniqueness (`I₀↔I₁∧I₂`), closed-deletes (`Dⱼ→Iⱼ`), and subset (`D₀→Dⱼ`).
* **anchor** (later): `anc (merge …) t = canonAnc (ρ₀++π₀) (a::p)` — via `canonBirthBridge_of_branchChain`.

The causal facts are carried as explicit hypotheses here (skeleton-first); they are discharged from
`fullClosureRel` + distinctness + the branch perms in the execution-model plumbing step.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.Metatheory.RGAMergeCanon

open Sal.Emulation
open RGACanonConvergence (survP insertedIn deletedIn CanonMatch canonAnc resolve_eq_canonAnc)
open RGAMergeLinearization (contains_eq_domain)
open RGAMergeLinearizationTwoSided (birthEl)
open RGAMergeFoldChain (CanonBirthBridge)
open RGAMergeBranchNew (resolve_climb_start)

/-- The OR-set-vs-union survivor identity as a PURELY propositional fact (6 abstract atoms), so the
`tauto` never meets the `∃`-valued `insertedIn`/`deletedIn`. `I₀↔I₁∧I₂` (id-uniqueness), `Dⱼ→Iⱼ`
(closed deletes), `D₀→Dⱼ` (subset) are exactly what makes it hold. -/
theorem orset_survP_iff (I0 I1 I2 D0 D1 D2 : Prop)
    (hI0 : I0 ↔ I1 ∧ I2) (hD1I : D1 → I1) (hD2I : D2 → I2)
    (hD01 : D0 → D1) (hD02 : D0 → D2) :
    (((I0 ∧ ¬D0) ∧ (I1 ∧ ¬D1) ∧ (I2 ∧ ¬D2))
        ∨ ((I1 ∧ ¬D1) ∧ ¬(I0 ∧ ¬D0)) ∨ ((I2 ∧ ¬D2) ∧ ¬(I0 ∧ ¬D0)))
      ↔ ((I1 ∨ I2) ∧ ¬(D1 ∨ D2)) := by
  tauto

/-- **Merge domain clause.**  The OR-set merge's domain equals the union survivor set `survP
(ρ₀++π₀)`, given each branch's canonical domain characterization (`hb₀/hb₁/hb₂`) and the causal facts
(id-uniqueness `hI0`, closed-deletes `hD1I/hD2I`, subset `hD01/hD02`, union membership `hIu/hDu`). -/
theorem merge_domain_clause
    (σ₀' σ₁' σ₂' : concrete_st) (ρ₀ π₀ ρ₁ ρ₂ : List op_t) (c : ℕ)
    (hb0 : contains σ₀' c = true ↔ survP ρ₀ c)
    (hb1 : contains σ₁' c = true ↔ survP ρ₁ c)
    (hb2 : contains σ₂' c = true ↔ survP ρ₂ c)
    (hI0 : insertedIn ρ₀ c ↔ insertedIn ρ₁ c ∧ insertedIn ρ₂ c)
    (hD1I : deletedIn ρ₁ c → insertedIn ρ₁ c)
    (hD2I : deletedIn ρ₂ c → insertedIn ρ₂ c)
    (hD01 : deletedIn ρ₀ c → deletedIn ρ₁ c)
    (hD02 : deletedIn ρ₀ c → deletedIn ρ₂ c)
    (hIu : insertedIn (ρ₀ ++ π₀) c ↔ insertedIn ρ₁ c ∨ insertedIn ρ₂ c)
    (hDu : deletedIn (ρ₀ ++ π₀) c ↔ deletedIn ρ₁ c ∨ deletedIn ρ₂ c) :
    contains (merge σ₀' σ₁' σ₂') c = true ↔ survP (ρ₀ ++ π₀) c := by
  rw [contains_merge]
  -- (1) the pure Boolean shape of `survivors` — no `survP`, cheap 8-way on concrete Bools
  have key : survivors σ₀' σ₁' σ₂' c = true ↔
      ((contains σ₀' c = true ∧ contains σ₁' c = true ∧ contains σ₂' c = true)
        ∨ (contains σ₁' c = true ∧ contains σ₀' c ≠ true)
        ∨ (contains σ₂' c = true ∧ contains σ₀' c ≠ true)) := by
    simp only [survivors, union, intersection, difference, ← contains_eq_domain]
    cases contains σ₀' c <;> cases contains σ₁' c <;> cases contains σ₂' c <;> simp
  rw [key]
  -- (2) the causal identity, `insertedIn`/`deletedIn` kept opaque via the propositional lemma
  simp only [ne_eq, hb0, hb1, hb2, survP]
  rw [hIu, hDu]
  exact orset_survP_iff (insertedIn ρ₀ c) (insertedIn ρ₁ c) (insertedIn ρ₂ c)
    (deletedIn ρ₀ c) (deletedIn ρ₁ c) (deletedIn ρ₂ c) hI0 hD1I hD2I hD01 hD02

#print axioms merge_domain_clause

/-- **Merge el clause.**  A survivor's element in the merge is its recorded element `e`.
`el (merge …) = birthEl` (rfl); `birthEl` reads the branch where the node lives, and each branch's
canonical `el` (from `CanonMatch ρᵢ σᵢ'`) returns the recorded `e` for that node's unique `Ins`.
The "node's `Ins` is in the branch it survives in" facts (`hsurvᵢ`, from id-uniqueness) and
"a survivor is in some branch" (`hin_branch`, from the domain clause) are carried as hypotheses. -/
theorem merge_el_clause
    (σ₀' σ₁' σ₂' : concrete_st) (ρ₀ ρ₁ ρ₂ : List op_t) (t r e a : ℕ) (p : List ℕ)
    (hcm0 : CanonMatch ρ₀ σ₀') (hcm1 : CanonMatch ρ₁ σ₁') (hcm2 : CanonMatch ρ₂ σ₂')
    (hsurv0 : contains σ₀' t = true → (t, r, .Ins e p a) ∈ ρ₀)
    (hsurv1 : contains σ₁' t = true → (t, r, .Ins e p a) ∈ ρ₁)
    (hsurv2 : contains σ₂' t = true → (t, r, .Ins e p a) ∈ ρ₂)
    (hin_branch : contains σ₀' t = true ∨ contains σ₁' t = true ∨ contains σ₂' t = true) :
    el (merge σ₀' σ₁' σ₂') t = e := by
  rw [show el (merge σ₀' σ₁' σ₂') t = birthEl σ₀' σ₁' σ₂' t from rfl, birthEl]
  by_cases h0 : contains σ₀' t = true
  · rw [if_pos h0]
    exact (hcm0.2 t r e p a (hsurv0 h0) ((hcm0.1 t).mp h0)).1
  · rw [if_neg h0]
    by_cases h1 : contains σ₁' t = true
    · rw [if_pos h1]
      exact (hcm1.2 t r e p a (hsurv1 h1) ((hcm1.1 t).mp h1)).1
    · rw [if_neg h1]
      have h2 : contains σ₂' t = true := by
        rcases hin_branch with h | h | h
        · exact absurd h h0
        · exact absurd h h1
        · exact h
      exact (hcm2.2 t r e p a (hsurv2 h2) ((hcm2.1 t).mp h2)).1

#print axioms merge_el_clause

/-- **Merge anchor clause.**  A survivor's anchor in the merge is `canonAnc F` of its recorded chain.
`anc (merge …) = climb (anc σ₀') survivors birthAnc` (rfl); via `resolve_climb_start` the climb is
`resolve (merge) (bw::cw)`, which is `canonAnc F (bw::cw)` (`resolve_eq_canonAnc`, domain clause), and
`CanonBirthBridge` reconciles that with `canonAnc F (a::p)`. Off-forest, `climb_fixpoint` collapses the
climb to `bw = canonAnc F (a::p)`. The birth-anchor's forest chain is `CanonBirthBridge`'s content;
`Hdec`/`Hstay`/`h0` (σ₀' forest invariants) and `hbwsurv` (birth-anchor is 0-or-survivor) are carried. -/
theorem merge_anc_clause
    (σ₀' σ₁' σ₂' : concrete_st) (F : List op_t) (t a : ℕ) (p : List ℕ)
    (Hdec : ∀ y, contains σ₀' y = true → y ≠ 0 → anc σ₀' y < y)
    (Hstay : ∀ y, contains σ₀' y = true → (anc σ₀' y = 0 ∨ contains σ₀' (anc σ₀' y) = true))
    (h0 : contains σ₀' 0 = false)
    (hdom : ∀ c, contains (merge σ₀' σ₁' σ₂') c = true ↔ survP F c)
    (hbridge : CanonBirthBridge σ₀' F (birthAnc σ₀' σ₁' σ₂' t) (a :: p))
    (hbwsurv : birthAnc σ₀' σ₁' σ₂' t = 0
        ∨ survivors σ₀' σ₁' σ₂' (birthAnc σ₀' σ₁' σ₂' t) = true) :
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
    rw [climb_fixpoint (fun y => anc σ₀' y) (survivors σ₀' σ₁' σ₂') bw hbwsurv]
    exact (hbout hlwf).symm

#print axioms merge_anc_clause

/-- **`CanonMatch F (merge σ₀' σ₁' σ₂')`** — the RGA merge computes the canonical state of the union
events, assembled from the three per-clause results (domain / el / anc). This is the SOLE RGA-specific
input to the canonical route (`RGA_EndToEnd.hCanon`'s merge half); everything else is generic. -/
theorem merge_canonMatch
    (σ₀' σ₁' σ₂' : concrete_st) (F : List op_t)
    (hdomain : ∀ c, contains (merge σ₀' σ₁' σ₂') c = true ↔ survP F c)
    (hel : ∀ (t r e a : ℕ) (p : List ℕ),
        (t, r, .Ins e p a) ∈ F → survP F t → el (merge σ₀' σ₁' σ₂') t = e)
    (hanc : ∀ (t r e a : ℕ) (p : List ℕ),
        (t, r, .Ins e p a) ∈ F → survP F t →
        anc (merge σ₀' σ₁' σ₂') t = canonAnc F (a :: p)) :
    CanonMatch F (merge σ₀' σ₁' σ₂') :=
  ⟨hdomain, fun t r e p a hins hsv => ⟨hel t r e a p hins hsv, hanc t r e a p hins hsv⟩⟩

#print axioms merge_canonMatch

/-- **Merge-side glue.**  Assembles `CanonMatch (ρ₀++π₀) (merge σ₀' σ₁' σ₂')` from the leaf inputs,
precisely typing the residual: the three branch `CanonMatch` (`hcmᵢ`), σ₀' forest invariants
(`Hdec`/`Hstay`/`h0`), the per-id causal facts (`hcaus`), per-survivor membership (`hins_branch`),
and per-survivor `CanonBirthBridge` + 0-or-survivor birth-anchor (`hbridge`). Everything else is the
three clause lemmas (done). What LEFT to discharge is exactly these five hypotheses. -/
theorem canonMatch_merge_of_inputs
    (σ₀' σ₁' σ₂' : concrete_st) (ρ₀ π₀ ρ₁ ρ₂ : List op_t)
    (hcm0 : CanonMatch ρ₀ σ₀') (hcm1 : CanonMatch ρ₁ σ₁') (hcm2 : CanonMatch ρ₂ σ₂')
    (Hdec : ∀ y, contains σ₀' y = true → y ≠ 0 → anc σ₀' y < y)
    (Hstay : ∀ y, contains σ₀' y = true → (anc σ₀' y = 0 ∨ contains σ₀' (anc σ₀' y) = true))
    (h0 : contains σ₀' 0 = false)
    (hcaus : ∀ c, (insertedIn ρ₀ c ↔ insertedIn ρ₁ c ∧ insertedIn ρ₂ c)
        ∧ (deletedIn ρ₁ c → insertedIn ρ₁ c) ∧ (deletedIn ρ₂ c → insertedIn ρ₂ c)
        ∧ (deletedIn ρ₀ c → deletedIn ρ₁ c) ∧ (deletedIn ρ₀ c → deletedIn ρ₂ c)
        ∧ (insertedIn (ρ₀ ++ π₀) c ↔ insertedIn ρ₁ c ∨ insertedIn ρ₂ c)
        ∧ (deletedIn (ρ₀ ++ π₀) c ↔ deletedIn ρ₁ c ∨ deletedIn ρ₂ c))
    (hins_branch : ∀ (t r e a : ℕ) (p : List ℕ),
        (t, r, .Ins e p a) ∈ ρ₀ ++ π₀ → survP (ρ₀ ++ π₀) t →
        (contains σ₀' t = true → (t, r, .Ins e p a) ∈ ρ₀)
        ∧ (contains σ₁' t = true → (t, r, .Ins e p a) ∈ ρ₁)
        ∧ (contains σ₂' t = true → (t, r, .Ins e p a) ∈ ρ₂)
        ∧ (contains σ₀' t = true ∨ contains σ₁' t = true ∨ contains σ₂' t = true))
    (hbridge : ∀ (t r e a : ℕ) (p : List ℕ),
        (t, r, .Ins e p a) ∈ ρ₀ ++ π₀ → survP (ρ₀ ++ π₀) t →
        CanonBirthBridge σ₀' (ρ₀ ++ π₀) (birthAnc σ₀' σ₁' σ₂' t) (a :: p)
        ∧ (birthAnc σ₀' σ₁' σ₂' t = 0
            ∨ survivors σ₀' σ₁' σ₂' (birthAnc σ₀' σ₁' σ₂' t) = true)) :
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
    obtain ⟨hbr, hbws⟩ := hbridge t r e a p hins hsv
    exact merge_anc_clause σ₀' σ₁' σ₂' (ρ₀ ++ π₀) t a p Hdec Hstay h0 hdomain hbr hbws

#print axioms canonMatch_merge_of_inputs

end Sal.Metatheory.RGAMergeCanon
