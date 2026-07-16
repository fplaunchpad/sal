import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_Skeleton3
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_MergeCanon_Fix

/-!
# Skeleton 3 leaf reduction — `hCanon` from a MINIMAL merge bundle

*Additive; modifies no existing file; 0 `sorry`.*

In the H-world the witnesses CARRY the engine discipline (`CanonFoldOK [] (init_st (α := α)) ρᵢ`), so:

* every `CanonMatch` derives directly (`canon_fold` + `canonMatch_of_canonInv`) — **no
  `EngineReady`, no `RefEdge`, no `hReady` leg anywhere**;
* `CanonInv` at every fold is free, so the σ-forest facts (`Hstay`/`h0`/branch `wf`) and the
  per-survivor membership bundle (`hins_branch`) are DERIVED, not leaves;
* the corrected merge glue (`canonMatch_merge_of_inputs'`, `RGA_MergeCanon_Fix`) needs only
  `CanonBirthBridge` per survivor — the false 0-or-survivor conjunct is gone.

`hCanon_of_leaves3` therefore reduces Skeleton 3's `hCanon` to THREE leaves:
`Hdec` (σ₀' id-monotonicity — a fold invariant from honest payload bounds), `hcaus` (the per-id
causal set-algebra; its two provenance clauses are the honest content), and `hbridge`
(per-survivor `CanonBirthBridge` — the `BranchInv`-I4 kernel).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open Classical

namespace Sal.ConditionedMRDTs.RGASkeleton3

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA)
open Sal.ConditionedMRDTs.RGAMergeCanon (canonMatch_merge_of_inputs')
open Sal.ConditionedMRDTs.RGACorrectedResidual (canonFoldOK_concat)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonMatch CanonFoldOK CanonInv canon_fold canonInv_init
  canonMatch_of_canonInv survP insertedIn deletedIn)
open RGAMergeFoldChain (CanonBirthBridge)

/-- **A disciplined enumeration folds to its canonical invariant.** -/
theorem canonInv_of_canonFoldOK (ρ : List (op_t α)) (h : CanonFoldOK [] (init_st (α := α)) ρ) :
    CanonInv ρ (applySeqR (init_st (α := α)) ρ) := by
  have hci := canon_fold ρ [] (init_st (α := α)) canonInv_init h
  rwa [List.nil_append] at hci

/-- **A disciplined enumeration folds to its canonical state.** -/
theorem canonMatch_of_canonFoldOK (ρ : List (op_t α)) (h : CanonFoldOK [] (init_st (α := α)) ρ) :
    CanonMatch ρ (applySeqR (init_st (α := α)) ρ) :=
  canonMatch_of_canonInv ρ _ (canonInv_of_canonFoldOK ρ h)

/-- **All four `CanonMatch`es from the Skeleton-3 disciplines** — no `EngineReady` anywhere. -/
theorem hFoldCanon3 (ρ₀ ρ₁ ρ₂ π₀ : List (op_t α))
    (h₀OK : CanonFoldOK [] (init_st (α := α)) ρ₀)
    (h₁OK : CanonFoldOK [] (init_st (α := α)) ρ₁)
    (h₂OK : CanonFoldOK [] (init_st (α := α)) ρ₂)
    (hπOK : CanonFoldOK ρ₀ (applySeqR (init_st (α := α)) ρ₀) π₀) :
    CanonMatch ρ₀ (applySeqR (init_st (α := α)) ρ₀) ∧ CanonMatch ρ₁ (applySeqR (init_st (α := α)) ρ₁)
      ∧ CanonMatch ρ₂ (applySeqR (init_st (α := α)) ρ₂)
      ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR (init_st (α := α)) ρ₀) π₀) := by
  refine ⟨canonMatch_of_canonFoldOK ρ₀ h₀OK, canonMatch_of_canonFoldOK ρ₁ h₁OK,
    canonMatch_of_canonFoldOK ρ₂ h₂OK, ?_⟩
  have hcat : CanonFoldOK [] (init_st (α := α)) (ρ₀ ++ π₀) :=
    canonFoldOK_concat ρ₀ [] (init_st (α := α)) π₀ h₀OK hπOK
  have hcm := canonMatch_of_canonFoldOK (ρ₀ ++ π₀) hcat
  have happ : applySeqR (init_st (α := α)) (ρ₀ ++ π₀) = applySeqR (applySeqR (init_st (α := α)) ρ₀) π₀ := by
    simp only [applySeqR, List.foldl_append]
  rw [happ] at hcm
  exact hcm

/-- **Skeleton 3's `hCanon` from the MINIMAL merge bundle** — `Hdec` (σ₀' id-monotonicity),
`hcaus` (per-id causal set-algebra), and per-survivor `CanonBirthBridge`.  Everything else —
the four `CanonMatch`es, the σ-forest facts, the branch `wf`s, and the per-survivor membership —
is derived from the carried disciplines. -/
theorem hCanon_of_leaves3
    (HonJ : (op_t α → op_t α → Prop) → Set (op_t α) → Prop)
    (hMergeInputs : ∀ (vis : op_t α → op_t α → Prop) (events ev₁ ev₂ : Set (op_t α)) (ρ₀ ρ₁ ρ₂ π₀ : List (op_t α)),
        HonJ vis events →
        (∀ {a b c : op_t α}, vis a b → vis b c → vis a c) → (∀ a : op_t α, ¬ vis a a) →
        (∀ a b : op_t α, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := (RGACondSig' α)) vis ev₁ → fullClosureRel (D := (RGACondSig' α)) vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq (rgaEqEquiv' α) WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        CanonFoldOK [] (init_st (α := α)) ρ₀ → CanonFoldOK [] (init_st (α := α)) ρ₁ → CanonFoldOK [] (init_st (α := α)) ρ₂ →
        CanonFoldOK ρ₀ (applySeqR (init_st (α := α)) ρ₀) π₀ →
        (∀ y, contains (applySeqR (init_st (α := α)) ρ₀) y = true → y ≠ 0 → anc (applySeqR (init_st (α := α)) ρ₀) y < y)
        ∧ (∀ c, (insertedIn ρ₀ c ↔ insertedIn ρ₁ c ∧ insertedIn ρ₂ c)
            ∧ (deletedIn ρ₁ c → insertedIn ρ₁ c) ∧ (deletedIn ρ₂ c → insertedIn ρ₂ c)
            ∧ (deletedIn ρ₀ c → deletedIn ρ₁ c) ∧ (deletedIn ρ₀ c → deletedIn ρ₂ c)
            ∧ (insertedIn (ρ₀ ++ π₀) c ↔ insertedIn ρ₁ c ∨ insertedIn ρ₂ c)
            ∧ (deletedIn (ρ₀ ++ π₀) c ↔ deletedIn ρ₁ c ∨ deletedIn ρ₂ c))
        ∧ (∀ (t r : ℕ) (e : α) (a : ℕ) (p : List ℕ),
            (t, r, .Ins e p a) ∈ ρ₀ ++ π₀ → survP (ρ₀ ++ π₀) t →
            CanonBirthBridge (applySeqR (init_st (α := α)) ρ₀) (ρ₀ ++ π₀)
                (birthAnc (applySeqR (init_st (α := α)) ρ₀) (applySeqR (init_st (α := α)) ρ₁) (applySeqR (init_st (α := α)) ρ₂) t) (a :: p))) :
    ∀ (vis : op_t α → op_t α → Prop) (events ev₁ ev₂ : Set (op_t α)) (ρ₀ ρ₁ ρ₂ π₀ : List (op_t α)),
        HonJ vis events →
        (∀ {a b c : op_t α}, vis a b → vis b c → vis a c) → (∀ a : op_t α, ¬ vis a a) →
        (∀ a b : op_t α, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := (RGACondSig' α)) vis ev₁ → fullClosureRel (D := (RGACondSig' α)) vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq (rgaEqEquiv' α) WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        CanonFoldOK [] (init_st (α := α)) ρ₀ → CanonFoldOK [] (init_st (α := α)) ρ₁ → CanonFoldOK [] (init_st (α := α)) ρ₂ →
        CanonFoldOK ρ₀ (applySeqR (init_st (α := α)) ρ₀) π₀ →
        CanonMatch (ρ₀ ++ π₀)
            (merge (applySeqR (init_st (α := α)) ρ₀) (applySeqR (init_st (α := α)) ρ₁) (applySeqR (init_st (α := α)) ρ₂))
          ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR (init_st (α := α)) ρ₀) π₀) := by
  intro vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ hHonJ htr hir hdts hev1 hev2 hcl1 hcl2 h0p h1p h2p hπp hπr
    h₀OK h₁OK h₂OK hπOK
  obtain ⟨hcm0, hcm1, hcm2, hfold⟩ := hFoldCanon3 ρ₀ ρ₁ ρ₂ π₀ h₀OK h₁OK h₂OK hπOK
  obtain ⟨Hdec, hcaus, hbridge⟩ :=
    hMergeInputs vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ hHonJ htr hir hdts hev1 hev2 hcl1 hcl2
      h0p h1p h2p hπp hπr h₀OK h₁OK h₂OK hπOK
  -- the canonical invariants at the three folds
  have hci0 : CanonInv ρ₀ (applySeqR (init_st (α := α)) ρ₀) := canonInv_of_canonFoldOK ρ₀ h₀OK
  have hci1 : CanonInv ρ₁ (applySeqR (init_st (α := α)) ρ₁) := canonInv_of_canonFoldOK ρ₁ h₁OK
  have hci2 : CanonInv ρ₂ (applySeqR (init_st (α := α)) ρ₂) := canonInv_of_canonFoldOK ρ₂ h₂OK
  -- derived σ-forest facts
  have h0σ : contains (applySeqR (init_st (α := α)) ρ₀) 0 = false := hci0.1
  have Hstay : ∀ y, contains (applySeqR (init_st (α := α)) ρ₀) y = true →
      (anc (applySeqR (init_st (α := α)) ρ₀) y = 0
        ∨ contains (applySeqR (init_st (α := α)) ρ₀) (anc (applySeqR (init_st (α := α)) ρ₀) y) = true) :=
    fun y hy => hci0.2.1 y hy
  have hwf1 : ∀ y, contains (applySeqR (init_st (α := α)) ρ₁) y = true →
      (anc (applySeqR (init_st (α := α)) ρ₁) y = 0
        ∨ contains (applySeqR (init_st (α := α)) ρ₁) (anc (applySeqR (init_st (α := α)) ρ₁) y) = true) :=
    fun y hy => hci1.2.1 y hy
  have hwf2 : ∀ y, contains (applySeqR (init_st (α := α)) ρ₂) y = true →
      (anc (applySeqR (init_st (α := α)) ρ₂) y = 0
        ∨ contains (applySeqR (init_st (α := α)) ρ₂) (anc (applySeqR (init_st (α := α)) ρ₂) y) = true) :=
    fun y hy => hci2.2.1 y hy
  -- op identity from id-uniqueness on the ambient event universe
  have hmemU : ∀ a, a ∈ ρ₀ ++ π₀ → a ∈ events := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hev1 a ((h0p.2 a).mp h).1
    · rcases ((hπp.2 a).mp h).1 with h' | h'
      · exact hev1 a h'
      · exact hev2 a h'
  have hopEq : ∀ {o o' : op_t α}, o ∈ events → o' ∈ events → o.1 = o'.1 → o = o' := by
    intro o o' ho ho' hid
    by_contra hne
    exact hdts o o' ho ho' hne hid
  -- derived per-survivor membership bundle
  have hins_branch : ∀ (t r : ℕ) (e : α) (a : ℕ) (p : List ℕ),
      (t, r, .Ins e p a) ∈ ρ₀ ++ π₀ → survP (ρ₀ ++ π₀) t →
      (contains (applySeqR (init_st (α := α)) ρ₀) t = true → (t, r, .Ins e p a) ∈ ρ₀)
      ∧ (contains (applySeqR (init_st (α := α)) ρ₁) t = true → (t, r, .Ins e p a) ∈ ρ₁)
      ∧ (contains (applySeqR (init_st (α := α)) ρ₂) t = true → (t, r, .Ins e p a) ∈ ρ₂)
      ∧ (contains (applySeqR (init_st (α := α)) ρ₀) t = true ∨ contains (applySeqR (init_st (α := α)) ρ₁) t = true
          ∨ contains (applySeqR (init_st (α := α)) ρ₂) t = true) := by
    intro t r e a p hins hsv
    have hoursE : (t, r, .Ins e p a) ∈ events := hmemU _ hins
    have hpick : ∀ (ρ : List (op_t α)) (evs : Set (op_t α)), listPermOf ρ evs →
        (∀ x ∈ evs, x ∈ events) → insertedIn ρ t → (t, r, .Ins e p a) ∈ ρ := by
      intro ρ evs hperm hsub hinst
      obtain ⟨r', e', p', a', hm⟩ := hinst
      have hmE : (t, r', .Ins e' p' a') ∈ events := hsub _ ((hperm.2 _).mp hm)
      have heq := hopEq hmE hoursE rfl
      exact heq ▸ hm
    obtain ⟨hI0, hD1I, hD2I, hD01, hD02, hIu, hDu⟩ := hcaus t
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hc0
      exact hpick ρ₀ (ev₁ ∩ ev₂) h0p (fun x hx => hev1 x hx.1)
        ((hci0.2.2.1 t).mp hc0).1
    · intro hc1
      exact hpick ρ₁ ev₁ h1p hev1 ((hci1.2.2.1 t).mp hc1).1
    · intro hc2
      exact hpick ρ₂ ev₂ h2p hev2 ((hci2.2.2.1 t).mp hc2).1
    · -- a union survivor lives in the branch that inserted it
      have hnotdel : ¬ deletedIn (ρ₀ ++ π₀) t := hsv.2
      have hnd1 : ¬ deletedIn ρ₁ t := fun h => hnotdel (hDu.mpr (Or.inl h))
      have hnd2 : ¬ deletedIn ρ₂ t := fun h => hnotdel (hDu.mpr (Or.inr h))
      rcases hIu.mp hsv.1 with h | h
      · exact Or.inr (Or.inl ((hci1.2.2.1 t).mpr ⟨h, hnd1⟩))
      · exact Or.inr (Or.inr ((hci2.2.2.1 t).mpr ⟨h, hnd2⟩))
  exact ⟨canonMatch_merge_of_inputs' (applySeqR (init_st (α := α)) ρ₀) (applySeqR (init_st (α := α)) ρ₁)
      (applySeqR (init_st (α := α)) ρ₂) ρ₀ π₀ ρ₁ ρ₂ hcm0 hcm1 hcm2 Hdec Hstay hwf1 hwf2 h0σ hcaus
      hins_branch hbridge,
    hfold⟩

/-! ## Axiom audit -/

#print axioms canonInv_of_canonFoldOK
#print axioms canonMatch_of_canonFoldOK
#print axioms hFoldCanon3
#print axioms hCanon_of_leaves3

end Sal.ConditionedMRDTs.RGASkeleton3
