import Sal.MRDTs.Instances.EfficientORSetGCSPOT

/-! # Head-only GC with an unchanged historical base

This module studies one common two-record state and arbitrary fresh update
continuations on its two branches. It does not rewrite the merge base.
-/

namespace Sal.MRDTs.Instances.EfficientORSet.HeadGC
open Sal.MRDTs.Foundation
open GCResearch

theorem erase_fold (d : Record Nat) (s : State Nat)
    (ops : List (Op (SetOp Nat)))
    (fresh : ∀ e ∈ ops, e.1 ≠ d.2.1) :
    (ops.foldl update s).erase d = ops.foldl update (s.erase d) := by
  induction ops generalizing s with
  | nil => rfl
  | cons e es ih =>
      simp only [List.foldl_cons]
      rw [ih _ (fun z hz => fresh z (List.mem_cons_of_mem e hz))]
      rw [erase_update d s e (fresh e (by simp))]

/-- Erasing a redundant initial record preserves membership through any
fresh sequential continuation, even when the retained record is replaced. -/
theorem erase_fold_elements (d a : Record Nat) (s : State Nat)
    (ha : a ∈ s) (different : a ≠ d) (same : a.2.2 = d.2.2)
    (ops : List (Op (SetOp Nat)))
    (fresh : ∀ e ∈ ops, e.1 ≠ d.2.1) :
    elements ((ops.foldl update s).erase d) = elements (ops.foldl update s) := by
  rw [erase_fold d s ops fresh, elements_fold, elements_fold,
    erase_elements d a s ha different same]

/-- When the discarded record is in the ORIGINAL base, collecting only one
head erases that record from the merge result; it cannot resurrect it. -/
theorem merge_erase_left (d : Record Nat) (l a b : State Nat) (hd : d ∈ l) :
    merge l (a.erase d) b = (merge l a b).erase d := by
  ext p
  simp only [merge, Finset.mem_erase, Finset.mem_union, Finset.mem_inter,
    Finset.mem_sdiff]
  by_cases h : p = d
  · subst p; simp [hd]
  · tauto

theorem merge_erase_right (d : Record Nat) (l a b : State Nat) (hd : d ∈ l) :
    merge l a (b.erase d) = (merge l a b).erase d := by
  rw [merge_comm l a (b.erase d), merge_erase_left d l b a hd, merge_comm l b a]

/-- The base has just the two records a and d for this element. If each
branch still has a witness other than d whenever d is live, the merged state
does too. Other elements and arbitrarily many fresh branch records are allowed. -/
theorem merge_keeps_witness (d a : Record Nat) (l left right : State Nat)
    (base : ∀ p ∈ l, p.2.2 = d.2.2 → p = a ∨ p = d)
    (hl : elements (left.erase d) = elements left)
    (hr : elements (right.erase d) = elements right)
    (hd : d ∈ l) :
    elements ((merge l left right).erase d) = elements (merge l left right) := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨p, (Finset.mem_erase.mp hp).2, hpx⟩
  · intro x hx
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
    by_cases hpd : p = d
    · subst p
      have hdheads : d ∈ left ∧ d ∈ right := by
        simpa [merge, hd] using hp
      have hxl : d.2.2 ∈ elements (left.erase d) := by
        rw [hl]; exact Finset.mem_image.mpr ⟨d, hdheads.1, rfl⟩
      have hxr : d.2.2 ∈ elements (right.erase d) := by
        rw [hr]; exact Finset.mem_image.mpr ⟨d, hdheads.2, rfl⟩
      obtain ⟨pl, hpl, hple⟩ := Finset.mem_image.mp hxl
      obtain ⟨pr, hpr, hpre⟩ := Finset.mem_image.mp hxr
      obtain ⟨hpld, hpll⟩ := Finset.mem_erase.mp hpl
      obtain ⟨hprd, hprr⟩ := Finset.mem_erase.mp hpr
      by_cases hplbase : pl ∈ l
      · by_cases hprbase : pr ∈ l
        · have hpla : pl = a := (base pl hplbase hple).resolve_right hpld
          have hpra : pr = a := (base pr hprbase hpre).resolve_right hprd
          have hm : pl ∈ merge l left right := by
            simp only [merge, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
            exact Or.inl (Or.inl ⟨⟨hplbase, hpll⟩, hpla ▸ hpra ▸ hprr⟩)
          exact Finset.mem_image.mpr ⟨pl, Finset.mem_erase.mpr ⟨hpld, hm⟩, hple.trans hpx⟩
        · have hm : pr ∈ merge l left right := by
            simp only [merge, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
            exact Or.inr ⟨hprr, hprbase⟩
          exact Finset.mem_image.mpr ⟨pr, Finset.mem_erase.mpr ⟨hprd, hm⟩, hpre.trans hpx⟩
      · have hm : pl ∈ merge l left right := by
          simp only [merge, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
          exact Or.inl (Or.inr ⟨hpll, hplbase⟩)
        exact Finset.mem_image.mpr ⟨pl, Finset.mem_erase.mpr ⟨hpld, hm⟩, hple.trans hpx⟩
    · exact Finset.mem_image.mpr ⟨p, Finset.mem_erase.mpr ⟨hpd, hp⟩, hpx⟩

def maybeErase (collect : Bool) (d : Record Nat) (s : State Nat) : State Nat :=
  if collect then s.erase d else s

/-- One fork/join, arbitrary-length fresh continuations, independently
collecting either or both initial heads. The historical base stays l.
The base may have arbitrary other elements, but exactly the candidate pair
are allowed for d's element. This is not yet a repeated-GC protocol. -/
theorem head_only_fork_correct (d a : Record Nat) (l : State Nat)
    (ha : a ∈ l) (hd : d ∈ l) (different : a ≠ d)
    (same : a.2.2 = d.2.2)
    (base : ∀ p ∈ l, p.2.2 = d.2.2 → p = a ∨ p = d)
    (left right : List (Op (SetOp Nat)))
    (fl : ∀ e ∈ left, e.1 ≠ d.2.1)
    (fr : ∀ e ∈ right, e.1 ≠ d.2.1)
    (collectLeft collectRight : Bool) :
    elements (merge l
      (left.foldl update (maybeErase collectLeft d l))
      (right.foldl update (maybeErase collectRight d l))) =
    elements (merge l (left.foldl update l) (right.foldl update l)) := by
  have hl := erase_fold_elements d a l ha different same left fl
  have hr := erase_fold_elements d a l ha different same right fr
  have hm := merge_keeps_witness d a l _ _ base hl hr hd
  cases collectLeft <;> cases collectRight <;> simp only [maybeErase, Bool.false_eq_true,
    ↓reduceIte]
  · rw [← erase_fold d l right fr, merge_erase_right d _ _ _ hd]
    exact hm
  · rw [← erase_fold d l left fl, merge_erase_left d _ _ _ hd]
    exact hm
  · rw [← erase_fold d l left fl, ← erase_fold d l right fr,
      merge_erase_left d _ _ _ hd, merge_erase_right d _ _ _ hd, Finset.erase_idem]
    exact hm

#print axioms head_only_fork_correct

/-- Minimum-timestamp specialization with the Lamport freshness obligation.
The merge base is explicitly the original two-record set in both runs. -/
theorem minimum_timestamp_fork_correct
    (r₁ r₂ t₁ t₂ x : Nat) (ordered : t₁ < t₂)
    (left right : List (Op (SetOp Nat)))
    (fl : ∀ e ∈ left, t₂ < e.1) (fr : ∀ e ∈ right, t₂ < e.1)
    (collectLeft collectRight : Bool) :
    let l : State Nat := {(r₁,t₁,x), (r₂,t₂,x)}
    elements (merge l
      (left.foldl update (maybeErase collectLeft (r₂,t₂,x) l))
      (right.foldl update (maybeErase collectRight (r₂,t₂,x) l))) =
    elements (merge l (left.foldl update l) (right.foldl update l)) := by
  dsimp only
  apply head_only_fork_correct (r₂,t₂,x) (r₁,t₁,x)
  · simp
  · simp
  · intro h
    have he := congrArg (fun p : Record Nat => p.2.1) h
    exact (Nat.ne_of_lt ordered) he
  · rfl
  · intro p hp _
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hp
  · intro e he
    exact Nat.ne_of_gt (fl e he)
  · intro e he
    exact Nat.ne_of_gt (fr e he)

#print axioms minimum_timestamp_fork_correct

end Sal.MRDTs.Instances.EfficientORSet.HeadGC
