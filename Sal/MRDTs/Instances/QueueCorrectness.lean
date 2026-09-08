import Sal.MRDTs.Instances.QueueLegalization

/-! Queue correctness, including the concrete timestamp order of survivors. -/
namespace Sal.MRDTs.Instances.Queue

open Sal.MRDTs.Foundation
open Classical

private def VersionsSorted (C : Configuration Q) : Prop :=
  ∀ v s E, C.ver v = some (s, E) → s.Pairwise qEntryLE

private theorem sorted_step {C C' : Configuration Q} {l : Label Q}
    (step : Step Q C l C') (h : VersionsSorted C)
    (hsupport : ∀ (v : Version) (s : QState) (E : Set (Op QOp)), C.ver v = some (s, E) →
      ∀ p ∈ s, ∃ e ∈ E, e.1 = p.1) : VersionsSorted C' := by
  cases step with
  | @fork dst src v vnew s ev fresh hh hv hnew hr C' hvis hver hhead hparents =>
    intro w sw Ew hw
    rw [hver] at hw
    dsimp only at hw
    split at hw
    · cases hw
      exact h v s ev hv
    · exact h w sw Ew hw
  | @apply t r op v s ev vnew hh hv hf ht hn hr C' hvis hver hhead hparents =>
    intro w sw Ew hw
    rw [hver] at hw
    dsimp only at hw
    split at hw
    · cases hw
      have hs := h v s ev hv
      cases op with
      | enq value =>
        change (qUpdate s (t, r, .enq value)).Pairwise qEntryLE
        simp only [qUpdate]
        split
        · exact hs
        · apply List.pairwise_append.mpr
          refine ⟨hs, by simp, ?_⟩
          intro p hp q hq
          have hq' : q = (t, value) := List.mem_singleton.mp hq
          subst q
          obtain ⟨e, he, het⟩ := hsupport v s ev hv p hp
          have hvise : C'.vis e (t, r, .enq value) := by
            rw [hvis]
            exact Or.inr ⟨he, rfl⟩
          exact Or.inl (by simpa only [het] using C'.causal_mono hvise)
      | deq target =>
        change (s.filter (fun x => decide (x.1 ≠ target))).Pairwise qEntryLE
        exact hs.sublist (List.filter_sublist (p := fun x : ℕ × ℕ => decide (x.1 ≠ target)))
    · exact h w sw Ew hw
  | merge hh₁ hh₂ hv₁ hv₂ hgca hvT hnew hr₁ hr₂ C' hvis hver hhead hparents =>
    intro w sw Ew hw
    rw [hver] at hw
    dsimp only at hw
    split at hw
    · cases hw
      exact qEntry_mergeSort_sorted _
    · exact h w sw Ew hw
  | query hs hv => exact h

/-- Every stored version is in timestamp order, including after ordinary
updates and virtual-base merges. This is stronger than `loOn` respect alone. -/
theorem queue_versions_sorted {C : Configuration Q}
    (exec : CertifiedExecution Q generation C) :
    ∀ v s E, C.ver v = some (s, E) → s.Pairwise qEntryLE := by
  have reach : MintCertifiedReachV Q (canonicalVirtualMergeBase Q) generation C := by
    cases exec with
    | ordinary h => exact h.toV
    | virtual h => exact h
  clear exec
  induction reach with
  | init =>
    intro v s E hv
    change (if v = 0 then some (Q.init, ∅) else none) = some (s, E) at hv
    split at hv
    · cases hv
      exact List.Pairwise.nil
    · contradiction
  | @step C C' l reach before one after ih =>
    have hsupp : ∀ (v : Version) (s : QState) (E : Set (Op QOp)), C.ver v = some (s, E) →
        ∀ p ∈ s, ∃ e ∈ E, e.1 = p.1 := by
      intro v s E hv p hp
      have ht : p.1 ∈ qTags s := List.mem_map.mpr ⟨p, hp, rfl⟩
      obtain ⟨⟨e, he, _, het⟩, _⟩ :=
        (queue_version_contents (.virtual reach) hv p.1).mp ht
      exact ⟨e, he, het⟩
    cases one.toRaw with
    | base raw => exact sorted_step raw ih hsupp
    | mergeVirtual hh₁ hh₂ hv₁ hv₂ hnew hr₁ hr₂ C' hvis hver hhead hparents =>
      intro w sw Ew hw
      rw [hver] at hw
      dsimp only at hw
      split at hw
      · cases hw
        exact qEntry_mergeSort_sorted _
      · exact ih w sw Ew hw

/-- The public Queue contract combines the legal FIFO witness, exact
surviving identities and timestamp order, and the concurrency restriction
on repeated dequeue targets. All parts concern the same certified execution. -/
theorem queue_correct {C : Configuration Q}
    (exec : CertifiedExecution Q generation C) :
    IsSpecLinearizable Q rc clientSpec Eq C ∧
    (∀ v s E, C.ver v = some (s, E) → s.Pairwise qEntryLE ∧
      ∀ target, target ∈ qTags s ↔ qEnqIn E target ∧ ¬ qDeqIn E target) ∧
    (∀ a ∈ C.events, ∀ b ∈ C.events, ∀ target,
      a.2.2 = .deq target → b.2.2 = .deq target → ¬ C.vis a b ∧ ¬ C.vis b a) := by
  refine ⟨?_, ?_, ?_⟩
  · cases exec with
    | ordinary h => exact verified.correct h
    | virtual h => exact verified.correctV h
  · intro v s E hv
    exact ⟨queue_versions_sorted exec v s E hv, queue_version_contents exec hv⟩
  · intro a ha b hb target hoa hob
    exact duplicate_dequeues_concurrent exec ha hb hoa hob

#print axioms queue_versions_sorted
#print axioms queue_correct

end Sal.MRDTs.Instances.Queue
