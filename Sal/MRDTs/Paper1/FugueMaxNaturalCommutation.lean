import Sal.MRDTs.Paper1.FugueMaxNaturalControls

/-! Commutation in the guarded origin-list language. Deletion preserves
permanent anchors, so it commutes with insertion except at that insertion's
own fresh identity. These lemmas justify moving deletions past unrelated
births without dropping specification-conflict visibility. -/
namespace Sal.MRDTs.Paper1.FugueMaxNaturalCommutation
open FugueMaxNaturalSequence FugueMaxNaturalControls
open FugueMaxClientCandidate (deleteState)

theorem language_commutes_of_steps (a b : Action)
    (ab : ∀ s, legal (step s a) b ↔ legal s b)
    (ba : ∀ s, legal (step s b) a ↔ legal s a)
    (swap : ∀ s, step (step s a) b = step (step s b) a) :
    spec.Commutes a b := by
  apply HistoryMachine.commutes_of_diamond machine
  intro s t
  have forward : ∀ a b,
      (∀ s, legal (step s a) b ↔ legal s b) →
      (∀ s, legal (step s b) a ↔ legal s a) →
      (∀ s, step (step s a) b = step (step s b) a) →
      Runs machine.transition s [.update a,.update b] t →
      Runs machine.transition s [.update b,.update a] t := by
    intro a b ab ba swap run
    cases run with
    | cons first rest =>
      cases rest with
      | cons second tail =>
        cases tail
        change legal s a ∧ _ at first
        obtain ⟨ha,rfl⟩ := first
        change legal (step s a) b ∧ _ at second
        obtain ⟨hb,rfl⟩ := second
        exact .cons ⟨(ab s).mp hb,rfl⟩
          (.cons ⟨(ba s).mpr ha,swap s⟩ (.nil _))
  exact ⟨forward a b ab ba swap,forward b a ba ab (fun s => (swap s).symm)⟩

theorem insert_delete_commutes (id left target : Nat) (different : target ≠ id) :
    spec.Commutes (.insertAfter id left) (.deleteID target) := by
  apply language_commutes_of_steps
  · intro s
    simp [legal,step,mem_insertAfter,different]
  · intro s
    simp [legal,step,deleteState]
  · intro s
    cases s
    by_cases zero : target = 0 <;> simp [step,deleteState,zero]

theorem deletes_commute (a b : Nat) : spec.Commutes (.deleteID a) (.deleteID b) := by
  apply language_commutes_of_steps
  · intro s; simp [legal,step,deleteState]
  · intro s; simp [legal,step,deleteState]
  · intro s
    cases s
    by_cases az : a = 0 <;> by_cases bz : b = 0 <;>
      simp [step,deleteState,az,bz,Finset.insert_comm]

#print axioms insert_delete_commutes
#print axioms deletes_commute
end Sal.MRDTs.Paper1.FugueMaxNaturalCommutation
