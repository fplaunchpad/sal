import Sal.MRDTs.Paper1.RGA
import Sal.MRDTs.Paper1.SpecificationVisibility

/-!
# Allocating RGA labels expose independent specification conflicts

The application insertion label has no inserted identifier. An independent
allocator can therefore choose an identifier named by a deletion. This makes
the two labels fail global contextual commutation, even when the particular
implementation insertion chooses an unrelated identifier. The checked contexts
below contain query labels which pin allocation choices independently.

Concrete grow-only RGA updates all commute. Consequently the specification-visible criterion's
`SpecificationConflictsCovered` premise fails for this allocating language.
This does not by itself refute its stronger configuration criterion.
-/
namespace Sal.MRDTs.Paper1.RGA
open Sal.MRDTs.Foundation
open Sal.MRDTs.Instances.RGA

/-- A query immediately after deletion cannot contain the deleted identifier,
regardless of the prefix or its nondeterministic allocation choices. -/
theorem after_delete_not_mem (pre : List (SeqLabel RGAOp Unit (List ℕ)))
    (id : ℕ) (answer : List ℕ)
    (accepted : listHistorySpec.admits (pre ++ [.update (.remove id), .query () answer])) :
    id ∉ answer := by
  obtain ⟨final, run⟩ := accepted
  obtain ⟨mid, _, rest⟩ := run.split pre [.update (.remove id), .query () answer]
  cases rest with
  | cons hu rest =>
      cases rest with
      | cons hq _ =>
          change _ = (mid.1.filter (· ≠ id), mid.2) at hu
          subst hu
          have hanswer : answer = mid.1.filter (· ≠ id) := hq.2
          rw [hanswer]
          simp

/-- PASS: an absent deletion followed by allocation of that identifier displays
it. The insertion operation itself carries no identifier. -/
theorem delete_then_allocate_admitted :
    listHistorySpec.admits
      [.update (.remove 1), .update (.addAfter 0), .query () [1]] := by
  refine ⟨([1], [1]), .cons (m := ([], [])) rfl
    (.cons (m := ([1], [1])) ?_ (.cons ⟨rfl, rfl⟩ (.nil _)))⟩
  exact ⟨1, by simp, rfl⟩

/-- FAIL: swapping the same labels deletes the displayed identifier. -/
theorem allocate_then_delete_rejected :
    ¬ listHistorySpec.admits
      [.update (.addAfter 0), .update (.remove 1), .query () [1]] := by
  intro accepted
  exact after_delete_not_mem [.update (.addAfter 0)] 1 [1] accepted (by decide)

theorem root_insert_remove_not_commute :
    ¬ listHistorySpec.Commutes (.addAfter 0) (.remove 1) := by
  intro commute
  have hs := commute [] [.query () [1]]
  exact allocate_then_delete_rejected (hs.mpr delete_then_allocate_admitted)

/-- A prefix query pins the existing anchor to 2. Deleting absent identifier 1
then allocating it after that anchor displays both identifiers. -/
theorem anchor_two_delete_then_allocate_admitted :
    listHistorySpec.admits
      [.update (.addAfter 0), .query () [2], .update (.remove 1),
       .update (.addAfter 2), .query () [2, 1]] := by
  refine ⟨([2, 1], [2, 1]), .cons (m := ([2], [2])) ?_
    (.cons (m := ([2], [2])) ⟨rfl, rfl⟩
      (.cons (m := ([2], [2])) rfl
        (.cons (m := ([2, 1], [2, 1])) ?_ (.cons ⟨rfl, rfl⟩ (.nil _)))))⟩
  · refine ⟨2, ?_⟩
    exact ⟨by simp [allocationMachine], rfl⟩
  · exact ⟨1, by decide, rfl⟩

/-- Even deletion of an identifier different from the anchor conflicts with
an insertion label: its allocator can choose that deleted identifier. -/
theorem anchor_two_insert_remove_one_not_commute :
    ¬ listHistorySpec.Commutes (.addAfter 2) (.remove 1) := by
  intro commute
  have hs := commute [.update (.addAfter 0), .query () [2]] [.query () [2, 1]]
  have accepted := hs.mpr anchor_two_delete_then_allocate_admitted
  exact after_delete_not_mem
    [.update (.addAfter 0), .query () [2], .update (.addAfter 2)]
    1 [2, 1] accepted (by decide)

/-- Symmetric checked context for the other crossed local operation pair. -/
theorem anchor_one_delete_then_allocate_admitted :
    listHistorySpec.admits
      [.update (.addAfter 0), .query () [1], .update (.remove 2),
       .update (.addAfter 1), .query () [1, 2]] := by
  refine ⟨([1, 2], [1, 2]), .cons (m := ([1], [1])) ?_
    (.cons (m := ([1], [1])) ⟨rfl, rfl⟩
      (.cons (m := ([1], [1])) rfl
        (.cons (m := ([1, 2], [1, 2])) ?_ (.cons ⟨rfl, rfl⟩ (.nil _)))))⟩
  · refine ⟨1, ?_⟩
    exact ⟨by simp [allocationMachine], rfl⟩
  · exact ⟨2, by decide, rfl⟩

theorem anchor_one_insert_remove_two_not_commute :
    ¬ listHistorySpec.Commutes (.addAfter 1) (.remove 2) := by
  intro commute
  have hs := commute [.update (.addAfter 0), .query () [1]] [.query () [1, 2]]
  have accepted := hs.mpr anchor_one_delete_then_allocate_admitted
  exact after_delete_not_mem
    [.update (.addAfter 0), .query () [1], .update (.addAfter 1)]
    2 [1, 2] accepted (by decide)

/-- The specification-visible criterion's conflict-coverage premise is incompatible with the current
commuting implementation and this independent allocating history language. -/
theorem specification_conflicts_not_covered :
    ¬ SpecificationConflictsCovered RGAM listHistorySpec := by
  intro covered
  exact covered (0, 0, .addAfter 0) (1, 0, .remove 1)
    root_insert_remove_not_commute (RGAM_all_comm _ _)

/-- PASS+FAIL control for the contextual conflict witness. -/
example : listHistorySpec.admits
      [.update (.remove 1), .update (.addAfter 0), .query () [1]] ∧
    ¬ listHistorySpec.admits
      [.update (.addAfter 0), .update (.remove 1), .query () [1]] :=
  ⟨delete_then_allocate_admitted, allocate_then_delete_rejected⟩

#print axioms root_insert_remove_not_commute
#print axioms anchor_two_insert_remove_one_not_commute
#print axioms specification_conflicts_not_covered
end Sal.MRDTs.Paper1.RGA
