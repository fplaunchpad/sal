import Sal.MRDTs.Paper1.FugueMaxOriginTreeWitness

/-! Appending original deletion events to a constructed origin-list witness.
Every target must have a birth (or be the root); repeated removals retain their
events and are idempotent. -/
namespace Sal.MRDTs.Paper1.FugueMaxNaturalReplay
open FugueMaxNaturalSequence FugueMaxOriginTreeWitness
open FugueMaxClientCandidate (deleteState visible visiblePart)

def deleteLabels (targets : List Nat) : List (SeqLabel Action Unit (List Nat)) :=
  targets.map (fun id => .update (.deleteID id))

theorem delete_run (s : Buffer) (targets : List Nat)
    (born : ∀ id ∈ targets, id ∈ s.order) :
    Runs machine.transition s (deleteLabels targets)
      ⟨s.order,s.deleted ∪ targets.toFinset.erase 0⟩ := by
  induction targets generalizing s with
  | nil => simpa [deleteLabels] using (Runs.nil (step := machine.transition) s)
  | cons target rest ih =>
    have tail := ih (deleteState s target) (fun id member => born id (by simp [member]))
    have one : machine.transition s (.update (.deleteID target)) (deleteState s target) :=
      ⟨born target (by simp),rfl⟩
    have run := Runs.cons one tail
    have finalEq : (⟨(deleteState s target).order,
        (deleteState s target).deleted ∪ rest.toFinset.erase 0⟩ : Buffer) =
        ⟨s.order,s.deleted ∪ (target :: rest).toFinset.erase 0⟩ := by
      by_cases zero : target = 0
      · simp [deleteState,zero]
      · simp only [deleteState,if_neg zero,List.toFinset_cons]
        congr 1
        ext id
        simp only [Finset.mem_erase,Finset.mem_union,Finset.mem_insert,List.mem_toFinset]
        grind
    rw [finalEq] at run
    exact run

/-- The forest insertion witness followed by all named removals has exactly
the expected visible list. Its order/permutation obligations are separate. -/
theorem plan_admits {ids : List Nat} {pairs : List (Nat × Nat)}
    (plan : OriginPlan 0 ids pairs) (unique : (0 :: ids).Nodup)
    (targets : List Nat) (born : ∀ id ∈ targets, id ∈ 0 :: ids) :
    spec.admits (labels pairs ++ deleteLabels targets ++
      [.query () (ids.filter (fun id => decide (id ∉ targets)))]) := by
  have insertions := legal_run plan [] [] ∅
    (by simpa using unique)
    (fun id member eq => (List.nodup_cons.mp unique).1 (eq ▸ member))
  have deletions := delete_run (⟨0 :: ids,∅⟩ : Buffer) targets born
  simp only [List.nil_append,List.append_nil] at insertions
  have combined := insertions.append deletions
  refine ⟨⟨0 :: ids,∅ ∪ targets.toFinset.erase 0⟩,combined.append ?_⟩
  apply Runs.cons ?_ (.nil _)
  constructor
  · rfl
  · change ids.filter _ = visible ⟨0 :: ids,∅ ∪ targets.toFinset.erase 0⟩
    simp only [visible,visiblePart,List.filter_cons,ne_eq,not_true_eq_false,
      false_and,decide_false,Bool.false_eq_true,if_false,Finset.empty_union]
    apply List.filter_congr
    intro id member
    have nonzero : id ≠ 0 := fun eq => (List.nodup_cons.mp unique).1 (eq ▸ member)
    simp [nonzero]

#print axioms delete_run
#print axioms plan_admits
end Sal.MRDTs.Paper1.FugueMaxNaturalReplay
