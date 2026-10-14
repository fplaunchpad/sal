import Sal.MRDTs.Paper1.FugueMaxNaturalSequence

/-! Constructive insertion witnesses for ordered left-origin forests.
The forest is proof data, not a field of the natural list specification.
Siblings are replayed in reverse display order, each before its descendants. -/
namespace Sal.MRDTs.Paper1.FugueMaxOriginTreeWitness
open FugueMaxNaturalSequence

inductive OriginPlan : Nat → List Nat → List (Nat × Nat) → Prop where
  | nil (parent : Nat) : OriginPlan parent [] []
  | cons {parent child : Nat} {children siblings : List Nat}
      {childPairs siblingPairs : List (Nat × Nat)}
      (descendants : OriginPlan child children childPairs)
      (remaining : OriginPlan parent siblings siblingPairs) :
      OriginPlan parent (child :: children ++ siblings)
        (siblingPairs ++ [(child,parent)] ++ childPairs)

def labels (pairs : List (Nat × Nat)) : List (SeqLabel Action Unit (List Nat)) :=
  pairs.map (fun p => .update (.insertAfter p.1 p.2))

theorem ids_perm {parent : Nat} {ids : List Nat} {pairs : List (Nat × Nat)}
    (plan : OriginPlan parent ids pairs) : (pairs.map Prod.fst).Perm ids := by
  induction plan with
  | nil => exact .refl _
  | @cons parent child children siblings childPairs siblingPairs desc rem ihc ihs =>
    simp only [List.map_append,List.map_cons,List.map_nil]
    have h := ihs.append (List.Perm.cons child ihc)
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using
      h.trans List.perm_append_comm

/-- A genuine guarded replay exists for every finite ordered origin forest.
No assumption says that replay already equals the final list. -/
theorem legal_run {parent : Nat} {ids : List Nat} {pairs : List (Nat × Nat)}
    (plan : OriginPlan parent ids pairs) (pre suf : List Nat) (deleted : Finset Nat)
    (unique : (pre ++ parent :: (ids ++ suf)).Nodup)
    (nonzero : ∀ id ∈ ids, id ≠ 0) :
    Runs machine.transition ⟨pre ++ parent :: suf,deleted⟩ (labels pairs)
      ⟨pre ++ parent :: (ids ++ suf),deleted⟩ := by
  induction plan generalizing pre suf with
  | nil parent => simpa [labels] using (Runs.nil (step := machine.transition)
      (⟨pre ++ parent :: suf,deleted⟩ : Buffer))
  | @cons parent child children siblings childPairs siblingPairs desc rem ihc ihs =>
    have siblingUnique : (pre ++ parent :: (siblings ++ suf)).Nodup := by
      exact List.Nodup.sublist
        (((List.sublist_append_right (child :: children) (siblings ++ suf)).cons₂ parent).append_left pre)
        (by simpa [List.append_assoc] using unique)
    have siblingsRun := ihs pre suf siblingUnique
      (fun id member => nonzero id (by simp [member]))
    have pieces := List.nodup_append.mp unique
    have inner := List.nodup_cons.mp pieces.2.1
    have childInner := List.nodup_cons.mp inner.2
    have parentAbsent : parent ∉ pre := by
      intro member
      exact pieces.2.2 parent member parent (by simp) rfl
    have childAbsent : child ∉ pre ++ parent :: (siblings ++ suf) := by
      simp only [List.mem_append,List.mem_cons]
      rintro (member | same | member)
      · exact pieces.2.2 child member child (by simp) rfl
      · exact inner.1 (by simp [same])
      · exact childInner.1 (by simp [member])
    have insertRun : Runs machine.transition
        (⟨pre ++ parent :: (siblings ++ suf),deleted⟩ : Buffer)
        [.update (.insertAfter child parent)]
        ⟨pre ++ parent :: child :: (siblings ++ suf),deleted⟩ := by
      apply Runs.cons ?_ (.nil _)
      constructor
      · exact ⟨nonzero child (by simp),childAbsent,by simp⟩
      · simp [machine,step,insertAfter_split pre (siblings ++ suf) child parent parentAbsent]
    have childrenUnique : ((pre ++ [parent]) ++ child :: (children ++ (siblings ++ suf))).Nodup := by
      simpa [List.append_assoc] using unique
    have childrenRun := ihc (pre ++ [parent]) (siblings ++ suf) childrenUnique
      (fun id member => nonzero id (by simp [member]))
    simp only [List.append_assoc,List.cons_append,List.nil_append] at childrenRun
    have assembled := siblingsRun.append (insertRun.append childrenRun)
    simpa [labels,List.map_append,List.append_assoc] using assembled

#print axioms ids_perm
#print axioms legal_run
end Sal.MRDTs.Paper1.FugueMaxOriginTreeWitness
