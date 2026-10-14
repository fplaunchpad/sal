import Sal.MRDTs.Paper1.FugueMaxOriginTreeWitness

/-! Finite preorder decomposition independent of implementation coordinates.
An ancestor's descendants occupy an initial segment after it; parents precede
their children. These properties construct an ordered forest replay plan. -/
namespace Sal.MRDTs.Paper1.OriginForestDecomposition
open FugueMaxOriginTreeWitness

def NoGaps (desc : Nat → Nat → Prop) : List Nat → Prop
  | [] => True
  | a :: rest => rest.Pairwise (fun b c => desc c a → desc b a) ∧ NoGaps desc rest

theorem NoGaps.sublist {desc : Nat → Nat → Prop} {xs ys : List Nat}
    (sub : xs.Sublist ys) (good : NoGaps desc ys) : NoGaps desc xs := by
  induction sub with
  | slnil => trivial
  | cons a sub ih => exact ih good.2
  | cons₂ a sub ih => exact ⟨good.1.sublist sub,ih good.2⟩

theorem prefix_partition (P : Nat → Prop) (xs : List Nat)
    (ordered : xs.Pairwise (fun a b => P b → P a)) :
    ∃ pre post, xs = pre ++ post ∧ (∀ x ∈ pre, P x) ∧ (∀ x ∈ post, ¬ P x) := by
  classical
  induction xs with
  | nil => exact ⟨[],[],rfl,by simp,by simp⟩
  | cons a xs ih =>
    by_cases yes : P a
    · obtain ⟨pre,post,eq,all,none⟩ := ih (List.pairwise_cons.mp ordered).2
      exact ⟨a :: pre,post,by simp [eq],by simpa using And.intro yes all,none⟩
    · refine ⟨[],a :: xs,rfl,by simp,?_⟩
      intro x member px
      rcases List.mem_cons.mp member with rfl | member
      · exact yes px
      · exact yes ((List.pairwise_cons.mp ordered).1 x member px)

theorem forest_exists (parentOf : Nat → Nat) (desc : Nat → Nat → Prop)
    (trans : Transitive desc) (antisymm : ∀ {x y}, desc x y → desc y x → x = y)
    (parentEdge : ∀ x, desc x (parentOf x))
    (peel : ∀ x y, desc x y → x ≠ y → desc (parentOf x) y)
    (parent : Nat) (ids : List Nat)
    (unique : (parent :: ids).Nodup)
    (outside : ∀ x ∈ ids, ¬ desc parent x)
    (noSelf : ∀ x ∈ ids, parentOf x ≠ x)
    (closed : ∀ x ∈ ids, parentOf x = parent ∨ parentOf x ∈ ids)
    (ordered : ids.Pairwise (fun a b => parentOf a ≠ b))
    (gaps : NoGaps desc ids) :
    ∃ pairs, OriginPlan parent ids pairs ∧ ∀ pair ∈ pairs, pair.2 = parentOf pair.1 := by
  classical
  induction ids using (measure List.length).wf.induction generalizing parent with
  | h ids ih =>
    cases ids with
    | nil => exact ⟨[],.nil parent,by simp⟩
    | cons child rest =>
      have childParent : parentOf child = parent := by
        rcases closed child (by simp) with yes | member
        · exact yes
        · rcases List.mem_cons.mp member with self | later
          · exact False.elim (noSelf child (by simp) self)
          · exact False.elim ((List.pairwise_cons.mp ordered).1 _ later rfl)
      obtain ⟨children,siblings,split,descendants,separate⟩ :=
        prefix_partition (fun x => desc x child) rest gaps.1
      have childNot : child ∉ children ++ siblings := by
        simpa [split] using (List.nodup_cons.mp (List.nodup_cons.mp unique).2).1
      have childrenSub : children.Sublist rest := by rw [split]; exact List.sublist_append_left ..
      have siblingsSub : siblings.Sublist rest := by rw [split]; exact List.sublist_append_right ..
      have childFresh (x : Nat) (member : x ∈ children) : x ≠ child := by
        intro eq; subst x; exact childNot (by simp [member])
      have childrenClosed : ∀ x ∈ children, parentOf x = child ∨ parentOf x ∈ children := by
        intro x member
        have ancestor := peel x child (descendants x member) (childFresh x member)
        rcases closed x (by simp [split,member]) with root | member'
        · rw [root] at ancestor
          exact False.elim (outside child (by simp) ancestor)
        · rcases List.mem_cons.mp member' with root | member'
          · exact Or.inl root
          · rw [split,List.mem_append] at member'
            rcases member' with yes | no
            · exact Or.inr yes
            · exact False.elim (separate _ no ancestor)
      have siblingsClosed : ∀ x ∈ siblings, parentOf x = parent ∨ parentOf x ∈ siblings := by
        intro x member
        rcases closed x (by simp [split,member]) with root | member'
        · exact Or.inl root
        · rcases List.mem_cons.mp member' with childEq | member'
          · exact False.elim (separate x member (childEq ▸ parentEdge x))
          · rw [split,List.mem_append] at member'
            rcases member' with childMember | siblingMember
            · exact False.elim (separate x member (trans (parentEdge x) (descendants _ childMember)))
            · exact Or.inr siblingMember
      have childrenUnique : (child :: children).Nodup := by
        exact List.Nodup.sublist (childrenSub.cons₂ child) (List.nodup_cons.mp unique).2
      have siblingsUnique : (parent :: siblings).Nodup := by
        exact List.Nodup.sublist
          ((siblingsSub.trans (List.sublist_cons_self _ _)).cons₂ parent) unique
      obtain ⟨childPairs,childPlan,childShape⟩ := ih children
        (by change children.length < (child :: rest).length
            simp only [List.length_cons,split,List.length_append]; omega) child childrenUnique
        (fun x member both => childFresh x member (antisymm (descendants x member) both))
        (fun x member => noSelf x (by simp [split,member])) childrenClosed
        ((List.pairwise_cons.mp ordered).2.sublist childrenSub) (NoGaps.sublist childrenSub gaps.2)
      obtain ⟨siblingPairs,siblingPlan,siblingShape⟩ := ih siblings
        (by change siblings.length < (child :: rest).length
            simp only [List.length_cons,split,List.length_append]; omega) parent siblingsUnique
        (fun x member => outside x (by simp [split,member]))
        (fun x member => noSelf x (by simp [split,member])) siblingsClosed
        ((List.pairwise_cons.mp ordered).2.sublist siblingsSub) (NoGaps.sublist siblingsSub gaps.2)
      refine ⟨siblingPairs ++ [(child,parent)] ++ childPairs,?_,?_⟩
      · simpa [split,List.append_assoc] using OriginPlan.cons childPlan siblingPlan
      · intro pair member
        simp only [List.mem_append,List.mem_singleton] at member
        rcases member with (old | rfl) | old
        · exact siblingShape pair old
        · exact childParent.symm
        · exact childShape pair old

#print axioms forest_exists
end Sal.MRDTs.Paper1.OriginForestDecomposition
