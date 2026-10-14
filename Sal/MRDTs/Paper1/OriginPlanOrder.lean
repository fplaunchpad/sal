import Sal.MRDTs.Paper1.FugueMaxOriginTreeWitness

/-! Ordering properties of the constructive origin-forest replay. -/
namespace Sal.MRDTs.Paper1.OriginPlanOrder
open FugueMaxOriginTreeWitness

theorem id_mem {parent : Nat} {ids : List Nat} {pairs : List (Nat × Nat)}
    (plan : OriginPlan parent ids pairs) {pair : Nat × Nat} (member : pair ∈ pairs) :
    pair.1 ∈ ids :=
  (ids_perm plan).mem_iff.mp (List.mem_map.mpr ⟨pair,member,rfl⟩)

theorem parent_mem {parent : Nat} {ids : List Nat} {pairs : List (Nat × Nat)}
    (plan : OriginPlan parent ids pairs) {pair : Nat × Nat} (member : pair ∈ pairs) :
    pair.2 = parent ∨ pair.2 ∈ ids := by
  induction plan with
  | nil => simp at member
  | @cons parent child children siblings childPairs siblingPairs desc rem ihc ihs =>
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with (old | rfl) | old
    · rcases ihs old with root | inner
      · exact Or.inl root
      · exact Or.inr (by simp [inner])
    · exact Or.inl rfl
    · rcases ihc old with root | inner
      · exact Or.inr (by simp [root])
      · exact Or.inr (by simp [inner])

theorem replay_order {parent : Nat} {ids : List Nat} {pairs : List (Nat × Nat)}
    (plan : OriginPlan parent ids pairs) (unique : (parent :: ids).Nodup)
    (before : Nat → Nat → Prop) (sorted : ids.Pairwise before) :
    pairs.Pairwise (fun a b => a.2 ≠ b.1 ∧ (a.2 = b.2 → before b.1 a.1)) := by
  induction plan with
  | nil => exact .nil
  | @cons parent child children siblings childPairs siblingPairs desc rem ihc ihs =>
    have pAbsent : parent ∉ child :: children ++ siblings := (List.nodup_cons.mp unique).1
    have cUnique : (child :: (children ++ siblings)).Nodup := (List.nodup_cons.mp unique).2
    have cAbsent : child ∉ children ++ siblings := (List.nodup_cons.mp cUnique).1
    have apart := (List.nodup_append.mp (List.nodup_cons.mp cUnique).2).2.2
    have separated : ∀ x ∈ parent :: siblings, ∀ y ∈ child :: children, x ≠ y := by
      intro x hx y hy eq
      subst y
      simp only [List.mem_cons] at hx hy
      rcases hx with rfl | hs
      · rcases hy with root | member
        · exact pAbsent (by simp [root])
        · exact pAbsent (by simp [member])
      · rcases hy with rfl | hc
        · exact cAbsent (by simp [hs])
        · exact apart x hc x hs rfl
    have cu : (child :: children).Nodup :=
      List.Nodup.sublist ((List.sublist_append_left children siblings).cons₂ child) cUnique
    have su : (parent :: siblings).Nodup := List.Nodup.sublist
      (((List.sublist_append_right children siblings).trans
        (List.sublist_cons_self child (children ++ siblings))).cons₂ parent) unique
    have sortedTail := (List.pairwise_cons.mp sorted).2
    have cr := ihc cu (sortedTail.sublist (List.sublist_append_left ..))
    have sr := ihs su (sortedTail.sublist (List.sublist_append_right ..))
    have childRun : ([(child,parent)] ++ childPairs).Pairwise
        (fun a b => a.2 ≠ b.1 ∧ (a.2 = b.2 → before b.1 a.1)) := by
      apply List.pairwise_append.mpr
      refine ⟨by simp,cr,?_⟩
      intro a ha b hb
      have ae : a = (child,parent) := List.mem_singleton.mp ha
      subst a
      have bId := id_mem desc hb
      have bParent := parent_mem desc hb
      constructor
      · exact separated parent (by simp) b.1 (by simp [bId])
      · intro eq
        exact False.elim (separated parent (by simp) b.2 (by simpa using bParent) eq)
    rw [List.append_assoc]
    apply List.pairwise_append.mpr
    refine ⟨sr,childRun,?_⟩
    intro a ha b hb
    have aId := id_mem rem ha
    have aParent : a.2 ∈ parent :: siblings := by simpa using parent_mem rem ha
    rcases List.mem_append.mp hb with singleton | descendant
    · have be : b = (child,parent) := List.mem_singleton.mp singleton
      subst b
      exact ⟨separated _ aParent child (by simp),fun _ =>
        (List.pairwise_cons.mp sorted).1 a.1 (by simp [aId])⟩
    · have bId := id_mem desc descendant
      have bParent : b.2 ∈ child :: children := by simpa using parent_mem desc descendant
      exact ⟨separated _ aParent b.1 (by simp [bId]),fun eq =>
        False.elim (separated _ aParent _ bParent eq)⟩

#print axioms replay_order
end Sal.MRDTs.Paper1.OriginPlanOrder
