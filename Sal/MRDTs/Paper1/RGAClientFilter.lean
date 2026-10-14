import Sal.MRDTs.Paper1.RGAClientLocal

namespace Sal.MRDTs.Paper1.RGA.ClientFilter
open Foundation Instances.RGA

theorem insertAfter_filter (keep : Nat → Bool) (anchor value : Nat)
    (kept : keep value = true) (anchorKept : anchor = 0 ∨ keep anchor = true)
    (xs : List Nat) :
    (insertAfter anchor value xs).filter keep = insertAfter anchor value (xs.filter keep) := by
  by_cases root : anchor = 0
  · subst anchor
    cases xs <;> simp [insertAfter,kept]
  have hk := anchorKept.resolve_left root
  induction xs with
  | nil => simp [insertAfter,root]
  | cons head tail ih =>
    by_cases same : head = anchor
    · subst head
      simp [insertAfter,root,hk,kept]
    · cases headKept : keep head <;> simp [insertAfter,root,same,headKept,ih]

theorem mem_insertAfter {anchor value x : Nat} {xs : List Nat}
    (member : x ∈ insertAfter anchor value xs) : x = value ∨ x ∈ xs := by
  induction xs with
  | nil => by_cases root : anchor = 0 <;> simp_all [insertAfter]
  | cons head tail ih =>
    by_cases root : anchor = 0
    · simpa [insertAfter,root] using member
    by_cases same : head = anchor
    · simp only [insertAfter,if_neg root,if_pos same,List.mem_cons] at member
      rcases member with eq | eq | old
      · exact Or.inr (by simp [eq])
      · exact Or.inl eq
      · exact Or.inr (by simp [old])
    · simp only [insertAfter,if_neg root,if_neg same,List.mem_cons] at member
      rcases member with eq | rest
      · exact Or.inr (by simp [eq])
      · rcases ih rest with eq | old
        · exact Or.inl eq
        · exact Or.inr (by simp [old])

theorem insertAfter_nodup (anchor value : Nat) (xs : List Nat)
    (unique : xs.Nodup) (fresh : value ∉ xs) : (insertAfter anchor value xs).Nodup := by
  induction xs with
  | nil => by_cases root : anchor = 0 <;> simp [insertAfter,root]
  | cons head tail ih =>
    obtain ⟨headFresh,tailUnique⟩ := List.nodup_cons.mp unique
    have valueNe : value ≠ head := fun eq => fresh (by simp [eq])
    have valueFresh : value ∉ tail := fun h => fresh (by simp [h])
    by_cases root : anchor = 0
    · simpa [insertAfter,root] using List.nodup_cons.mpr ⟨fresh,unique⟩
    by_cases same : head = anchor
    · subst head
      simp [insertAfter,root,headFresh,valueFresh,Ne.symm valueNe,tailUnique]
    · simp only [insertAfter,if_neg root,if_neg same,List.nodup_cons]
      refine ⟨?_,ih tailUnique valueFresh⟩
      intro member
      rcases mem_insertAfter member with eq | old
      · exact valueNe eq.symm
      · exact headFresh old

theorem insertFold_nodup (entries : List (Nat × Nat))
    (entryUnique : (entries.map Prod.fst).Nodup) (xs : List Nat)
    (unique : xs.Nodup) (fresh : ∀ e ∈ entries, e.1 ∉ xs) :
    (entries.foldl (fun ys e => insertAfter e.2 e.1 ys) xs).Nodup := by
  induction entries generalizing xs with
  | nil => exact unique
  | cons head tail ih =>
    obtain ⟨headFresh,tailUnique⟩ := List.nodup_cons.mp entryUnique
    apply ih tailUnique _ (insertAfter_nodup _ _ _ unique (fresh head (by simp)))
    intro e he member
    rcases mem_insertAfter member with same | old
    · exact headFresh (List.mem_map.mpr ⟨e,he,same⟩)
    · exact fresh e (by simp [he]) old

theorem prepared_listStep {view : List Nat} (unique : view.Nodup)
    (noRoot : 0 ∉ view) {stamp replica : Nat} {request : Client.Request}
    {event : Op RGAOp} (prepared : Client.prepare view stamp replica request = some event) :
    listStep view event = Client.step view stamp request := by
  obtain ⟨allocated,transition⟩ := Client.prepared_refines_identified unique noRoot
    (allocated := ∅) (by simp) prepared
  rcases event with ⟨t,r,op⟩
  cases op with
  | addAfter anchor =>
    rw [EventSpec.insertion_uses_timestamp] at transition
    exact (congrArg Prod.fst transition.2.2).symm
  | remove target =>
    rw [EventSpec.deletion_uses_target] at transition
    exact (congrArg Prod.fst transition).symm

#print axioms insertAfter_filter
#print axioms insertAfter_nodup
#print axioms prepared_listStep
end Sal.MRDTs.Paper1.RGA.ClientFilter
