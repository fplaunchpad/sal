import Sal.MRDTs.Paper1.ConcreteJoin

/-! Generic facts for filtered identifier lookup and candidate selection.
These use no ordering law or datatype invariant. -/
namespace Sal.MRDTs.Paper1.Automation.FiniteLookup

theorem marked_lookup {R : Type} (xs : List R) (marked : R → Bool) (id : R → Nat)
    (n : Nat) (mem : n∈(xs.filter marked).map id) :
    ∃g,(xs.filter marked).find? (fun g=>id g==n)=some g ∧ g∈xs ∧ marked g=true ∧ id g=n := by
  obtain ⟨g,hg,eq⟩ := List.mem_map.mp mem
  have some : ((xs.filter marked).find? (fun g=>id g==n)).isSome := by
    rw [List.find?_isSome]; exact ⟨g,hg,by simp [eq]⟩
  obtain ⟨g,found⟩ := Option.isSome_iff_exists.mp some
  have hm := List.mem_of_find?_eq_some found
  exact ⟨g,found,List.mem_of_mem_filter hm,(List.mem_filter.mp hm).2,
    by simpa using List.find?_some found⟩

theorem zero_lookup {R C : Type} (xs : List R) (marked : R → Bool) (id : R → Nat)
    (chain : R → C) (empty : C) (positive : ∀ g ∈ xs, 0 < id g) :
    (((xs.filter marked).find? (fun g=>id g==0)).map chain).getD empty=empty := by
  rw [List.find?_eq_none.mpr]
  · rfl
  · intro g hg; simp only [beq_iff_eq]
    exact Nat.ne_of_gt (positive g (List.mem_of_mem_filter hg))

theorem fold_choice {R : Type} (step : Option R → R → Option R)
    (choice : ∀acc p,step acc p=acc ∨ step acc p=some p)
    (xs : List R) (acc : Option R) (p : R) (selected : xs.foldl step acc=some p) :
    acc=some p ∨ p∈xs := by
  induction xs generalizing acc with
  | nil => exact Or.inl selected
  | cons x xs ih =>
    rcases ih (step acc x) selected with prior | mem
    · rcases choice acc x with old | new
      · exact Or.inl (old.symm.trans prior)
      · exact Or.inr (List.mem_cons.mpr (Or.inl (Option.some.inj (new.symm.trans prior)).symm))
    · exact Or.inr (List.mem_cons_of_mem _ mem)

theorem selected_id {R : Type} (step : Option R → R → Option R)
    (choice : ∀acc p,step acc p=acc ∨ step acc p=some p)
    (xs : List R) (id : R → Nat) (n : Nat)
    (selected : (xs.foldl step none).map id=some n) : ∃p∈xs,id p=n := by
  cases h : xs.foldl step none with
  | none => simp [h] at selected
  | some p =>
    simp only [h,Option.map_some,Option.some.injEq] at selected
    exact ⟨p,(fold_choice step choice xs none p h).resolve_left (by simp),selected⟩
end Sal.MRDTs.Paper1.Automation.FiniteLookup
