import Sal.MRDTs.Paper1.DistinctOperationFullModel

namespace Sal.MRDTs.Paper1.DistinctOperationFullCounterexample
open Foundation ConcreteMRDT

/-- Independent minimum-timestamp register. Zero denotes an empty register;
updates at arbitrary timestamps are total, including timestamp zero. -/
def minimumSpec : DeterministicSpec (Op Unit) Unit Nat where
  State := Option Nat
  initial := none
  update := fun s e => some (match s with | none => e.time | some n => min n e.time)
  query := fun s _ => s.getD 0

theorem minimum_language_commutes (x y : Op Unit) :
    minimumSpec.toSpec.Commutes x y := by
  apply minimumSpec.language_commutes
  intro s
  cases s <;> simp [minimumSpec, Nat.min_assoc, Nat.min_left_comm, Nat.min_comm]

theorem paperOrder_empty {C : ReplayContext D.toUpdateSig} (good : Good C)
    (E : Set (Op Unit)) (x y : Op Unit) : ¬ paperOrder P C E x y := by
  simp [paperOrder, P, good.1 x y]

theorem specVisibility_empty {C : ReplayContext D.toUpdateSig} (good : Good C)
    (x y : Op Unit) : ¬ projectedSpecVisibility (D := D) id minimumSpec.toSpec C x y := by
  intro h
  exact good.1 x y h.1

/-- The independent history premise may select the reverse replay, even
though representation selects the forward replay for the two-event set. -/
theorem history_of_representation {C : ReplayContext D.toUpdateSig}
    {E : Set (Op Unit)} {s : Nat} (represented : R C E s) (q : Unit) :
    ∃ π : List (Op Unit), listPermOf π E ∧ respects π (paperOrder P C E) ∧
      respects π (projectedSpecVisibility (D := D) id minimumSpec.toSpec C) ∧
      minimumSpec.toSpec.admits (projectedLabels (D := D) id π ++
        [.query q (D.query (applySeq D.toUpdateSig D.init π) q)]) := by
  have order : ∀ π : List (Op Unit), respects π (paperOrder P C E) := by
    intro π
    exact List.pairwise_of_forall (fun x y => paperOrder_empty represented.1 E y x)
  have visibility : ∀ π : List (Op Unit),
      respects π (projectedSpecVisibility (D := D) id minimumSpec.toSpec C) := by
    intro π
    exact List.pairwise_of_forall (fun x y => specVisibility_empty represented.1 y x)
  rcases represented.2.2 with h | h | h | h
  · rcases h with ⟨rfl,rfl⟩
    refine ⟨[], ?_, order [], visibility [], ?_⟩
    · simp [listPermOf]
    · exact (minimumSpec.updates_query_iff [] q 0).mpr rfl
  · rcases h with ⟨rfl,rfl⟩
    refine ⟨[a], ?_, order [a], visibility [a], ?_⟩
    · simp [listPermOf]
    · exact (minimumSpec.updates_query_iff [a] q 1).mpr rfl
  · rcases h with ⟨rfl,rfl⟩
    refine ⟨[b], ?_, order [b], visibility [b], ?_⟩
    · simp [listPermOf]
    · exact (minimumSpec.updates_query_iff [b] q 2).mpr rfl
  · rcases h with ⟨rfl,rfl⟩
    refine ⟨[b,a], ?_, order [b,a], visibility [b,a], ?_⟩
    · simp [listPermOf, a, b, Set.pair_comm]
    · exact (minimumSpec.updates_query_iff [b,a] q 1).mpr rfl

theorem two_event_answer {π : List (Op Unit)} (perm : listPermOf π {a,b})
    {answer : Nat} (accepted : minimumSpec.toSpec.admits
      (projectedLabels (D := D) id π ++ [.query () answer])) : answer = 1 := by
  have pairPerm : listPermOf [a,b] ({a,b} : Set (Op Unit)) := by
    simp [listPermOf, a, b]
  have length := listPermOf_length_eq perm pairPerm
  cases π with
  | nil => simp at length
  | cons x xs =>
    cases xs with
    | nil => simp at length
    | cons y ys =>
      cases ys with
      | cons z zs => simp at length
      | nil =>
        have hx := (perm.2 x).mp (by simp)
        have hy := (perm.2 y).mp (by simp)
        have ne : x ≠ y := by simpa using perm.1
        have eq := (minimumSpec.updates_query_iff [x,y] () answer).mp accepted
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        all_goals simp [minimumSpec, a, b, Op.time] at eq ne ⊢
        all_goals assumption

theorem scoped_history_of_represented {I : Issuance D}
    (represented : ∀ C, CertifiedExecution D I C → ∀ v s E,
      C.ver v = some (s,E) → R C.replayContext E s) :
    ExecutionHistoryAdequacy P minimumSpec.toSpec I := by
  intro C execution v s E hv q
  exact history_of_representation (represented C execution v s E hv) q

theorem minimum_compatibility : CommutationCompatibility D id minimumSpec.toSpec :=
  fun x y _ => minimum_language_commutes x y

theorem total_fold_sound_fails : ¬ EventFoldHistorySound D minimumSpec.toSpec := by
  intro sound
  have accepted := sound [a,b] ()
  have perm : listPermOf [a,b] ({a,b} : Set (Op Unit)) := by simp [listPermOf, a, b]
  have wrong := two_event_answer perm accepted
  norm_num [D, applySeq, a, b, Op.time] at wrong

end Sal.MRDTs.Paper1.DistinctOperationFullCounterexample
