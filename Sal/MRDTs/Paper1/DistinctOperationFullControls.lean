import Sal.MRDTs.Paper1.DistinctOperationFullCounterexample
import Sal.MRDTs.Paper1.DistinctOperationFullHistory

namespace Sal.MRDTs.Paper1.DistinctOperationFullCounterexample
open Foundation ConcreteMRDT

def controlContext : ReplayContext D.toUpdateSig where
  L := fun _ => some {a,b}
  vis := fun _ _ => False
  timestamps_distinct := by
    intro x y r E r' F h hx k hy ne
    obtain rfl := Option.some.inj h
    obtain rfl := Option.some.inj k
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all [a,b]
  vis_total_same_replica := by
    intro x y r E r' F h hx k hy ne same
    obtain rfl := Option.some.inj h
    obtain rfl := Option.some.inj k
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all [a,b]

private theorem good_control : Good controlContext := by
  constructor
  · simp [controlContext]
  · intro e he
    obtain ⟨r,E,h,he⟩ := he
    obtain rfl := Option.some.inj h
    exact he

private theorem support_control {E : Set (Op Unit)} (sub : E ⊆ {a,b}) :
    Supported controlContext E := fun e he => ⟨0,{a,b},rfl,sub he⟩

private theorem represented_control :
    R controlContext ∅ 0 ∧ R controlContext {a} 1 ∧
    R controlContext {b} 2 ∧ R controlContext {a,b} 2 := by
  refine ⟨⟨good_control,support_control (by simp),Or.inl ⟨rfl,rfl⟩⟩,
    ⟨good_control,support_control (by simp),Or.inr (Or.inl ⟨rfl,rfl⟩)⟩,
    ⟨good_control,support_control (by simp),Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))⟩,
    ⟨good_control,support_control (by simp),Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))⟩⟩

private theorem closed_control (E : Set (Op Unit)) : (scheme controlContext).Closed E := by
  intro x y edge _
  exact False.elim edge.1

private theorem context_control (E F : Set (Op Unit))
    (supE : Supported controlContext E) (supF : Supported controlContext F) :
    Raw.Context P scheme controlContext E F b := by
  refine ⟨?_,?_,supE,supF,closed_control E,closed_control F,?_,?_⟩
  · simp [controlContext,Transitive]
  · simp [controlContext]
  · exact fun x _ _ => empty_order good_control _ b x
  · exact fun x _ _ edge => good_control.1 b x edge.1

/-- All indexed antecedents of the causal VC are populated. -/
theorem causal_vc_control :
    D.merge 0 1 (D.update 0 b) = 2 ∧ D.merge 0 1 (D.update 0 b) ≠ 1 := by
  have reps := represented_control
  have equation := vcs.causal_delta controlContext {a,b} 1 0 b
    (by simp [controlContext,Transitive]) (by simp [controlContext]) reps.2.2.2.2.1
    (closed_control _) (by simp)
    (fun x _ _ => empty_order good_control _ b x)
    (fun x _ _ edge => good_control.1 b x edge.1)
    (by simpa [Set.ext_iff,a,b] using reps.2.1)
    (by simpa [past good_control,Set.diff_self] using reps.1)
    (by simpa [past good_control,D,b,Op.time] using reps.2.2.1)
    (by simpa [D,b,Op.time] using reps.2.2.2)
  exact ⟨by simpa [D,b,Op.time] using equation,by decide⟩

/-- Disjoint singleton branches exercise local redistribution. -/
theorem local_vc_control :
    D.merge 0 (D.merge 0 0 (D.update 0 b)) 1 = 2 ∧
    D.merge 0 (D.merge 0 0 (D.update 0 b)) 1 ≠ 1 := by
  have reps := represented_control
  have equation := vcs.local_redistribute controlContext {b} {a} 0 0 0 1 b
    (context_control _ _ reps.2.2.1.2.1 reps.2.1.2.1) (by simp) (by simp [a,b])
    (by simpa [Set.ext_iff,a,b] using reps.1)
    (by simpa [past good_control,Set.diff_self] using reps.1)
    (by simpa using reps.1) reps.2.1
    (by simpa [past good_control,D,b,Op.time] using reps.2.2.1)
    (by simpa [D,b,Op.time] using reps.2.2.1)
    (by simpa [D,Set.ext_iff,a,b] using reps.2.1)
  constructor
  · rw [equation]; decide
  · decide

/-- Overlapping unequal branches exercise the shared-event equation. -/
theorem shared_vc_control :
    D.merge (D.merge 0 0 (D.update 0 b)) (D.merge 0 1 (D.update 0 b))
      (D.merge 0 0 (D.update 0 b)) = 2 ∧
    D.merge (D.merge 0 0 (D.update 0 b)) (D.merge 0 1 (D.update 0 b))
      (D.merge 0 0 (D.update 0 b)) ≠ 1 := by
  have reps := represented_control
  have equation := vcs.shared controlContext {a,b} {b} 0 1 0 0 b
    (context_control _ _ reps.2.2.2.2.1 reps.2.2.1.2.1) (by simp) (by simp)
    (by simpa [Set.ext_iff,a,b] using reps.1)
    (by simpa [past good_control,Set.diff_self] using reps.1)
    (by simpa [Set.ext_iff,a,b] using reps.2.1)
    (by simpa using reps.1)
    (by simpa [past good_control,D,b,Op.time] using reps.2.2.1)
    (by simpa [D,Set.ext_iff,a,b] using reps.2.2.1)
    (by simpa [D,b,Op.time] using reps.2.2.2)
    (by simpa [D,b,Op.time] using reps.2.2.1)
    (by simpa [D,Set.ext_iff,a,b] using reps.2.1)
  constructor
  · rw [equation]; decide
  · decide

theorem singleton_spec_control :
    minimumSpec.toSpec.admits (projectedLabels (D := D) id [a] ++ [.query () 1]) ∧
    ¬ minimumSpec.toSpec.admits (projectedLabels (D := D) id [a] ++ [.query () 0]) := by
  constructor
  · exact (minimumSpec.updates_query_iff [a] () 1).mpr rfl
  · intro h
    have bad := (minimumSpec.updates_query_iff [a] () 0).mp h
    change (0 : Nat) = 1 at bad
    omega

end Sal.MRDTs.Paper1.DistinctOperationFullCounterexample
