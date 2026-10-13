import Sal.MRDTs.Paper1.DistinctOperationReplay
import Sal.MRDTs.Paper1.DistinctOperationPolicy
import Sal.MRDTs.Paper1.DistinctOperationCounterexample
import Sal.MRDTs.Paper1.EfficientORSetDistinctOperation

/-! The proposed complete replay-law bundle admits the checked countermodel;
the explicit repair rejects it and is satisfied by the unchanged efficient set. -/
namespace Sal.MRDTs.Paper1.DistinctOperationControls
open Foundation

namespace Counter
open DistinctOperationCounterexample

def proposed : DistinctOperationReplay.Laws D P where
  noncomm_exact := revised_exact
  no_chain x y z _ _ := revised_other_laws.1 x y z
  conditional_commutation s x y z between _ _ _ :=
    revised_other_laws.2 s x y z between

theorem missing_equal_operation_condition : ¬ DistinctOperationReplay.EqualOperationCommutes D := by
  intro equal
  have commutes := equal a b (by change (1 : Nat) ≠ 2; decide) (by decide) rfl
  exact noncommuting (fun s _ => commutes s)

def proposedScoped : DistinctOperationPolicy.Invariant.PolicyLaws scope Inv P where
  concurrent_exact x y _ _ ne _ _ := False.elim (ne (Subsingleton.elim _ _))
  no_chain _ _ _ _ _ _ _ _ := by simp [P]

theorem missing_scoped_diamond : ¬ DistinctOperationPolicy.Invariant.RestrictedLaws scope Inv P :=
  fun laws => no_replay_certificate laws.replay

end Counter

namespace Efficient
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

def proposed : DistinctOperationReplay.Laws (D α).toUpdateSig (EfficientORSet.EventSpec.conflict α) where
  noncomm_exact := EfficientORSet.DistinctOperation.noncomm_exact
  no_chain := EfficientORSet.Guarded.laws.no_chain
  conditional_commutation := EfficientORSet.Guarded.laws.conditional_commutation

theorem equal_operation_commutes : DistinctOperationReplay.EqualOperationCommutes (D α).toUpdateSig := by
  intro a b _ replicas same
  rcases a with ⟨ta,ra,ao⟩
  rcases b with ⟨tb,rb,bo⟩
  change ao = bo at same
  subst bo
  cases ao with
  | add x => exact EfficientORSet.NeemScope.adds_commute_of_replica_ne ta ra tb rb x x replicas
  | remove x => exact EfficientORSet.NeemScope.removes_commute ta ra tb rb x x

/-- The repaired formulation feeds the existing concrete replay metatheory. -/
def repaired : GuardedReplay.Laws (D α).toUpdateSig (EfficientORSet.EventSpec.conflict α) :=
  proposed.toGuarded equal_operation_commutes

/-- The repair does not incorrectly assert commutation for repeated local adds. -/
theorem local_adds_still_noncommuting (x : α) :
    ¬ (D α).toUpdateSig.commutes (1,0,.add x) (2,0,.add x) :=
  EfficientORSet.EventSpec.same_replica_adds_noncomm x

end Efficient

#print axioms Counter.proposed
#print axioms Counter.missing_equal_operation_condition
#print axioms Counter.missing_scoped_diamond
#print axioms Efficient.repaired
#print axioms DistinctOperationReplay.replay_equal
#print axioms DistinctOperationPolicy.Invariant.ofExisting
#print axioms DistinctOperationPolicy.Invariant.canonical_unique
end Sal.MRDTs.Paper1.DistinctOperationControls
