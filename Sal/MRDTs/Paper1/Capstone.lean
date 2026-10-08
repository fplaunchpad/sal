import Sal.MRDTs.Paper1.ORSetSpecification
import Sal.MRDTs.Paper1.RGAActive

/-! The exact paper OR-set has an unrestricted sequential bridge, so its
ordinary raw execution guarantee needs no issuance assumptions. RGA's
issuance-sensitive guarantee remains in `RGAActive`. -/

namespace Sal.MRDTs.Paper1.ORSet
open Foundation
variable {α : Type} [DecidableEq α]

theorem rawRA : RAImplementation (D α) (conflict α) (spec α).toSpec := by
  apply rawRA_of_join_total restrictedLaws _ foldHistorySound
  rw [conflict_lift_eq]
  exact join

/-- At every raw reachable configuration, each allocated version has a single
update history explaining all queries, including queries not taken in the trace. -/
theorem rawUniformRA {C : Configuration (D α)}
    (reach : (labeledTS (D α)).ReachableFrom (initConfig (D α)) C) :
    UniformVersionsRALinearizable (D α) (conflict α) (spec α).toSpec C := by
  letI : ReplayPolicy (D α).toUpdateSig := (conflict α).lift
  have hjoin : @Join (D α) (conflict α).lift := by
    rw [conflict_lift_eq]
    exact join
  exact uniform_ra_of_replay_total restrictedLaws
    (replayWitness_of_join hjoin C reach) foldHistorySound

/-- The specification-visible criterion also holds at every raw reachable configuration. -/
theorem rawSpecificationRA {C : Configuration (D α)}
    (reach : (labeledTS (D α)).ReachableFrom (initConfig (D α)) C) :
    SpecificationRALinearizable (D α) (conflict α) (spec α).toSpec C := by
  letI : ReplayPolicy (D α).toUpdateSig := (conflict α).lift
  have hjoin : @Join (D α) (conflict α).lift := by
    rw [conflict_lift_eq]
    exact join
  exact specificationRA_of_replay_total restrictedLaws
    (replayWitness_of_join hjoin C reach) specificationConflictsCovered foldHistorySound

end Sal.MRDTs.Paper1.ORSet
