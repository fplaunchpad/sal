import Sal.MRDTs.Paper1.GuardedRawExactExecution
import Sal.MRDTs.Paper1.ORSetSpecification

/-! Payload-set specification correctness derived from the five concrete VCs.
No direct datatype Join theorem or client-supplied merge premise is used. -/
namespace Sal.MRDTs.Paper1.ORSet.PaperContract
open Foundation
variable {α : Type} [DecidableEq α]
noncomputable local instance : ReplayPolicy (D α).toUpdateSig := (conflict α).lift

theorem specificationCertifiedRAV {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (issuance α) C) :
    SpecificationRALinearizable (D α) (conflict α) (spec α).toSpec C :=
  specificationRA_of_canonical_total restrictedLaws
    (RawExecution.vcCanonicalConfig reach) specificationConflictsCovered foldHistorySound

theorem specificationCertifiedRA {C : Configuration (D α)}
    (reach : MintCertifiedReach (D α) (issuance α) C) :
    SpecificationRALinearizable (D α) (conflict α) (spec α).toSpec C :=
  specificationCertifiedRAV reach.toV

theorem specificationRawRA {C : Configuration (D α)}
    (reach : (labeledTS (D α)).ReachableFrom (initConfig (D α)) C) :
    SpecificationRALinearizable (D α) (conflict α) (spec α).toSpec C :=
  specificationRA_of_replay_total restrictedLaws
    (replayWitness_of_join RawExecution.vcJoinAt C reach)
    specificationConflictsCovered foldHistorySound

theorem specificationRawRAV {C : Configuration (D α)}
    (reach : (labeledTSV (D α) (canonicalVirtualMergeBase (D α))).ReachableFrom
      (initConfig (D α)) C) :
    SpecificationRALinearizable (D α) (conflict α) (spec α).toSpec C :=
  specificationRA_of_canonical_total restrictedLaws
    (canonicalConfig_reachableV RawExecution.vcJoinAt reach)
    specificationConflictsCovered foldHistorySound

#print axioms specificationRawRA
#print axioms specificationRawRAV
end Sal.MRDTs.Paper1.ORSet.PaperContract
