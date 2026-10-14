import Sal.MRDTs.Paper1.OptionalRegisterReadSide
import Sal.MRDTs.Paper1.OptionalRegisterVC
import Sal.MRDTs.Paper1.OptionalRegisterExecution

namespace Sal.MRDTs.Paper1.OptionalRegister
open Foundation Instances.OptionalRegister

/-- Every certified stored map satisfies the exact refinement of the supplied
F* concrete_st type. Positivity comes from the explicit issuance guard;
field semantics come from the five-VC-derived Join and execution induction.
Both ordinary executions and recursive virtual merge-base executions are covered. -/
theorem sourceWellFormed {C : Configuration D}
    (execution : CertifiedExecution D generation C)
    {v : Version} {s : State} {E : Set Event} (hv : C.ver v = some (s,E)) :
    SourceWellFormed s := by
  have reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C := by
    cases execution with
    | ordinary reach => exact reach.toV
    | virtual reach => exact reach
  have hs := representedVersionsOfJoin representationJoin reach v s E hv
  exact sourceWellFormed_of_representation C.replayContext E s hs
    (fun e he => positive_events execution e (hs.supported e he))

theorem sourceWellFormedV {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C)
    {v : Version} {s : State} {E : Set Event} (hv : C.ver v = some (s,E)) :
    SourceWellFormed s := sourceWellFormed (.virtual reach) hv

theorem sourceWellFormedOrdinary {C : Configuration D}
    (reach : MintCertifiedReach D generation C)
    {v : Version} {s : State} {E : Set Event} (hv : C.ver v = some (s,E)) :
    SourceWellFormed s := sourceWellFormed (.ordinary reach) hv

#print axioms sourceWellFormed
#print axioms sourceWellFormedV
end Sal.MRDTs.Paper1.OptionalRegister
