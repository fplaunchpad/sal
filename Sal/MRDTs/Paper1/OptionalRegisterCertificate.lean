import Sal.MRDTs.Paper1.OptionalRegisterVC
import Sal.MRDTs.Paper1.OptionalRegisterExecution
import Sal.MRDTs.Paper1.OptionalRegisterHistory

/-! The final optional-register root consumes the five source VCs through the
finite Join induction and both ordinary/recursive execution preservation. Its
independent scalar optional-register language has a scoped history bridge. -/
namespace Sal.MRDTs.Paper1.OptionalRegister
open Foundation ConcreteMRDT Instances.OptionalRegister

theorem representedVersions {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C)
    (v : Version) (s : State) (E : Set Event) (hv : C.ver v = some (s,E)) :
    representation C.replayContext E s :=
  representedVersionsOfJoin representationJoin reach v s E hv

private theorem virtual_reach {C : Configuration D} (execution : CertifiedExecution D generation C) :
    MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C := by
  cases execution with
  | ordinary reach => exact reach.toV
  | virtual reach => exact reach

theorem representedExecutionVersions (C : Configuration D)
    (execution : CertifiedExecution D generation C) (v : Version) (s : State)
    (E : Set Event) (hv : C.ver v = some (s,E)) : representation C.replayContext E s :=
  representedVersions (virtual_reach execution) v s E hv

theorem canonicalExecutionVersions (C : Configuration D)
    (execution : CertifiedExecution D generation C) (v : Version) (s : State)
    (E : Set Event) (hv : C.ver v = some (s,E)) : Canonical policy C.replayContext E s :=
  canonical C.replayContext E s (representedExecutionVersions C execution v s E hv)

theorem history : EventExecutionHistoryAdequacy D policy spec generation :=
  history_from_representation representedExecutionVersions canonicalExecutionVersions

def replayConditions : VCReplayConditions policy generation where
  representation := representation
  scheme := scheme
  laws := splitLaws.toGuarded
  vcs := fiveVC
  unique := unique
  initial := fun C _ _ hs => initial_rep C hs.good
  finite := finite_rep
  canonical := canonical
  supported := fun _ _ _ hs => hs.supported
  replaySupply := fun C _ _ _ _ _ _ _ _ ha _ => replaySupply C ha.good
  representedVersions := fun _ reach v s E hv => representedVersions reach v s E hv

def conditions : ScopedVCConditions policy spec generation where
  toVCReplayConditions := replayConditions
  history := history

theorem certifiedV : EventCertifiedSpecificationRAV D policy spec generation := by
  intro C reach
  exact conditions.versionsV reach

theorem certified : EventCertifiedSpecificationRA D policy spec generation := certifiedV.ordinary

theorem executions (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D generation).Execution (initConfig D) trace) :
    ExecutionCorrect policy spec trace := conditions.executions trace execution

theorem executionsV (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D generation).Execution (initConfig D) trace) :
    ExecutionCorrect policy spec trace := conditions.executionsV trace execution

theorem convergence {C : Configuration D} (execution : CertifiedExecution D generation C)
    {v w : Version} {s t : State} {E : Set Event}
    (hv : C.ver v = some (s,E)) (hw : C.ver w = some (t,E)) : s = t :=
  conditions.toCertificate.convergence execution hv hw

#print axioms certifiedV
#print axioms executionsV
#print axioms history
#print axioms convergence
end Sal.MRDTs.Paper1.OptionalRegister
