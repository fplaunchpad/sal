import Sal.MRDTs.Paper1.SetWinsMapEvent

namespace Sal.MRDTs.Paper1.SetWinsMap
open Foundation ConcreteMRDT Instances.SetWinsMap

def replayConditions : VCReplayConditions policy issuance where
  representation := representation
  scheme := scheme
  laws := splitLaws.toGuarded
  vcs := fiveVC
  unique := unique
  initial := fun C _ _ _ => initial C
  finite := finite
  canonical := canonical
  supported := fun _ _ _ h => h.2
  replaySupply := fun C _ _ _ _ trans irrefl _ _ _ _ => replaySupply C trans irrefl
  representedVersions := fun _ reach v s E hv => representedVersions reach v s E hv

def conditions : VCConditions policy spec issuance where
  toVCReplayConditions := replayConditions
  compatibility := compatibility
  historySound := historySound

theorem certifiedV : EventCertifiedSpecificationRAV D policy spec issuance := by
  intro C reach
  exact conditions.versionsV reach

theorem certified : EventCertifiedSpecificationRA D policy spec issuance := certifiedV.ordinary

theorem executions (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D issuance).Execution (initConfig D) trace) :
    ExecutionCorrect policy spec trace := conditions.executions trace execution

theorem executionsV (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D issuance).Execution (initConfig D) trace) :
    ExecutionCorrect policy spec trace := conditions.executionsV trace execution

#print axioms certifiedV
#print axioms certified
#print axioms executionsV
#print axioms splitLaws
end Sal.MRDTs.Paper1.SetWinsMap
