import Sal.MRDTs.Paper1.PriorityQueueSameRecordHistory

/-! Complete scoped certificate for the intentional same-record repair.
The named five VCs feed the shared metadata Join induction; actual issuer
snapshots then select ordinary per-key histories, composed into one finite
priority-map history explaining every query (including maximum).

Issuance uses the source's exact Add-absent / Inc-and-Remove-present preparation.
The independent explaining machine instead has explicit total Add overwrite,
Inc absent no-op and Remove absent no-op semantics. All records have globally
unique causal operation timestamps in Sal's stored-version execution domain. -/
namespace Sal.MRDTs.Paper1.PriorityQueueSameRecord
open Foundation Instances.PriorityQueueSameRecord ConcreteMRDT

def conditions : ScopedVCConditions policy spec generation where
  toVCReplayConditions := replayConditions
  history := historyAdequacy

def certificate : ScopedCertificate policy spec generation := conditions.toCertificate

/-- Every allocated version, including old ancestors and recursively merged
versions, admits the independent ordinary queue history and preserves
specification-conflicting visibility. -/
theorem certifiedV : EventCertifiedSpecificationRAV D policy spec generation := by
  intro C reach
  exact certificate.versionsV reach

theorem certified : EventCertifiedSpecificationRA D policy spec generation := certifiedV.ordinary

theorem executions (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D generation).Execution (initConfig D) trace) :
    ExecutionCorrect policy spec trace := conditions.executions trace execution

theorem executionsV (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D generation).Execution (initConfig D) trace) :
    ExecutionCorrect policy spec trace := conditions.executionsV trace execution

theorem convergence {C : Configuration D} (execution : CertifiedExecution D generation C)
    {v w : Version} {s t : D.State} {E : Set Event}
    (hv : C.ver v = some (s,E)) (hw : C.ver w = some (t,E)) : s = t :=
  certificate.convergence execution hv hw

#print axioms certifiedV
#print axioms certified
#print axioms executions
#print axioms executionsV
#print axioms convergence
end Sal.MRDTs.Paper1.PriorityQueueSameRecord
