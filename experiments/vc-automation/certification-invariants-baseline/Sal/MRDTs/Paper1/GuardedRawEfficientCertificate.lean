import Sal.MRDTs.Paper1.ConcreteHistoryBridge
import Sal.MRDTs.Paper1.GuardedRawORSetJoin
import Sal.MRDTs.Paper1.GuardedRawEfficientExecution

/-! Efficient OR-set correctness with concrete equality throughout the merge
VC and canonical-state conclusions. Join and stored canonicality are derived.
The sequential specification is the independent ordinary-set language. -/
namespace Sal.MRDTs.Paper1.EfficientORSet.RawCertificate
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

theorem representedVersions {C : Configuration (D α)}
    (execution : CertifiedExecution (D α) issuance C) :
    ∀ v s E, C.ver v = some (s,E) → ConcreteRep.representation C.replayContext E s := by
  cases execution with
  | ordinary reach =>
    exact RawExecution.vcRepresentedVersions GuardedRawVC.representationJoin reach.toV
  | virtual reach =>
    exact RawExecution.vcRepresentedVersions GuardedRawVC.representationJoin reach

def certificate : ConcreteMRDT.ScopedCertificate
    (EventSpec.conflict α) (EventSpec.spec α) issuance :=
  ConcreteMRDT.ScopedCertificate.ofTotal Guarded.laws
    (fun C E supported _ _ hs ht => ConcreteMRDT.canonical_unique Guarded.laws C E supported hs ht)
    (fun _ execution v s E hv => (representedVersions execution v s E hv).2.2.1)
    (fun _ execution v s E hv =>
      RawReplay.representsCanonical _ _ _ (representedVersions execution v s E hv))
    EventSpec.commutationCompatibility EventSpec.foldHistorySound

/-- Every stored state is exactly a semantic-order replay, including its tags. -/
theorem storedCanonical {C : Configuration (D α)}
    (execution : CertifiedExecution (D α) issuance C)
    {v : Version} {s : (D α).State} {E : Set (Op (D α).AppOp)}
    (hv : C.ver v = some (s,E)) :
    ∃ π, listPermOf π E ∧ respects π (paperOrder (EventSpec.conflict α) C.replayContext E) ∧
      applySeq (D α).toUpdateSig (D α).init π = s :=
  certificate.canonicalVersions C execution v s E hv

theorem versionsV {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) issuance C) :
    ConcreteMRDT.VersionsWitness
      (EventSpec.conflict α) (EventSpec.spec α) C := certificate.versionsV reach

theorem executions (trace : List (Label (D α) × Configuration (D α)))
    (execution : (certifiedTS (D α) issuance).Execution (initConfig (D α)) trace) :
    ConcreteMRDT.ExecutionCorrect
      (EventSpec.conflict α) (EventSpec.spec α) trace := certificate.executions trace execution

theorem executionsV (trace : List (Label (D α) × Configuration (D α)))
    (execution : (certifiedTSV (D α) issuance).Execution (initConfig (D α)) trace) :
    ConcreteMRDT.ExecutionCorrect
      (EventSpec.conflict α) (EventSpec.spec α) trace := certificate.executionsV trace execution

theorem convergence {C : Configuration (D α)}
    (execution : CertifiedExecution (D α) issuance C)
    {v w : Version} {s t : (D α).State} {E : Set (Op (D α).AppOp)}
    (hv : C.ver v = some (s,E)) (hw : C.ver w = some (t,E)) : s = t :=
  certificate.convergence execution hv hw

end Sal.MRDTs.Paper1.EfficientORSet.RawCertificate
