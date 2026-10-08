import Sal.MRDTs.Paper1.ConcreteFormalism
import Sal.MRDTs.Paper1.ExecutionTrace

/-! Independent sequential histories explain exact concrete replays.
No implementation-state abstraction or observational equality is used. -/
namespace Sal.MRDTs.Paper1.ConcreteMRDT
open Foundation
variable {D : MRDTSig}

abbrev ExecutionHistoryAdequacy (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D) :=
  EventExecutionHistoryAdequacy D P S I

def CanonicalUnique (P : OperationPolicy D.AppOp) : Prop :=
  ∀ C E, Supported C E → ∀ s t,
    Canonical P C E s → Canonical P C E t → s = t

theorem of_canonical {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {C : Configuration D}
    (canonical : ∀ v s E, C.ver v = some (s,E) → Canonical P C.replayContext E s)
    (compatible : CommutationCompatibility D id S) (sound : EventFoldHistorySound D S) :
    VersionsWitness P S C := by
  intro v s E hv q
  obtain ⟨π,hp,ho,hf⟩ := canonical v s E hv
  refine ⟨π,hp,ho,?_,?_⟩
  · exact ho.imp (fun {_ _} h => h ∘
      projectedSpecVisibility_sub_paperOrder compatible C.replayContext E _ _)
  · simpa only [hf] using sound π q

theorem versions_of_scoped_history {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (unique : CanonicalUnique P) (history : ExecutionHistoryAdequacy P S I)
    {C : Configuration D} (execution : CertifiedExecution D I C)
    (supported : ∀ v s E, C.ver v = some (s,E) → Supported C.replayContext E)
    (canonical : ∀ v s E, C.ver v = some (s,E) → Canonical P C.replayContext E s) :
    VersionsWitness P S C := by
  intro v s E hv q
  obtain ⟨π,hp,ho,hs,accepted⟩ := history C execution v s E hv q
  have same := unique C.replayContext E (supported v s E hv)
    _ _ ⟨π,hp,ho,rfl⟩ (canonical v s E hv)
  exact ⟨π,hp,ho,hs,by simpa only [same] using accepted⟩

structure ScopedCertificate (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D) : Prop where
  laws : GuardedReplay.Laws D.toUpdateSig P
  unique : CanonicalUnique P
  supportedVersions : ∀ C, CertifiedExecution D I C →
    ∀ v s E, C.ver v = some (s,E) → Supported C.replayContext E
  canonicalVersions : ∀ C, CertifiedExecution D I C →
    ∀ v s E, C.ver v = some (s,E) → Canonical P C.replayContext E s
  history : ExecutionHistoryAdequacy P S I

def ScopedCertificate.ofTotal {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (laws : GuardedReplay.Laws D.toUpdateSig P) (unique : CanonicalUnique P)
    (supported : ∀ C, CertifiedExecution D I C →
      ∀ v s E, C.ver v = some (s,E) → Supported C.replayContext E)
    (canonical : ∀ C, CertifiedExecution D I C →
      ∀ v s E, C.ver v = some (s,E) → Canonical P C.replayContext E s)
    (compatible : CommutationCompatibility D id S) (sound : EventFoldHistorySound D S) :
    ScopedCertificate P S I where
  laws := laws
  unique := unique
  supportedVersions := supported
  canonicalVersions := canonical
  history := by
    intro C execution v s E hv q
    obtain ⟨π,hp,ho,_⟩ := canonical C execution v s E hv
    refine ⟨π,hp,ho,?_,sound π q⟩
    exact ho.imp (fun {_ _} h => h ∘
      projectedSpecVisibility_sub_paperOrder compatible C.replayContext E _ _)

theorem ScopedCertificate.versions {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : ScopedCertificate P S I) {C : Configuration D}
    (execution : CertifiedExecution D I C) : VersionsWitness P S C :=
  versions_of_scoped_history cert.unique cert.history execution
    (cert.supportedVersions C execution) (cert.canonicalVersions C execution)

theorem ScopedCertificate.versionsV {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : ScopedCertificate P S I) {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) :
    VersionsWitness P S C := cert.versions (.virtual reach)

theorem ScopedCertificate.convergence {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : ScopedCertificate P S I) {C : Configuration D}
    (execution : CertifiedExecution D I C)
    {v w : Version} {s t : D.State} {E : Set (Op D.AppOp)}
    (hv : C.ver v = some (s,E)) (hw : C.ver w = some (t,E)) : s = t :=
  cert.unique C.replayContext E (cert.supportedVersions C execution v s E hv) s t
    (cert.canonicalVersions C execution v s E hv)
    (cert.canonicalVersions C execution w t E hw)

def ExecutionCorrect (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value)
    (trace : List (Label D × Configuration D)) : Prop :=
  VersionsWitness P S (initConfig D) ∧ ∀ entry ∈ trace, VersionsWitness P S entry.2

theorem ScopedCertificate.executions {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : ScopedCertificate P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D I).Execution (initConfig D) trace) :
    ExecutionCorrect P S trace := by
  have reached := ExecutionTrace.visited (Good := MintCertifiedReach D I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) execution .init
  exact ⟨cert.versions (.ordinary .init),
    fun entry he => cert.versions (.ordinary (reached entry he))⟩

theorem ScopedCertificate.executionsV {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : ScopedCertificate P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D I).Execution (initConfig D) trace) :
    ExecutionCorrect P S trace := by
  have reached := ExecutionTrace.visited
    (Good := MintCertifiedReachV D (canonicalVirtualMergeBase D) I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) execution .init
  exact ⟨cert.versions (.virtual .init),
    fun entry he => cert.versions (.virtual (reached entry he))⟩
end Sal.MRDTs.Paper1.ConcreteMRDT
