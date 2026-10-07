import Sal.MRDTs.Paper1.VCExecutionContract

/-! An execution-scoped history bridge for specifications with issuance or
anchor guards. It explains a merge-free fold, not the stored query result.
Observable canonical uniqueness then connects that fold to the stored state.
Global implementation/specification commutation compatibility is not assumed.
-/
namespace Sal.MRDTs.Paper1.AbstractMRDT
open Foundation
variable {D : MRDTSig}

def ExecutionHistoryAdequacy (A : Model D) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D) : Prop :=
  ∀ C, CertifiedExecution D I C → ∀ v s E, C.ver v = some (s,E) →
    ∀ q, ∃ π : List (Op D.AppOp),
      listPermOf π E ∧ respects π (order A P C.replayContext E) ∧
      respects π (projectedSpecVisibility id S C.replayContext) ∧
      S.admits (projectedLabels id π ++
        [.query q (D.query (applySeq D.toUpdateSig D.init π) q)])

theorem versions_of_scoped_history {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (laws : Laws A P) (history : ExecutionHistoryAdequacy A P S I)
    {C : Configuration D} (execution : CertifiedExecution D I C)
    (supported : ∀ v s E, C.ver v = some (s,E) → Supported C.replayContext E)
    (canonical : ∀ v s E, C.ver v = some (s,E) → Canonical A P C.replayContext E s) :
    VersionsRALinearizable A P S C := by
  refine ⟨laws, ?_⟩
  intro v s E hv q
  obtain ⟨π,hp,ho,hs,accepted⟩ := history C execution v s E hv q
  have folded : Canonical A P C.replayContext E
      (applySeq D.toUpdateSig D.init π) :=
    (canonical_iff laws _ _ _).mpr ⟨π,hp,ho,rfl⟩
  have same := canonical_query_unique laws C.replayContext E
    (supported v s E hv) folded (canonical v s E hv) q
  exact ⟨π,hp,ho,hs,by simpa only [same] using accepted⟩

structure ScopedVCConditions (A : Model D) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D)
    extends VCReplayConditions A P I where
  supportedVersions : ∀ C, MintCertifiedReachV D (canonicalVirtualMergeBase D) I C →
    ∀ v s E, C.ver v = some (s,E) → Supported C.replayContext E
  history : ExecutionHistoryAdequacy A P S I

theorem ScopedVCConditions.versionsV {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (conditions : ScopedVCConditions A P S I) {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) :
    VersionsRALinearizable A P S C :=
  versions_of_scoped_history conditions.laws conditions.history (.virtual reach)
    (conditions.supportedVersions C reach)
    (fun v s E hv => conditions.canonical _ _ _ (conditions.representedVersions C reach v s E hv))

theorem ScopedVCConditions.executionsV {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (conditions : ScopedVCConditions A P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D I).Execution (initConfig D) trace) :
    ExecutionCorrect A P S trace := by
  have versions := visited (Good := MintCertifiedReachV D (canonicalVirtualMergeBase D) I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) execution .init
  exact ⟨conditions.versionsV .init,fun entry he => conditions.versionsV (versions entry he)⟩

theorem ScopedVCConditions.executions {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (conditions : ScopedVCConditions A P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D I).Execution (initConfig D) trace) :
    ExecutionCorrect A P S trace := by
  have versions := visited (Good := MintCertifiedReach D I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) execution .init
  exact ⟨conditions.versionsV .init,fun entry he => conditions.versionsV (versions entry he).toV⟩

end Sal.MRDTs.Paper1.AbstractMRDT
