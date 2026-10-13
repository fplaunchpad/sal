import Sal.MRDTs.Paper1.ConcreteVCExecution
import Sal.MRDTs.Paper1.DistinctOperationReplay

/-! Total sequential soundness needs the actual state's canonical replay,
not uniqueness of every permitted replay. The conditions below retain every
five-VC, representation and certified-execution field of VCReplayConditions;
only its policy-law field uses payload-distinct exactness. This result does
not cover the existential execution-scoped history bridge. -/
namespace Sal.MRDTs.Paper1.ConcreteMRDT
open Foundation
variable {D : MRDTSig}

structure DistinctVCReplayConditions (P : OperationPolicy D.AppOp) (I : Issuance D) where
  representation : Representation D
  scheme : ∀ C, MetadataDependencies C
  laws : DistinctOperationReplay.Laws D.toUpdateSig P
  vcs : Raw.MergeVCs P representation scheme
  unique : Raw.Unique representation
  initial : ∀ C E s, representation C E s → representation C ∅ D.init
  finite : ∀ C E s, representation C E s → ∃ π, listPermOf π E
  canonical : ∀ C E s, representation C E s → Canonical P C E s
  supported : ∀ C E s, representation C E s → Supported C E
  replaySupply : ∀ C E₁ E₂ a b, Transitive C.vis → (∀ x, ¬ C.vis x x) →
    Supported C E₁ → Supported C E₂ → representation C E₁ a → representation C E₂ b →
    Raw.ReplaySupply P representation scheme C
  representedVersions : ∀ C, MintCertifiedReachV D (canonicalVirtualMergeBase D) I C →
    ∀ v s E, C.ver v = some (s,E) → representation C.replayContext E s

structure DistinctVCConditions (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D)
    extends DistinctVCReplayConditions P I where
  compatibility : CommutationCompatibility D id S
  historySound : EventFoldHistorySound D S

/-- The existing existential scoped bridge, with only the replay-law field
changed. Unlike the total bridge above, this contract need not be sound. -/
structure DistinctScopedVCConditions (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D)
    extends DistinctVCReplayConditions P I where
  history : ExecutionHistoryAdequacy P S I

theorem DistinctVCReplayConditions.join {P : OperationPolicy D.AppOp} {I : Issuance D}
    (c : DistinctVCReplayConditions P I) : RepresentationJoin c.representation :=
  Raw.representationJoin_of_vcs c.vcs c.unique c.initial c.finite c.replaySupply

theorem DistinctVCConditions.versions {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : DistinctVCConditions P S I) {C : Configuration D}
    (execution : CertifiedExecution D I C) : VersionsWitness P S C := by
  have reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C := by
    cases execution with
    | ordinary reach => exact reach.toV
    | virtual reach => exact reach
  exact of_canonical
    (fun v s E hv => c.canonical _ _ _ (c.representedVersions C reach v s E hv))
    c.compatibility c.historySound

theorem DistinctVCConditions.executions {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : DistinctVCConditions P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D I).Execution (initConfig D) trace) :
    ExecutionCorrect P S trace := by
  have reached := ExecutionTrace.visited (Good := MintCertifiedReach D I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) execution .init
  exact ⟨c.versions (.ordinary .init),
    fun entry he => c.versions (.ordinary (reached entry he))⟩

theorem DistinctVCConditions.executionsV {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : DistinctVCConditions P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D I).Execution (initConfig D) trace) :
    ExecutionCorrect P S trace := by
  have reached := ExecutionTrace.visited
    (Good := MintCertifiedReachV D (canonicalVirtualMergeBase D) I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) execution .init
  exact ⟨c.versions (.virtual .init),
    fun entry he => c.versions (.virtual (reached entry he))⟩

end Sal.MRDTs.Paper1.ConcreteMRDT
