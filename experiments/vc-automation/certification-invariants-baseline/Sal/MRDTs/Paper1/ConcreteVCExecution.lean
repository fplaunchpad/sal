import Sal.MRDTs.Paper1.ConcreteJoin
import Sal.MRDTs.Paper1.ConcreteReplay
import Sal.MRDTs.Paper1.ConcreteHistoryBridge

/-! Concrete sufficient conditions retaining the five-VC dependency gate.
Join is derived by the event-set induction rather than supplied as a field. -/
namespace Sal.MRDTs.Paper1.ConcreteMRDT
open Foundation
variable {D : MRDTSig}

structure VCReplayConditions (P : OperationPolicy D.AppOp) (I : Issuance D) where
  representation : Representation D
  scheme : ∀ C, MetadataDependencies C
  laws : GuardedReplay.Laws D.toUpdateSig P
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

structure VCConditions (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D)
    extends VCReplayConditions P I where
  compatibility : CommutationCompatibility D id S
  historySound : EventFoldHistorySound D S

structure ScopedVCConditions (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D)
    extends VCReplayConditions P I where
  history : ExecutionHistoryAdequacy P S I

theorem VCReplayConditions.join {P : OperationPolicy D.AppOp} {I : Issuance D}
    (c : VCReplayConditions P I) : RepresentationJoin c.representation :=
  Raw.representationJoin_of_vcs c.vcs c.unique c.initial c.finite c.replaySupply

private theorem virtual_reach {I : Issuance D} {C : Configuration D}
    (execution : CertifiedExecution D I C) :
    MintCertifiedReachV D (canonicalVirtualMergeBase D) I C := by
  cases execution with
  | ordinary reach => exact reach.toV
  | virtual reach => exact reach

def VCConditions.toCertificate {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : VCConditions P S I) : ScopedCertificate P S I :=
  ScopedCertificate.ofTotal c.laws
    (fun C E sup s t hs ht => canonical_unique c.laws C E sup hs ht)
    (fun C ex v s E hv => c.supported _ _ _ (c.representedVersions C (virtual_reach ex) v s E hv))
    (fun C ex v s E hv => c.canonical _ _ _ (c.representedVersions C (virtual_reach ex) v s E hv))
    c.compatibility c.historySound

def ScopedVCConditions.toCertificate {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : ScopedVCConditions P S I) : ScopedCertificate P S I where
  laws := c.laws
  unique := fun C E sup s t hs ht => canonical_unique c.laws C E sup hs ht
  supportedVersions := fun C ex v s E hv => c.supported _ _ _ (c.representedVersions C (virtual_reach ex) v s E hv)
  canonicalVersions := fun C ex v s E hv => c.canonical _ _ _ (c.representedVersions C (virtual_reach ex) v s E hv)
  history := c.history

theorem VCConditions.executions {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : VCConditions P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D I).Execution (initConfig D) trace) : ExecutionCorrect P S trace :=
  c.toCertificate.executions trace execution

theorem VCConditions.executionsV {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : VCConditions P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D I).Execution (initConfig D) trace) : ExecutionCorrect P S trace :=
  c.toCertificate.executionsV trace execution

theorem VCConditions.versionsV {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : VCConditions P S I) {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) : VersionsWitness P S C :=
  c.toCertificate.versionsV reach

theorem ScopedVCConditions.executions {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : ScopedVCConditions P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D I).Execution (initConfig D) trace) : ExecutionCorrect P S trace :=
  c.toCertificate.executions trace execution

theorem ScopedVCConditions.executionsV {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : ScopedVCConditions P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D I).Execution (initConfig D) trace) : ExecutionCorrect P S trace :=
  c.toCertificate.executionsV trace execution

theorem ScopedVCConditions.versionsV {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : ScopedVCConditions P S I) {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) : VersionsWitness P S C :=
  c.toCertificate.versionsV reach

end Sal.MRDTs.Paper1.ConcreteMRDT
