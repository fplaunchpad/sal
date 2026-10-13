import Sal.MRDTs.Paper1.SplitPolicy
import Sal.MRDTs.Paper1.Soundness
import Sal.MRDTs.Paper1.ConcreteVCExecution

/-! Paper-facing soundness takes the split policy fields as premises. The
proved adapters retain the five merge VCs, representation, canonical replay,
issuance and independent sequential-history bridge verbatim. -/
namespace Sal.MRDTs.Paper1.SplitPolicy
open Foundation

namespace Concrete
open ConcreteMRDT
variable {D : MRDTSig}

structure VCReplayConditions (P : OperationPolicy D.AppOp) (I : Issuance D) where
  representation : Representation D
  scheme : ∀ C, MetadataDependencies C
  laws : SplitPolicy.Laws D.toUpdateSig P
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


def VCReplayConditions.toExisting {P : OperationPolicy D.AppOp} {I : Issuance D}
    (c : VCReplayConditions P I) : ConcreteMRDT.VCReplayConditions P I where
  representation := c.representation
  scheme := c.scheme
  laws := c.laws.toGuarded
  vcs := c.vcs
  unique := c.unique
  initial := c.initial
  finite := c.finite
  canonical := c.canonical
  supported := c.supported
  replaySupply := c.replaySupply
  representedVersions := c.representedVersions

def VCReplayConditions.ofExisting {P : OperationPolicy D.AppOp} {I : Issuance D}
    (c : ConcreteMRDT.VCReplayConditions P I) : VCReplayConditions P I where
  representation := c.representation
  scheme := c.scheme
  laws := Laws.ofGuarded c.laws
  vcs := c.vcs
  unique := c.unique
  initial := c.initial
  finite := c.finite
  canonical := c.canonical
  supported := c.supported
  replaySupply := c.replaySupply
  representedVersions := c.representedVersions

def ScopedVCConditions.toExisting {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : ScopedVCConditions P S I) : ConcreteMRDT.ScopedVCConditions P S I where
  toVCReplayConditions := c.toVCReplayConditions.toExisting
  history := c.history

def ScopedVCConditions.ofExisting {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : ConcreteMRDT.ScopedVCConditions P S I) : ScopedVCConditions P S I where
  toVCReplayConditions := VCReplayConditions.ofExisting c.toVCReplayConditions
  history := c.history

def VCConditions.toExisting {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : VCConditions P S I) : ConcreteMRDT.VCConditions P S I where
  toVCReplayConditions := c.toVCReplayConditions.toExisting
  compatibility := c.compatibility
  historySound := c.historySound

def VCConditions.ofExisting {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : ConcreteMRDT.VCConditions P S I) : VCConditions P S I where
  toVCReplayConditions := VCReplayConditions.ofExisting c.toVCReplayConditions
  compatibility := c.compatibility
  historySound := c.historySound

theorem VCReplayConditions.join {P : OperationPolicy D.AppOp} {I : Issuance D}
    (c : VCReplayConditions P I) : RepresentationJoin c.representation := c.toExisting.join

theorem ScopedVCConditions.executions {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : ScopedVCConditions P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D I).Execution (initConfig D) trace) : ExecutionCorrect P S trace :=
  c.toExisting.executions trace execution

theorem ScopedVCConditions.executionsV {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : ScopedVCConditions P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D I).Execution (initConfig D) trace) : ExecutionCorrect P S trace :=
  c.toExisting.executionsV trace execution

theorem ScopedVCConditions.versionsV {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : ScopedVCConditions P S I) {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) : VersionsWitness P S C :=
  c.toExisting.versionsV reach

theorem VCConditions.executions {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : VCConditions P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D I).Execution (initConfig D) trace) : ExecutionCorrect P S trace :=
  c.toExisting.executions trace execution

theorem VCConditions.executionsV {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : VCConditions P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D I).Execution (initConfig D) trace) : ExecutionCorrect P S trace :=
  c.toExisting.executionsV trace execution

theorem VCConditions.versionsV {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : VCConditions P S I) {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) : VersionsWitness P S C :=
  c.toExisting.versionsV reach

/-- End-to-end concrete certificate with the split policy as an actual field. -/
structure ScopedCertificate (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D) : Prop where
  laws : SplitPolicy.Laws D.toUpdateSig P
  unique : CanonicalUnique P
  supportedVersions : ∀ C, CertifiedExecution D I C →
    ∀ v s E, C.ver v = some (s,E) → Supported C.replayContext E
  canonicalVersions : ∀ C, CertifiedExecution D I C →
    ∀ v s E, C.ver v = some (s,E) → Canonical P C.replayContext E s
  history : ExecutionHistoryAdequacy P S I

def ScopedCertificate.toExisting {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : ScopedCertificate P S I) : ConcreteMRDT.ScopedCertificate P S I :=
  ⟨c.laws.toGuarded,c.unique,c.supportedVersions,c.canonicalVersions,c.history⟩

def ScopedCertificate.ofExisting {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : ConcreteMRDT.ScopedCertificate P S I) : ScopedCertificate P S I :=
  ⟨Laws.ofGuarded c.laws,c.unique,c.supportedVersions,c.canonicalVersions,c.history⟩

theorem ScopedCertificate.executions {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : ScopedCertificate P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D I).Execution (initConfig D) trace) : ExecutionCorrect P S trace :=
  c.toExisting.executions trace execution

theorem ScopedCertificate.executionsV {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (c : ScopedCertificate P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D I).Execution (initConfig D) trace) : ExecutionCorrect P S trace :=
  c.toExisting.executionsV trace execution

end Concrete

namespace Certified
variable {D : UpdateSig} {P : OperationPolicy D.AppOp} {S : CertifiedReplay.Scope D}

theorem canonical_unique (L : RestrictedLaws S P) {initial a b : D.State}
    (represented : S.represented ∅ initial)
    (ha : CertifiedReplay.Canonical S P initial a)
    (hb : CertifiedReplay.Canonical S P initial b) : a = b :=
  CertifiedReplay.canonical_unique L.replay represented ha hb
end Certified

namespace Invariant
variable {D : UpdateSig} {P : OperationPolicy D.AppOp} {S : InvariantReplay.Scope D}
    {Inv : D.State → Prop}

theorem canonical_unique (L : RestrictedLaws S Inv P) {initial a b : D.State}
    (represented : S.represented ∅ initial)
    (ha : InvariantReplay.Canonical S Inv P initial a)
    (hb : InvariantReplay.Canonical S Inv P initial b) : a = b :=
  InvariantReplay.canonical_unique L.replay represented ha hb
end Invariant
namespace Certified
open ConcreteMRDT
variable {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {Spec : HistorySpec (Op D.AppOp) D.Query D.Value} {C : Configuration D}


/-- Query soundness from split scoped laws and independently admitted canonical
histories. The language and specification visibility are unchanged. -/
theorem versions_of_canonical_histories
    (scope : Set (Op D.AppOp) → CertifiedReplay.Scope D.toUpdateSig)
    (laws : ∀ E, RestrictedLaws (scope E) P)
    (initial : ∀ E, (scope E).represented ∅ D.init)
    (stored : ∀ v s E, C.ver v = some (s,E) →
      CertifiedReplay.Canonical (scope E) P D.init s)
    (history : ∀ v s E, C.ver v = some (s,E) → ∀ q,
      ∃ π t, listPermOf π E ∧ respects π (paperOrder P C.replayContext E) ∧
        respects π (projectedSpecVisibility id Spec C.replayContext) ∧
        CertifiedReplay.Canonical (scope E) P D.init t ∧
        Spec.admits (projectedLabels id π ++ [.query q (D.query t q)])) :
    ConcreteMRDT.VersionsWitness P Spec C := by
  intro v s E hv q
  obtain ⟨π,t,perm,ordered,visible,canonical,accepted⟩ := history v s E hv q
  have same : t = s := CertifiedReplay.canonical_unique (laws E).toExisting.replay (initial E)
    canonical (stored v s E hv)
  exact ⟨π,perm,ordered,visible,by simpa only [same] using accepted⟩
end Certified

namespace Invariant
open ConcreteMRDT
variable {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {Spec : HistorySpec (Op D.AppOp) D.Query D.Value} {C : Configuration D}
variable {Inv : D.State → Prop}

/-- Query soundness from split scoped laws and independently admitted canonical
histories. The language and specification visibility are unchanged. -/
theorem versions_of_canonical_histories
    (scope : Set (Op D.AppOp) → InvariantReplay.Scope D.toUpdateSig)
    (laws : ∀ E, RestrictedLaws (scope E) Inv P)
    (initial : ∀ E, (scope E).represented ∅ D.init)
    (stored : ∀ v s E, C.ver v = some (s,E) →
      InvariantReplay.Canonical (scope E) Inv P D.init s)
    (history : ∀ v s E, C.ver v = some (s,E) → ∀ q,
      ∃ π t, listPermOf π E ∧ respects π (InvariantOrder.order Inv P C.replayContext E) ∧
        respects π (projectedSpecVisibility id Spec C.replayContext) ∧
        InvariantReplay.Canonical (scope E) Inv P D.init t ∧
        Spec.admits (projectedLabels id π ++ [.query q (D.query t q)])) :
    InvariantOrder.VersionsRA D Inv P Spec C := by
  intro v s E hv q
  obtain ⟨π,t,perm,ordered,visible,canonical,accepted⟩ := history v s E hv q
  have same : t = s := InvariantReplay.canonical_unique (laws E).toExisting.replay (initial E)
    canonical (stored v s E hv)
  exact ⟨π,perm,ordered,visible,by simpa only [same] using accepted⟩
end Invariant

end Sal.MRDTs.Paper1.SplitPolicy
