import Sal.MRDTs.Paper1.MetadataJoin
import Sal.MRDTs.Paper1.AbstractSoundness

/-! Sufficient conditions for issuance-certified execution correctness.
There is no Join field: it is derived from the observational VCs and metadata
obligations. Stored-version evidence separately accounts for issuance, context
transport, and recursive merge-base evaluation. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT
open Foundation
variable {D : MRDTSig}

structure VCReplayConditions (A : Model D) (P : OperationPolicy D.AppOp)
    (I : Issuance D) where
  representation : Representation D
  scheme : ∀ C, MetadataDependencies A C
  queryComplete : A.QueryComplete
  laws : Laws A P
  vcs : DependencyMergeVCs A P representation scheme
  canonical : RepresentsCanonical A P representation
  substitute : MetadataSubstitution A representation
  initial : InitialMetadata representation
  initMetadata : InitMetadata representation
  symmetry : MergeCommMetadata representation
  causal : CausalMetadata A P representation scheme
  localMetadata : LocalMetadata A P representation scheme
  sharedMetadata : SharedMetadata A P representation scheme
  replaySupply : ∀ C E₁ E₂ a b, Transitive C.vis → (∀ x, ¬ C.vis x x) →
    Supported C E₁ → Supported C E₂ → representation C E₁ a → representation C E₂ b →
    ReplaySupply A P representation scheme C
  representedVersions : ∀ C, MintCertifiedReachV D (canonicalVirtualMergeBase D) I C →
    ∀ v s E, C.ver v = some (s,E) → representation C.replayContext E s

structure VCConditions (A : Model D) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D)
    extends VCReplayConditions A P I where
  compatibility : SpecificationCompatibility A S
  historySound : EventFoldHistorySound D S

theorem VCReplayConditions.join {A : Model D} {P : OperationPolicy D.AppOp}
    {I : Issuance D} (conditions : VCReplayConditions A P I) :
    RepresentationJoin conditions.representation :=
  representationJoin_of_vcs conditions.laws conditions.vcs conditions.canonical
    conditions.substitute conditions.initial conditions.initMetadata conditions.symmetry
    conditions.causal conditions.localMetadata conditions.sharedMetadata conditions.replaySupply

def VCConditions.toCertificate {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (conditions : VCConditions A P S I) : Certificate A P S I where
  queryComplete := conditions.queryComplete
  laws := conditions.laws
  representation := conditions.representation
  representsCanonical := conditions.canonical
  representationJoin := conditions.toVCReplayConditions.join
  representedVersions := conditions.representedVersions
  compatibility := conditions.compatibility
  historySound := conditions.historySound

theorem VCConditions.executions {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (conditions : VCConditions A P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D I).Execution (initConfig D) trace) : ExecutionCorrect A P S trace :=
  conditions.toCertificate.executions trace execution

theorem VCConditions.executionsV {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (conditions : VCConditions A P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D I).Execution (initConfig D) trace) : ExecutionCorrect A P S trace :=
  conditions.toCertificate.executionsV trace execution

end Sal.MRDTs.Paper1.AbstractMRDT
