import Sal.MRDTs.Paper1.GuardedHistoryBridge
import Sal.MRDTs.Paper1.GuardedRawModel
import Sal.MRDTs.Paper1.SimpleAbstractPorts
import Sal.MRDTs.Paper1.GuardedAbstractPorts
import Sal.MRDTs.Paper1.RGAAbstractPort

/-! Positive production ports into the guarded public criterion. The adapters
below explicitly use already-proved stronger uniform laws and their VC-derived
stored canonicality. They do not posit a direct production Join theorem.
All twelve entries use identity models. The four issuance-sensitive entries
retain independent specifications and scoped history proofs from their existing
positive VC ports; exact canonical metadata comes from the VC induction. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT.Guarded.Positive
open Foundation
variable {D : MRDTSig}

private theorem virtual_reach {I : Issuance D} {C : Configuration D}
    (execution : CertifiedExecution D I C) :
    MintCertifiedReachV D (canonicalVirtualMergeBase D) I C := by
  cases execution with
  | ordinary reach => exact reach.toV
  | virtual reach => exact reach

/-- Explicit sufficient adapter from a positive uniform scoped VC port. -/
def ofScopedVC {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (conditions : ScopedVCConditions A P S I) : ScopedCertificate A P S I where
  laws := Laws.ofUniform conditions.laws
  supportedVersions := fun C execution => conditions.supportedVersions C (virtual_reach execution)
  canonicalVersions := by
    intro C execution v s E hv
    apply (canonical_iff_uniform conditions.laws _ _ _).mpr
    exact conditions.canonical _ _ _
      (conditions.representedVersions C (virtual_reach execution) v s E hv)
  history := conditions.history

/-- Total languages require no extra support premise at the history bridge. -/
structure TotalCertificate (A : Model D) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D) : Prop where
  laws : Laws A P
  canonicalVersions : ∀ C, CertifiedExecution D I C →
    ∀ v s E, C.ver v = some (s,E) → Canonical A P C.replayContext E s
  compatibility : SpecificationCompatibility A S
  historySound : EventFoldHistorySound D S

/-- Explicit sufficient adapter retaining the original VC-derived proof. -/
def ofTotalVC {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (conditions : VCConditions A P S I) : TotalCertificate A P S I where
  laws := Laws.ofUniform conditions.laws
  canonicalVersions := by
    intro C execution v s E hv
    apply (canonical_iff_uniform conditions.laws _ _ _).mpr
    exact conditions.canonical _ _ _
      (conditions.representedVersions C (virtual_reach execution) v s E hv)
  compatibility := conditions.compatibility
  historySound := conditions.historySound

theorem TotalCertificate.versions {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : TotalCertificate A P S I) {C : Configuration D}
    (execution : CertifiedExecution D I C) : VersionsRALinearizable A P S C :=
  of_canonical cert.laws (cert.canonicalVersions C execution) cert.compatibility cert.historySound

theorem TotalCertificate.versionsV {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : TotalCertificate A P S I) {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) :
    VersionsRALinearizable A P S C := cert.versions (.virtual reach)

theorem TotalCertificate.executions {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : TotalCertificate A P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D I).Execution (initConfig D) trace) :
    ExecutionCorrect A P S trace := by
  have versions := visited (Good := MintCertifiedReach D I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) execution .init
  exact ⟨cert.versions (.ordinary .init),
    fun entry he => cert.versions (.ordinary (versions entry he))⟩

theorem TotalCertificate.executionsV {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : TotalCertificate A P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D I).Execution (initConfig D) trace) :
    ExecutionCorrect A P S trace := by
  have versions := visited (Good := MintCertifiedReachV D (canonicalVirtualMergeBase D) I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) execution .init
  exact ⟨cert.versions (.virtual .init),
    fun entry he => cert.versions (.virtual (versions entry he))⟩

/-- Commuting production VCs retain exact stored replay metadata. No
query-completeness assumption is needed to expose that evidence with identity
abstraction, even when the public query hides part of the state. -/
def rawCommutingScoped
    (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (merge : MergeLaws D) (delta : DeltaLaws D) (peel : CommutingPeelLaw D)
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} (I : Issuance D)
    (history : EventExecutionHistoryAdequacy D (commutingPolicy D.AppOp) S I) :
    ScopedCertificate (Raw.model D) (commutingPolicy D.AppOp) S I where
  laws := Laws.ofUniform (laws_of_all_commute (Raw.model D) commute)
  supportedVersions := by
    intro C execution
    exact CommutingPort.vcSupportedVersions (Raw.model D) commute merge delta peel
      (virtual_reach execution)
  canonicalVersions := by
    intro C execution v s E hv
    obtain ⟨π, hp, _, hf⟩ :=
      (CommutingPort.vcCanonicalConfig (Raw.model D) commute merge delta peel
        (virtual_reach execution)).canonical v s E hv
    refine ⟨π, hp, ?_, hf⟩
    exact hp.1.imp (fun {_ _} _ =>
      CommutingPort.order_empty (Raw.model D) commute C.replayContext E _ _)
  history := CommutingPort.scopedHistory (Raw.model D) commute history

end Sal.MRDTs.Paper1.AbstractMRDT.Guarded.Positive

namespace Sal.MRDTs.Paper1.AbstractMRDT.Guarded.SimplePorts
noncomputable section
open Positive

abbrev gsetCertificate := ofTotalVC SimplePorts.gsetConditions
abbrev gsetVersions {C : Configuration (SimplePorts.Add.D (A := Nat))} := gsetCertificate.versions (C := C)
abbrev gsetVersionsV {C : Configuration (SimplePorts.Add.D (A := Nat))} := gsetCertificate.versionsV (C := C)
abbrev gsetExecutions := gsetCertificate.executions
abbrev gsetExecutionsV := gsetCertificate.executionsV

abbrev addStoreCertificate := ofTotalVC SimplePorts.addStoreConditions
abbrev addStoreVersions {C : Configuration (SimplePorts.Add.D (A := Nat))} := addStoreCertificate.versions (C := C)
abbrev addStoreVersionsV {C : Configuration (SimplePorts.Add.D (A := Nat))} := addStoreCertificate.versionsV (C := C)
abbrev addStoreExecutions := addStoreCertificate.executions
abbrev addStoreExecutionsV := addStoreCertificate.executionsV

abbrev finiteAddCertificate := ofTotalVC SimplePorts.finiteAddConditions
abbrev finiteAddVersions {C : Configuration (SimplePorts.Finite.D (A := Nat))} := finiteAddCertificate.versions (C := C)
abbrev finiteAddVersionsV {C : Configuration (SimplePorts.Finite.D (A := Nat))} := finiteAddCertificate.versionsV (C := C)
abbrev finiteAddExecutions := finiteAddCertificate.executions
abbrev finiteAddExecutionsV := finiteAddCertificate.executionsV

abbrev counterCertificate := ofTotalVC SimplePorts.counterConditions
abbrev counterVersions {C : Configuration (SimplePorts.Delta.D (A := Unit) (fun _ => 1))} := counterCertificate.versions (C := C)
abbrev counterVersionsV {C : Configuration (SimplePorts.Delta.D (A := Unit) (fun _ => 1))} := counterCertificate.versionsV (C := C)
abbrev counterExecutions := counterCertificate.executions
abbrev counterExecutionsV := counterCertificate.executionsV

abbrev iocCertificate := ofTotalVC SimplePorts.iocConditions
abbrev iocVersions {C : Configuration (SimplePorts.Delta.D (A := Instances.FlatCounters.IOCOp) (fun _ => 1))} := iocCertificate.versions (C := C)
abbrev iocVersionsV {C : Configuration (SimplePorts.Delta.D (A := Instances.FlatCounters.IOCOp) (fun _ => 1))} := iocCertificate.versionsV (C := C)
abbrev iocExecutions := iocCertificate.executions
abbrev iocExecutionsV := iocCertificate.executionsV

abbrev pnCertificate := ofTotalVC SimplePorts.pnConditions
abbrev pnVersions {C : Configuration (SimplePorts.Delta.D Instances.FlatCounters.pnDelta)} := pnCertificate.versions (C := C)
abbrev pnVersionsV {C : Configuration (SimplePorts.Delta.D Instances.FlatCounters.pnDelta)} := pnCertificate.versionsV (C := C)
abbrev pnExecutions := pnCertificate.executions
abbrev pnExecutionsV := pnCertificate.executionsV

abbrev booleanSetCertificate := ofTotalVC SimplePorts.booleanSetConditions
abbrev booleanSetVersions {C : Configuration (SimplePorts.Boolean.D (A := Nat))} := booleanSetCertificate.versions (C := C)
abbrev booleanSetVersionsV {C : Configuration (SimplePorts.Boolean.D (A := Nat))} := booleanSetCertificate.versionsV (C := C)
abbrev booleanSetExecutions := booleanSetCertificate.executions
abbrev booleanSetExecutionsV := booleanSetCertificate.executionsV

abbrev booleanMapCertificate := ofTotalVC SimplePorts.booleanMapConditions
abbrev booleanMapVersions {C : Configuration (SimplePorts.Boolean.D (A := Nat × Nat))} := booleanMapCertificate.versions (C := C)
abbrev booleanMapVersionsV {C : Configuration (SimplePorts.Boolean.D (A := Nat × Nat))} := booleanMapCertificate.versionsV (C := C)
abbrev booleanMapExecutions := booleanMapCertificate.executions
abbrev booleanMapExecutionsV := booleanMapCertificate.executionsV

end
end Sal.MRDTs.Paper1.AbstractMRDT.Guarded.SimplePorts

namespace Sal.MRDTs.Paper1.AbstractMRDT.Guarded.ScopedPorts
noncomputable section
open Positive

abbrev boundedCertificate := rawCommutingScoped
  Instances.BoundedCounter.BC_all_comm Instances.BoundedCounter.BC_mergeLaws Instances.BoundedCounter.BC_deltaLaws
  Instances.BoundedCounter.BC_commutingPeelLaw Instances.BoundedCounter.generation GuardedPorts.Bounded.history
abbrev boundedVersions {C : Configuration (Instances.BoundedCounter.BC)} := boundedCertificate.versions (C := C)
abbrev boundedVersionsV {C : Configuration (Instances.BoundedCounter.BC)} := boundedCertificate.versionsV (C := C)
abbrev boundedExecutions := boundedCertificate.executions
abbrev boundedExecutionsV := boundedCertificate.executionsV

abbrev treeCertificate := rawCommutingScoped
  Instances.TreeMove.all_comm Instances.TreeMove.mergeLaws Instances.TreeMove.deltaLaws
  Instances.TreeMove.commutingPeelLaw Instances.TreeMove.generation GuardedPorts.Tree.history
abbrev treeVersions {C : Configuration (Instances.TreeMove.D)} := treeCertificate.versions (C := C)
abbrev treeVersionsV {C : Configuration (Instances.TreeMove.D)} := treeCertificate.versionsV (C := C)
abbrev treeExecutions := treeCertificate.executions
abbrev treeExecutionsV := treeCertificate.executionsV

abbrev sheetCertificate := rawCommutingScoped
  Instances.AegisSheet.all_comm Instances.AegisSheet.mergeLaws Instances.AegisSheet.deltaLaws
  Instances.AegisSheet.commutingPeelLaw Instances.AegisSheet.generation GuardedPorts.Sheet.history
abbrev sheetVersions {C : Configuration (Instances.AegisSheet.D)} := sheetCertificate.versions (C := C)
abbrev sheetVersionsV {C : Configuration (Instances.AegisSheet.D)} := sheetCertificate.versionsV (C := C)
abbrev sheetExecutions := sheetCertificate.executions
abbrev sheetExecutionsV := sheetCertificate.executionsV

abbrev rgaCertificate := rawCommutingScoped
  Instances.RGA.RGAM_all_comm Instances.RGA.RGAM_mergeLaws Instances.RGA.RGAM_deltaLaws
  Instances.RGA.RGAM_commutingPeelLaw Instances.RGA.generation Sal.MRDTs.Paper1.RGA.AbstractPort.history
abbrev rgaVersions {C : Configuration (Instances.RGA.RGAM)} := rgaCertificate.versions (C := C)
abbrev rgaVersionsV {C : Configuration (Instances.RGA.RGAM)} := rgaCertificate.versionsV (C := C)
abbrev rgaExecutions := rgaCertificate.executions
abbrev rgaExecutionsV := rgaCertificate.executionsV

end
end Sal.MRDTs.Paper1.AbstractMRDT.Guarded.ScopedPorts
