import Sal.MRDTs.Paper1.SplitSoundness
import Sal.MRDTs.Paper1.ConcreteSimplePorts
import Sal.MRDTs.Paper1.GuardedLWWPort
import Sal.MRDTs.Paper1.GuardedRawExactExecution
import Sal.MRDTs.Paper1.GuardedRawEfficientCertificate
import Sal.MRDTs.Paper1.CertifiedMVRCertificate
import Sal.MRDTs.Paper1.CertifiedRGAInvariantCertificate
import Sal.MRDTs.Paper1.CertifiedSidedInvariantCertificate
import Sal.MRDTs.Paper1.CertifiedPeritextInvariantCertificate
import Sal.MRDTs.Paper1.CertifiedRGACoreCertificate
import Sal.MRDTs.Paper1.CertifiedRGARichCertificate
import Sal.MRDTs.Paper1.AnchoredQueueCertificate
import Sal.MRDTs.Paper1.SelfCommutationInstancesCertified

/-! Exactly the 22 automation cases after consolidating the grow-only set
with the generic AddStore implementation. Raw cases use split five-VC/certificate execution constructors;
scoped cases expose the split policy in the existing actual execution
certificate. FugueMax remains scoped algebraic replay, with no RA claim. -/
namespace Sal.MRDTs.Paper1.SplitCertificates
open Foundation SplitPolicy
noncomputable section
abbrev gset := Concrete.VCConditions.ofExisting ConcreteMRDT.SimplePorts.gsetConditions
abbrev gsetExecutions := gset.executions
abbrev gsetExecutionsV := gset.executionsV
abbrev finiteAdd := Concrete.VCConditions.ofExisting ConcreteMRDT.SimplePorts.finiteAddConditions
abbrev finiteAddExecutions := finiteAdd.executions
abbrev finiteAddExecutionsV := finiteAdd.executionsV
abbrev counter := Concrete.VCConditions.ofExisting ConcreteMRDT.SimplePorts.counterConditions
abbrev counterExecutions := counter.executions
abbrev counterExecutionsV := counter.executionsV
abbrev ioc := Concrete.VCConditions.ofExisting ConcreteMRDT.SimplePorts.iocConditions
abbrev iocExecutions := ioc.executions
abbrev iocExecutionsV := ioc.executionsV
abbrev pn := Concrete.VCConditions.ofExisting ConcreteMRDT.SimplePorts.pnConditions
abbrev pnExecutions := pn.executions
abbrev pnExecutionsV := pn.executionsV
abbrev booleanSet := Concrete.VCConditions.ofExisting ConcreteMRDT.SimplePorts.booleanSetConditions
abbrev booleanSetExecutions := booleanSet.executions
abbrev booleanSetExecutionsV := booleanSet.executionsV
abbrev booleanMap := Concrete.VCConditions.ofExisting ConcreteMRDT.SimplePorts.booleanMapConditions
abbrev booleanMapExecutions := booleanMap.executions
abbrev booleanMapExecutionsV := booleanMap.executionsV
abbrev bounded := Concrete.ScopedVCConditions.ofExisting ConcreteMRDT.GuardedPorts.Bounded.conditions
abbrev boundedExecutions := bounded.executions
abbrev boundedExecutionsV := bounded.executionsV
abbrev tree := Concrete.ScopedVCConditions.ofExisting ConcreteMRDT.GuardedPorts.Tree.conditions
abbrev treeExecutions := tree.executions
abbrev treeExecutionsV := tree.executionsV
abbrev aegis := Concrete.ScopedVCConditions.ofExisting ConcreteMRDT.GuardedPorts.Sheet.conditions
abbrev aegisExecutions := aegis.executions
abbrev aegisExecutionsV := aegis.executionsV
abbrev rga := Concrete.ScopedVCConditions.ofExisting RGA.ConcretePort.conditions
abbrev rgaExecutions := rga.executions
abbrev rgaExecutionsV := rga.executionsV
abbrev lww := Concrete.ScopedCertificate.ofExisting (LWW.GuardedPort.certificate)
abbrev lwwExecutions := lww.executions
abbrev lwwExecutionsV := lww.executionsV
abbrev ordinaryORSet := Concrete.ScopedCertificate.ofExisting (ORSet.RawExecution.certificate (α := Nat))
abbrev ordinaryORSetExecutions := ordinaryORSet.executions
abbrev ordinaryORSetExecutionsV := ordinaryORSet.executionsV
abbrev efficientORSet := Concrete.ScopedCertificate.ofExisting (EfficientORSet.RawCertificate.certificate (α := Nat))
abbrev efficientORSetExecutions := efficientORSet.executions
abbrev efficientORSetExecutionsV := efficientORSet.executionsV
abbrev mvr := @CertifiedQueueMVR.MVR.Certificate.executions
abbrev embedded := @CertifiedRGAInvariantCertificate.executions
abbrev sided := @CertifiedSidedInvariantCertificate.executions
abbrev peritext := @CertifiedPeritextInvariantCertificate.executions
abbrev core := @CertifiedRGACoreCertificate.executions
abbrev rich := @CertifiedRGARichCertificate.executions
abbrev anchoredQueue := @AnchoredQueue.History.certificate
/-- FugueMax retains both its split replay certificate and the representation
proved by the five VCs. No history-language or RA verdict is asserted. -/
theorem fugue (Γ : Sal.EmbedRGA.OrderedPrefixCode)
    {C : Configuration (Instances.SidedEmbedRGA.FugueMax.datatype Γ)}
    (execution : CertifiedExecution (Instances.SidedEmbedRGA.FugueMax.datatype Γ)
      (Instances.SidedEmbedRGA.FugueMax.generation Γ) C)
    {v s H} (stored : C.ver v = some (s,H)) :
    Invariant.RestrictedLaws (CertifiedFugueInvariantReplay.scope Γ C H)
      (CertifiedFugueInvariant.Valid Γ C.replayContext)
      (commutingPolicy (Instances.SidedEmbedRGA.FugueMax.datatype Γ).AppOp) ∧
    CertifiedFugueVCReplay.representation Γ C.replayContext H s :=
  ⟨SelfCommutationInstances.fugue_split Γ execution stored,
    CertifiedFugueVCExecution.representedVersions Γ execution stored⟩

end
end Sal.MRDTs.Paper1.SplitCertificates
