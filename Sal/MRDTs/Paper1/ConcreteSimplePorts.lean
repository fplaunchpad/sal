import Sal.MRDTs.Paper1.SimpleConcretePorts
import Sal.MRDTs.Paper1.IssuedConcretePorts
import Sal.MRDTs.Paper1.RGAConcretePort

/-! Twelve positive concrete ports, each retaining its five-VC derivation. -/
namespace Sal.MRDTs.Paper1.ConcreteMRDT.Guarded.SimplePorts
noncomputable section
open Sal.MRDTs.Paper1.ConcreteMRDT

abbrev gsetCertificate := Sal.MRDTs.Paper1.ConcreteMRDT.SimplePorts.gsetConditions.toCertificate
abbrev gsetVersions {C : Configuration (SimplePorts.Add.D (A := Nat))} := gsetCertificate.versions (C := C)
abbrev gsetVersionsV {C : Configuration (SimplePorts.Add.D (A := Nat))} := gsetCertificate.versionsV (C := C)
abbrev gsetExecutions := gsetCertificate.executions
abbrev gsetExecutionsV := gsetCertificate.executionsV

abbrev addStoreCertificate := Sal.MRDTs.Paper1.ConcreteMRDT.SimplePorts.addStoreConditions.toCertificate
abbrev addStoreVersions {C : Configuration (SimplePorts.Add.D (A := Nat))} := addStoreCertificate.versions (C := C)
abbrev addStoreVersionsV {C : Configuration (SimplePorts.Add.D (A := Nat))} := addStoreCertificate.versionsV (C := C)
abbrev addStoreExecutions := addStoreCertificate.executions
abbrev addStoreExecutionsV := addStoreCertificate.executionsV

abbrev finiteAddCertificate := Sal.MRDTs.Paper1.ConcreteMRDT.SimplePorts.finiteAddConditions.toCertificate
abbrev finiteAddVersions {C : Configuration (SimplePorts.Finite.D (A := Nat))} := finiteAddCertificate.versions (C := C)
abbrev finiteAddVersionsV {C : Configuration (SimplePorts.Finite.D (A := Nat))} := finiteAddCertificate.versionsV (C := C)
abbrev finiteAddExecutions := finiteAddCertificate.executions
abbrev finiteAddExecutionsV := finiteAddCertificate.executionsV

abbrev counterCertificate := Sal.MRDTs.Paper1.ConcreteMRDT.SimplePorts.counterConditions.toCertificate
abbrev counterVersions {C : Configuration (SimplePorts.Delta.D (A := Unit) (fun _ => 1))} := counterCertificate.versions (C := C)
abbrev counterVersionsV {C : Configuration (SimplePorts.Delta.D (A := Unit) (fun _ => 1))} := counterCertificate.versionsV (C := C)
abbrev counterExecutions := counterCertificate.executions
abbrev counterExecutionsV := counterCertificate.executionsV

abbrev iocCertificate := Sal.MRDTs.Paper1.ConcreteMRDT.SimplePorts.iocConditions.toCertificate
abbrev iocVersions {C : Configuration (SimplePorts.Delta.D (A := Instances.FlatCounters.IOCOp) (fun _ => 1))} := iocCertificate.versions (C := C)
abbrev iocVersionsV {C : Configuration (SimplePorts.Delta.D (A := Instances.FlatCounters.IOCOp) (fun _ => 1))} := iocCertificate.versionsV (C := C)
abbrev iocExecutions := iocCertificate.executions
abbrev iocExecutionsV := iocCertificate.executionsV

abbrev pnCertificate := Sal.MRDTs.Paper1.ConcreteMRDT.SimplePorts.pnConditions.toCertificate
abbrev pnVersions {C : Configuration (SimplePorts.Delta.D Instances.FlatCounters.pnDelta)} := pnCertificate.versions (C := C)
abbrev pnVersionsV {C : Configuration (SimplePorts.Delta.D Instances.FlatCounters.pnDelta)} := pnCertificate.versionsV (C := C)
abbrev pnExecutions := pnCertificate.executions
abbrev pnExecutionsV := pnCertificate.executionsV

abbrev booleanSetCertificate := Sal.MRDTs.Paper1.ConcreteMRDT.SimplePorts.booleanSetConditions.toCertificate
abbrev booleanSetVersions {C : Configuration (SimplePorts.Boolean.D (A := Nat))} := booleanSetCertificate.versions (C := C)
abbrev booleanSetVersionsV {C : Configuration (SimplePorts.Boolean.D (A := Nat))} := booleanSetCertificate.versionsV (C := C)
abbrev booleanSetExecutions := booleanSetCertificate.executions
abbrev booleanSetExecutionsV := booleanSetCertificate.executionsV

abbrev booleanMapCertificate := Sal.MRDTs.Paper1.ConcreteMRDT.SimplePorts.booleanMapConditions.toCertificate
abbrev booleanMapVersions {C : Configuration (SimplePorts.Boolean.D (A := Nat × Nat))} := booleanMapCertificate.versions (C := C)
abbrev booleanMapVersionsV {C : Configuration (SimplePorts.Boolean.D (A := Nat × Nat))} := booleanMapCertificate.versionsV (C := C)
abbrev booleanMapExecutions := booleanMapCertificate.executions
abbrev booleanMapExecutionsV := booleanMapCertificate.executionsV

end
end Sal.MRDTs.Paper1.ConcreteMRDT.Guarded.SimplePorts

namespace Sal.MRDTs.Paper1.ConcreteMRDT.Guarded.ScopedPorts
noncomputable section
open Sal.MRDTs.Paper1.ConcreteMRDT

abbrev boundedCertificate := GuardedPorts.Bounded.conditions.toCertificate
abbrev boundedVersions {C : Configuration (Instances.BoundedCounter.BC)} := boundedCertificate.versions (C := C)
abbrev boundedVersionsV {C : Configuration (Instances.BoundedCounter.BC)} := boundedCertificate.versionsV (C := C)
abbrev boundedExecutions := boundedCertificate.executions
abbrev boundedExecutionsV := boundedCertificate.executionsV

abbrev treeCertificate := GuardedPorts.Tree.conditions.toCertificate
abbrev treeVersions {C : Configuration (Instances.TreeMove.D)} := treeCertificate.versions (C := C)
abbrev treeVersionsV {C : Configuration (Instances.TreeMove.D)} := treeCertificate.versionsV (C := C)
abbrev treeExecutions := treeCertificate.executions
abbrev treeExecutionsV := treeCertificate.executionsV

abbrev sheetCertificate := GuardedPorts.Sheet.conditions.toCertificate
abbrev sheetVersions {C : Configuration (Instances.AegisSheet.D)} := sheetCertificate.versions (C := C)
abbrev sheetVersionsV {C : Configuration (Instances.AegisSheet.D)} := sheetCertificate.versionsV (C := C)
abbrev sheetExecutions := sheetCertificate.executions
abbrev sheetExecutionsV := sheetCertificate.executionsV

abbrev rgaCertificate := Sal.MRDTs.Paper1.RGA.ConcretePort.conditions.toCertificate
abbrev rgaVersions {C : Configuration (Instances.RGA.RGAM)} := rgaCertificate.versions (C := C)
abbrev rgaVersionsV {C : Configuration (Instances.RGA.RGAM)} := rgaCertificate.versionsV (C := C)
abbrev rgaExecutions := rgaCertificate.executions
abbrev rgaExecutionsV := rgaCertificate.executionsV

end
end Sal.MRDTs.Paper1.ConcreteMRDT.Guarded.ScopedPorts
