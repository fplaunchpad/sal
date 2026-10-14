import Sal.MRDTs.Paper1.SimpleConcretePorts
import Sal.MRDTs.Paper1.IssuedConcretePorts
import Sal.MRDTs.Paper1.RGAConcretePort

/-! Ten positive concrete ports, each retaining its five-VC derivation. -/
namespace Sal.MRDTs.Paper1.ConcreteMRDT.Guarded.SimplePorts
noncomputable section
open Sal.MRDTs.Paper1.ConcreteMRDT

abbrev gsetCertificate := Sal.MRDTs.Paper1.ConcreteMRDT.SimplePorts.gsetConditions.toCertificate
abbrev gsetVersions {C : Configuration (SimplePorts.Add.D (A := Nat))} := gsetCertificate.versions (C := C)
abbrev gsetVersionsV {C : Configuration (SimplePorts.Add.D (A := Nat))} := gsetCertificate.versionsV (C := C)
abbrev gsetExecutions := gsetCertificate.executions
abbrev gsetExecutionsV := gsetCertificate.executionsV


abbrev finiteAddCertificate := Sal.MRDTs.Paper1.ConcreteMRDT.SimplePorts.finiteAddConditions.toCertificate
abbrev finiteAddVersions {C : Configuration (SimplePorts.Finite.D (A := Nat))} := finiteAddCertificate.versions (C := C)
abbrev finiteAddVersionsV {C : Configuration (SimplePorts.Finite.D (A := Nat))} := finiteAddCertificate.versionsV (C := C)
abbrev finiteAddExecutions := finiteAddCertificate.executions
abbrev finiteAddExecutionsV := finiteAddCertificate.executionsV

abbrev counterCertificate := Sal.MRDTs.Paper1.ConcreteMRDT.SimplePorts.counterConditions.toCertificate
abbrev counterVersions {C : Configuration (SimplePorts.Delta.D Instances.FlatCounters.counterDelta)} := counterCertificate.versions (C := C)
abbrev counterVersionsV {C : Configuration (SimplePorts.Delta.D Instances.FlatCounters.counterDelta)} := counterCertificate.versionsV (C := C)
abbrev counterExecutions := counterCertificate.executions
abbrev counterExecutionsV := counterCertificate.executionsV

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
