import Sal.MRDTs.Paper1.Automation.TransferSimple
import Sal.MRDTs.Instances.TreeMove
import Sal.MRDTs.Instances.AegisSheet

/-! The TreeMove five-VC route. The actual guarded
issuers select histories but their representation effectors commute. Empty
metadata expansion therefore applies directly, without an issuer invariant. -/
namespace Sal.MRDTs.Paper1.Automation.TransferGuardedCommuting
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT



namespace Tree
open Instances.TreeMove

theorem kernels : TransferSimple.EmptyPastKernels D := by
  constructor <;> mrdt_representation [D]

end Tree

end Sal.MRDTs.Paper1.Automation.TransferGuardedCommuting
