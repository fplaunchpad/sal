import Sal.MRDTs.Paper1.Automation.TransferSimple
import Sal.MRDTs.Instances.BoundedCounter
import Sal.MRDTs.Instances.TreeMove
import Sal.MRDTs.Instances.AegisSheet

/-! Unchanged bounded-counter and TreeMove five-VC routes. The actual guarded
issuers select histories but their representation effectors commute. Empty
metadata expansion therefore applies directly, without an issuer invariant. -/
namespace Sal.MRDTs.Paper1.Automation.TransferGuardedCommuting
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT

namespace Bounded
open Instances.BoundedCounter

theorem kernels : TransferSimple.EmptyPastKernels BC := by
  constructor <;> mrdt_representation [BC,bcMerge,bcUpdate,bcBump]

end Bounded

namespace Tree
open Instances.TreeMove

theorem kernels : TransferSimple.EmptyPastKernels D := by
  constructor <;> mrdt_representation [D]

end Tree

end Sal.MRDTs.Paper1.Automation.TransferGuardedCommuting
