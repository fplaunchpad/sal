import Sal.MRDTs.Paper1.Automation.TransferSimple
import Sal.MRDTs.Instances.BoundedCounter
import Sal.MRDTs.Instances.TreeMove
import Sal.MRDTs.Instances.AegisSheet

/-! The unchanged AegisSheet five-VC port. The log carrier inserts each event
and merges by union. Its issuer's origin-legality checks are retained by the
existing port; the five raw equations need no stronger state assumptions. -/
namespace Sal.MRDTs.Paper1.Automation.TransferAegisSheet
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open Sal.MRDTs.Instances.AegisSheet

/-- Finite equations checked directly against the executable carrier. -/
theorem kernels : TransferSimple.EmptyPastKernels D := by
  constructor <;> mrdt_representation [D]

end Sal.MRDTs.Paper1.Automation.TransferAegisSheet
