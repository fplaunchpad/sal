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
  constructor
  · intros; apply Finset.ext; intro x; simp [D,or_comm]
  · intros; apply Finset.ext; intro x; simp [D]
  · intros; apply Finset.ext; intro x; simp [D]
  · intros; apply Finset.ext; intro x; simp [D,or_left_comm,or_comm]
  · intros; apply Finset.ext; intro x; simp [D,or_left_comm,or_comm]

end Sal.MRDTs.Paper1.Automation.TransferAegisSheet
