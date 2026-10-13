import Sal.MRDTs.Paper1.Automation.TransferSimple
import Sal.MRDTs.Instances.LWWRegister

/-! Instantiate the existing empty-policy paper1 LWW port. The timestamp
maximum implementation and its representation are unchanged. -/
namespace Sal.MRDTs.Paper1.Automation.TransferLWW
open Sal.MRDTs Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open Instances.LWWRegister

theorem kernels : TransferSimple.EmptyPastKernels D := by
  constructor <;> intros <;> simp only [D, update]
  all_goals simp [max_assoc, max_left_comm, max_comm]


end Sal.MRDTs.Paper1.Automation.TransferLWW
