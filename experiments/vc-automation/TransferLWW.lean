import TransferSimple
import Sal.MRDTs.Paper1.GuardedLWWPort

/-! Instantiate the existing empty-policy paper1 LWW port. The timestamp
maximum implementation and its representation are unchanged. -/
namespace NeemExpansion.TransferLWW
open Sal.MRDTs Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open Instances.LWWRegister

theorem kernels : TransferSimple.EmptyPastKernels D := by
  constructor <;> intros <;> simp only [D, update]
  all_goals simp [max_assoc, max_left_comm, max_comm]

theorem expanded_vcs : Raw.MergeVCs LWW.GuardedPort.policy
    (CommutingPort.representation D) (CommutingPort.scheme all_comm) :=
  TransferSimple.assemble D all_comm kernels

#print axioms expanded_vcs
end NeemExpansion.TransferLWW
