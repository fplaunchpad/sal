import TransferSimple
import Sal.MRDTs.Paper1.IssuedConcretePorts

/-! The TreeMove five-VC route. The actual guarded
issuers select histories but their representation effectors commute. Empty
metadata expansion therefore applies directly, without an issuer invariant. -/
namespace NeemExpansion.TransferGuardedCommuting
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT



namespace Tree
open Instances.TreeMove

theorem kernels : TransferSimple.EmptyPastKernels D := by
  constructor
  · intros; apply Finset.ext; intro p; simp [D,or_comm]
  · intros; apply Finset.ext; intro p; simp [D]
  · intros; apply Finset.ext; intro p; simp [D]
  · intros; apply Finset.ext; intro p; simp [D,or_left_comm,or_comm]
  · intros; apply Finset.ext; intro p; simp [D,or_left_comm,or_comm]

/-- Precisely the Raw.MergeVCs bundled by existing GuardedPorts.Tree.conditions. -/
theorem expanded_vcs : Raw.MergeVCs (commutingPolicy D.AppOp)
    (CommutingPort.representation D) (CommutingPort.scheme all_comm) :=
  TransferSimple.assemble D all_comm kernels
end Tree

#print axioms Tree.expanded_vcs
end NeemExpansion.TransferGuardedCommuting
