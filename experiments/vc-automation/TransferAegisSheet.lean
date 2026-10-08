import TransferSimple
import Sal.MRDTs.Paper1.IssuedConcretePorts

/-! The unchanged AegisSheet five-VC port. The log carrier inserts each event
and merges by union. Its issuer's origin-legality checks are retained by the
existing port; the five raw equations need no stronger state assumptions. -/
namespace NeemExpansion.TransferAegisSheet
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

/-- Exactly the existing commuting port: policy, replay representation and
metadata dependencies are unchanged. Empty-past replay is eliminated by the
generic assembler rather than a datatype history invariant. -/
theorem expanded_vcs : Raw.MergeVCs (commutingPolicy D.AppOp)
    (CommutingPort.representation D) (CommutingPort.scheme all_comm) :=
  TransferSimple.assemble D all_comm kernels

#print axioms expanded_vcs
end NeemExpansion.TransferAegisSheet
