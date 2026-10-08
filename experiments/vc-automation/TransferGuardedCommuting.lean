import TransferSimple
import Sal.MRDTs.Paper1.IssuedConcretePorts

/-! Unchanged bounded-counter and TreeMove five-VC routes. The actual guarded
issuers select histories but their representation effectors commute. Empty
metadata expansion therefore applies directly, without an issuer invariant. -/
namespace NeemExpansion.TransferGuardedCommuting
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT

namespace Bounded
open Instances.BoundedCounter

theorem kernels : TransferSimple.EmptyPastKernels BC := by
  constructor
  · intro l a b
    apply Prod.ext <;> funext k <;> simp only [BC,bcMerge] <;> omega
  · intro s
    apply Prod.ext <;> funext k <;> simp only [BC,bcMerge] <;> omega
  · intro s e
    rcases e with ⟨ts,r,op⟩
    cases op <;> apply Prod.ext <;> funext k <;> simp only [BC,bcMerge,bcUpdate,bcBump]
    all_goals omega
  · intro l B t b e
    rcases e with ⟨ts,r,op⟩
    cases op <;> apply Prod.ext <;> funext k <;> simp only [BC,bcMerge,bcUpdate,bcBump]
    all_goals omega
  · intro B t₀ t₁ t₂ e
    rcases e with ⟨ts,r,op⟩
    cases op <;> apply Prod.ext <;> funext k <;> simp only [BC,bcMerge,bcUpdate,bcBump]
    all_goals omega

/-- Precisely the Raw.MergeVCs bundled by existing GuardedPorts.Bounded.conditions. -/
theorem expanded_vcs : Raw.MergeVCs (commutingPolicy BC.AppOp)
    (CommutingPort.representation BC) (CommutingPort.scheme BC_all_comm) :=
  TransferSimple.assemble BC BC_all_comm kernels
end Bounded

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

#print axioms Bounded.expanded_vcs
#print axioms Tree.expanded_vcs
end NeemExpansion.TransferGuardedCommuting
