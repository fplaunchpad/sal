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

end Tree

end Sal.MRDTs.Paper1.Automation.TransferGuardedCommuting
