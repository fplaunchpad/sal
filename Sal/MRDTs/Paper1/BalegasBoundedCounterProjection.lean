import Sal.MRDTs.Instances.BalegasBoundedCounter

namespace Sal.MRDTs.Instances.BalegasBoundedCounter
open Foundation

theorem localRights_increment (n : Nat) (s : State) (ts rep amount r : Nat) :
    localRights n (update s (ts,rep,.increment amount)) r =
      localRights n s r + (if r = rep then (amount : Int) else 0) := by
  have hz : ∀ j ∈ (Finset.range n).erase r, ¬ (j = rep ∧ r = rep) := by
    intro j hj; have := (Finset.mem_erase.mp hj).1; grind
  have hz' : ∀ j ∈ (Finset.range n).erase r, ¬ (r = rep ∧ j = rep) := by
    intro j hj; have := (Finset.mem_erase.mp hj).1; grind
  simp only [localRights, update, Op.op, bumpMatrix, Nat.cast_add]
  simp only [Finset.sum_add_distrib]
  have h1 : (∑ j ∈ (Finset.range n).erase r,
      ((if j = rep ∧ r = rep then amount else 0 : Nat) : Int)) = 0 := by
    apply Finset.sum_eq_zero; intro j hj; simp [hz j hj]
  have h2 : (∑ j ∈ (Finset.range n).erase r,
      ((if r = rep ∧ j = rep then amount else 0 : Nat) : Int)) = 0 := by
    apply Finset.sum_eq_zero; intro j hj; simp [hz' j hj]
  rw [h1,h2]
  split_ifs <;> simp_all <;> omega

theorem localRights_decrement (n : Nat) (s : State) (ts rep amount r : Nat) :
    localRights n (update s (ts,rep,.decrement amount)) r =
      localRights n s r - (if r = rep then (amount : Int) else 0) := by
  simp only [localRights, update, Op.op, bump, Nat.cast_add]
  split_ifs <;> simp_all <;> omega

theorem localRights_transfer (n : Nat) (s : State) (ts rep amount target r : Nat)
    (hr : rep < n) (ht : target < n) (hne : target ≠ rep) :
    localRights n (update s (ts,rep,.transfer amount target)) r =
      localRights n s r + (if r = target then (amount : Int) else 0) -
        (if r = rep then (amount : Int) else 0) := by
  have hz : ¬ (r = rep ∧ r = target) := by grind
  simp only [localRights, update, Op.op, bumpMatrix, Nat.cast_add,
    Finset.sum_add_distrib, if_neg hz, Nat.cast_zero, add_zero]
  by_cases hrt : r = target
  · subst r
    simp [hne, hr, Finset.mem_erase, Finset.mem_range]
    omega
  · by_cases hrr : r = rep
    · subst r
      simp [hne, Ne.symm hne, ht, Finset.mem_erase, Finset.mem_range]
      omega
    · simp [hrt, hrr]

end Sal.MRDTs.Instances.BalegasBoundedCounter
