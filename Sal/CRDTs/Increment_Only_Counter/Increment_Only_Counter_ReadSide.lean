import Std.Tactic.BVDecide
import Sal.Interfaces.Map_Extended
import Sal.Tactic.Sal
import Sal.CRDTs.Increment_Only_Counter.Increment_Only_Counter_CRDT
import Mathlib

set_option linter.mathlibStandardSet false

open scoped Classical
set_option maxHeartbeats 400000
set_option relaxedAutoImplicit false
set_option autoImplicit false
open Classical

/-! # Increment_Only_Counter (CRDT) — read-side projection

The 24 VCs prove that the per-replica map converges under per-slot
max. The headline read is **per-replica increment count**: at
replica `rid`, the value is `state[rid]`, and `Incr` at that
replica raises it by 1. -/

/-- Per-replica counter value. -/
def value_at (s : concrete_st) (rid : ℕ) : Int := mysel s rid

theorem value_at_convergent (s₁ s₂ : concrete_st) (rid : ℕ) :
    eq s₁ s₂ → value_at s₁ rid = value_at s₂ rid := by
  intro h_eq
  unfold value_at
  exact (h_eq rid).2

/-- **Incr raises the replica's value by 1.** -/
theorem value_at_after_incr (s : concrete_st) (ts rid : ℕ) :
    value_at (do_ s (ts, rid, app_op_t.Incr)) rid = value_at s rid + 1 := by
  simp [value_at, do_, mysel]

/-- Incr on `rid'` does not affect `rid`'s value when `rid ≠ rid'`. -/
theorem value_at_unchanged_by_other_incr
    (s : concrete_st) (ts rid rid' : ℕ) (h_ne : rid ≠ rid') :
    value_at (do_ s (ts, rid', app_op_t.Incr)) rid = value_at s rid := by
  simp [value_at, do_, mysel, h_ne]
