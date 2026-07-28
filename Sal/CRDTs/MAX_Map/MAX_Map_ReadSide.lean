import Std.Tactic.BVDecide
import Sal.Interfaces.Map_Extended
import Sal.Tactic.Sal
import Sal.CRDTs.MAX_Map.MAX_Map_CRDT
import Mathlib

set_option linter.mathlibStandardSet false

open scoped Classical
set_option maxHeartbeats 400000
set_option relaxedAutoImplicit false
set_option autoImplicit false
open Classical

/-! # MAX_Map (CRDT): read-side projection

The 24 VCs prove the per-key map converges under per-key max. The
read is `lookup k`, the value at key `k` (zero-default for unset
keys). `Write k v` raises (or keeps) that value via `max`. -/

def lookup (s : concrete_st) (k : ℕ) : ℕ := mysel s k

theorem lookup_convergent (s₁ s₂ : concrete_st) (k : ℕ) :
    eq s₁ s₂ → lookup s₁ k = lookup s₂ k := by
  intro h_eq
  unfold lookup
  exact (h_eq k).2

/-- **Write at key k max-bumps the value at k.** -/
theorem lookup_after_write (s : concrete_st) (k v ts rid : ℕ) :
    lookup (do_ s (ts, rid, app_op_t.Write k v)) k =
      max (lookup s k) v := by
  simp [lookup, do_, mysel]

/-- **Write at key k' does not affect key k.** -/
theorem lookup_unchanged_at_other_key
    (s : concrete_st) (k k' v ts rid : ℕ) (h_ne : k ≠ k') :
    lookup (do_ s (ts, rid, app_op_t.Write k' v)) k = lookup s k := by
  simp [lookup, do_, mysel, h_ne, Ne.symm h_ne]
