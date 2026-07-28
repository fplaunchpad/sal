import Sal.Interfaces.Map_Extended
import Sal.MRDTs.Grow_Only_Map.Grow_Only_Map_MRDT
import Mathlib

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 400000
set_option relaxedAutoImplicit false
set_option autoImplicit false
open Classical

/-! # Grow_Only_Map (MRDT): read-side projection

The 24 VCs prove the per-key set-of-values map converges under
per-key three-way union. The read is `lookup k v`: is `v` in the
set at key `k`? -/

def lookup (s : concrete_st) (k v : ℕ) : Bool := mem v (mysel s k)

theorem lookup_convergent (s₁ s₂ : concrete_st) (k v : ℕ) :
    eq s₁ s₂ → lookup s₁ k v = lookup s₂ k v := by
  intro h_eq
  unfold lookup
  rw [(h_eq k).2]

/-- **Put k v** makes `v` live at `k`. -/
theorem lookup_after_put (s : concrete_st) (ts rid k v : ℕ) :
    lookup (do_ s (ts, rid, (k, v))) k v = true := by
  simp [lookup, do_, mysel, mem, add]

/-- A `Put k' v'` at a different key does not affect lookup at `k`. -/
theorem lookup_unchanged_at_other_key
    (s : concrete_st) (ts rid k k' v v' : ℕ) (h_ne : k ≠ k') :
    lookup (do_ s (ts, rid, (k', v'))) k v = lookup s k v := by
  simp [lookup, do_, mysel, h_ne, Ne.symm h_ne]
