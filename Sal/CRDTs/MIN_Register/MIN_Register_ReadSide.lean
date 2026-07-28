import Sal.CRDTs.MIN_Register.MIN_Register_CRDT

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 400000
open Classical

/-! # MIN_Register (CRDT): read-side projection

The 24 VCs prove the natural-number state converges under pointwise
min. The read is the state itself; `Write v` lowers (or keeps) the
value via `min`. Note: with `init_st = 0` on `ℕ`, the state is
absorbing at 0; the read-side theorems below state the operational
property symbolically without assuming a particular initial value. -/

def value (s : concrete_st) : ℕ := s

theorem value_convergent (s₁ s₂ : concrete_st) :
    eq s₁ s₂ → value s₁ = value s₂ := id

/-- **Write min-collapses the value.** -/
theorem value_after_write (s : concrete_st) (v ts rid : ℕ) :
    value (do_ s (ts, rid, app_op_t.Write v)) = min (value s) v := rfl

/-- **Merge gives the pointwise min of the two states.** -/
theorem value_of_merge (a b : concrete_st) :
    value (merge a b) = min (value a) (value b) := rfl
