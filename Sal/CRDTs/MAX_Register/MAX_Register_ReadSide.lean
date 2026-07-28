import Sal.CRDTs.MAX_Register.MAX_Register_CRDT

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 400000
open Classical

/-! # MAX_Register (CRDT): read-side projection

The 24 VCs prove the natural-number state converges under pointwise
max. The read is the state itself; `Write v` raises (or keeps) the
value via `max`. -/

def value (s : concrete_st) : ℕ := s

theorem value_convergent (s₁ s₂ : concrete_st) :
    eq s₁ s₂ → value s₁ = value s₂ := id

/-- **Write max-bumps the value.** -/
theorem value_after_write (s : concrete_st) (v ts rid : ℕ) :
    value (do_ s (ts, rid, app_op_t.Write v)) = max (value s) v := rfl

/-- **Merge gives the pointwise max of the two states.** -/
theorem value_of_merge (a b : concrete_st) :
    value (merge a b) = max (value a) (value b) := rfl
