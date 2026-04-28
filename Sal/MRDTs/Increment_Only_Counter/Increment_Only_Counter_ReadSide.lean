import Sal.MRDTs.Increment_Only_Counter.Increment_Only_Counter_MRDT

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 400000
open Classical

/-! # Increment_Only_Counter (MRDT) — read-side projection

The 24 VCs prove the integer state converges under three-way
merge `a + b − l`. The read is the integer state itself; `Incr`
raises it by 1. -/

def value (s : concrete_st) : Int := s

theorem value_convergent (s₁ s₂ : concrete_st) :
    eq s₁ s₂ → value s₁ = value s₂ := id

/-- **Incr raises the value by 1.** -/
theorem value_after_incr (s : concrete_st) (ts rid : ℕ) :
    value (do_ s (ts, rid, app_op_t.Incr)) = value s + 1 := rfl

/-- **Merge gives `a + b − l` on the values.** -/
theorem value_of_merge (l a b : concrete_st) :
    value (merge l a b) = value a + value b - value l := rfl
