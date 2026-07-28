import Sal.MRDTs.PN_Counter.PN_Counter_MRDT

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 400000
open Classical

/-! # PN_Counter (MRDT): read-side projection

The 24 VCs prove the integer state converges under three-way
merge `a + b − l`. The read is the integer state itself; `Inc`
raises it by 1, `Dec` lowers it by 1. -/

/-- The counter's value: the integer state itself. -/
def value (s : concrete_st) : Int := s

theorem value_convergent (s₁ s₂ : concrete_st) :
    eq s₁ s₂ → value s₁ = value s₂ := id

/-- **Inc raises the value by 1.** -/
theorem value_after_inc (s : concrete_st) (ts rid : ℕ) :
    value (do_ s (ts, rid, app_op_t.Inc)) = value s + 1 := rfl

/-- **Dec lowers the value by 1.** -/
theorem value_after_dec (s : concrete_st) (ts rid : ℕ) :
    value (do_ s (ts, rid, app_op_t.Dec)) = value s - 1 := rfl

/-- **Merge gives `a + b − l` (the read of the merged state). -/
theorem value_of_merge (l a b : concrete_st) :
    value (merge l a b) = value a + value b - value l := rfl
