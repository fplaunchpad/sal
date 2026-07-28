import Sal.CRDTs.Increment_Only_Counter.Increment_Only_Counter_CRDT
import Sal.CRDTs.Increment_Only_Counter.Increment_Only_Counter_ReadSide

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open Classical

/-! # Increment_Only_Counter (CRDT): SPOTs -/

namespace Increment_Only_Counter_SPOT

example : value_at (do_ init_st (1, 0, app_op_t.Incr)) 0 = 1 :=
  value_at_after_incr init_st 1 0

example :
    value_at
      (do_ (do_ init_st (1, 0, app_op_t.Incr)) (2, 0, app_op_t.Incr))
      0 = 2 := by
  rw [value_at_after_incr, value_at_after_incr]; simp [value_at, init_st, mysel]

example :
    let σ_a := do_ init_st (1, 0, app_op_t.Incr)
    let σ_b := do_ init_st (2, 1, app_op_t.Incr)
    let σ := merge σ_a σ_b
    value_at σ 0 = 1 ∧ value_at σ 1 = 1 := by
  refine ⟨?_, ?_⟩ <;> simp +decide [value_at, mysel]

end Increment_Only_Counter_SPOT
