import Sal.CRDTs.PN_Counter.PN_Counter_CRDT
import Sal.CRDTs.PN_Counter.PN_Counter_ReadSide

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open Classical

/-! # PN_Counter (CRDT) — SPOTs -/

namespace PN_Counter_SPOT

/-- **SPOT 1 — Inc raises value at the same replica.** -/
example : value_at (do_ init_st (1, 0, app_op_t.Inc)) 0 = 1 :=
  value_at_after_inc init_st 1 0

/-- **SPOT 2 — Inc then Dec on same replica nets to zero.** -/
example :
    value_at (do_ (do_ init_st (1, 0, app_op_t.Inc)) (2, 0, app_op_t.Dec)) 0 = 0 := by
  rw [value_at_after_dec, value_at_after_inc]
  rfl

/-- **SPOT 3 — Concurrent Inc on different replicas: each replica's
local value is 1.** -/
example :
    let σ_a := do_ init_st (1, 0, app_op_t.Inc)
    let σ_b := do_ init_st (2, 1, app_op_t.Inc)
    let σ := merge σ_a σ_b
    value_at σ 0 = 1 ∧ value_at σ 1 = 1 := by
  refine ⟨?_, ?_⟩ <;> simp +decide [value_at, mysel]

end PN_Counter_SPOT
