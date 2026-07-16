import Sal.CRDTs.MAX_Register.MAX_Register_CRDT
import Sal.CRDTs.MAX_Register.MAX_Register_ReadSide

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open Classical

/-! # MAX_Register (CRDT) — SPOTs -/

namespace MAX_Register_SPOT

example : value (do_ init_st (1, 0, app_op_t.Write 5)) = 5 := by decide

example :
    value (do_ (do_ init_st (1, 0, app_op_t.Write 5)) (2, 0, app_op_t.Write 3))
      = 5 := by decide

example :
    let σ_a := do_ init_st (1, 0, app_op_t.Write 5)
    let σ_b := do_ init_st (2, 1, app_op_t.Write 7)
    value (merge σ_a σ_b) = 7 := by decide

/-! ## Negative companions (should-FAIL pins) -/

/-- A smaller later write does NOT clobber: this is MAX, not LWW. -/
example :
    value (do_ (do_ init_st (1, 0, app_op_t.Write 5)) (2, 0, app_op_t.Write 3))
      ≠ 3 := by decide

/-- Merge is not left-biased (and not min): the other order agrees on 7. -/
example :
    let σ_a := do_ init_st (1, 0, app_op_t.Write 5)
    let σ_b := do_ init_st (2, 1, app_op_t.Write 7)
    value (merge σ_b σ_a) ≠ 5 := by decide

end MAX_Register_SPOT
