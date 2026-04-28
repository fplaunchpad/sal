import Sal.CRDTs.LWW_Register.LWW_Register_CRDT
import Sal.CRDTs.LWW_Register.LWW_Register_ReadSide

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open Classical

/-! # LWW_Register (CRDT) — SPOTs -/

namespace LWW_Register_SPOT

example : value (do_ init_st (1, 0, app_op_t.Write 42)) = 42 := by decide

example :
    value
      (do_ (do_ init_st (1, 0, app_op_t.Write 42)) (2, 0, app_op_t.Write 99))
      = 99 := by decide

/-- Concurrent writes converge to the higher-ts write. -/
example :
    let σ_a := do_ init_st (1, 0, app_op_t.Write 42)
    let σ_b := do_ init_st (2, 1, app_op_t.Write 99)
    value (merge σ_a σ_b) = 99 := by decide

end LWW_Register_SPOT
