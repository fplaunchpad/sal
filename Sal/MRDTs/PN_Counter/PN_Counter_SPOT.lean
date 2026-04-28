import Sal.MRDTs.PN_Counter.PN_Counter_MRDT
import Sal.MRDTs.PN_Counter.PN_Counter_ReadSide

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open Classical

/-! # PN_Counter (MRDT) — SPOTs -/

namespace PN_Counter_MRDT_SPOT

example : value (do_ init_st (1, 0, app_op_t.Inc)) = 1 := rfl

example :
    value (do_ (do_ init_st (1, 0, app_op_t.Inc)) (2, 0, app_op_t.Dec)) = 0 := rfl

/-- Concurrent Inc + Dec from a common LCA: branches converge to 0. -/
example :
    let σ_a := do_ init_st (1, 0, app_op_t.Inc)
    let σ_b := do_ init_st (2, 1, app_op_t.Dec)
    value (merge init_st σ_a σ_b) = 0 := rfl

end PN_Counter_MRDT_SPOT
