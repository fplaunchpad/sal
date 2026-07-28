import Sal.MRDTs.Increment_Only_Counter.Increment_Only_Counter_MRDT
import Sal.MRDTs.Increment_Only_Counter.Increment_Only_Counter_ReadSide

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open Classical

/-! # Increment_Only_Counter (MRDT): SPOTs -/

namespace Increment_Only_Counter_MRDT_SPOT

example : value (do_ init_st (1, 0, app_op_t.Incr)) = 1 := rfl

example :
    value (do_ (do_ init_st (1, 0, app_op_t.Incr)) (2, 0, app_op_t.Incr)) = 2 := rfl

/-- Concurrent Incrs from a common LCA: the shared LCA is subtracted
once, so two concurrent Incrs from a value-1 LCA give value 3. -/
example :
    let l := do_ init_st (1, 0, app_op_t.Incr)        -- value 1
    let σ_a := do_ l (2, 0, app_op_t.Incr)             -- value 2
    let σ_b := do_ l (3, 1, app_op_t.Incr)             -- value 2
    value (merge l σ_a σ_b) = 3 := rfl

end Increment_Only_Counter_MRDT_SPOT
