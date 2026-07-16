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

/-! ## Negative companions (should-FAIL pins)

Convention: every SPOT block carries negatives pinning the tempting
degenerate implementations; expected values are hand-derived, never
`#eval`'d from the code under test. -/

/-- Merge is not left-biased: the other argument order agrees. -/
example :
    let σ_a := do_ init_st (1, 0, app_op_t.Write 42)
    let σ_b := do_ init_st (2, 1, app_op_t.Write 99)
    value (merge σ_b σ_a) = 99 := by decide

/-- The FIRST-writer verdict is wrong: this register is LWW, not FWW
(the distinction the `lww_merge_needs_timestamps` kill-test polices). -/
example :
    let σ_a := do_ init_st (1, 0, app_op_t.Write 42)
    let σ_b := do_ init_st (2, 1, app_op_t.Write 99)
    value (merge σ_a σ_b) ≠ 42 := by decide

/-- A later write is not ignored: the state is not write-once. -/
example :
    value
      (do_ (do_ init_st (1, 0, app_op_t.Write 42)) (2, 0, app_op_t.Write 99))
      ≠ 42 := by decide

end LWW_Register_SPOT
