import Sal.CRDTs.MIN_Register.MIN_Register_CRDT
import Sal.CRDTs.MIN_Register.MIN_Register_ReadSide

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open Classical

/-! # MIN_Register (CRDT) — SPOTs

Note: with `init_st = 0` on ℕ the state is absorbing at 0; SPOTs
below start from a non-zero baseline to exercise the min behaviour. -/

namespace MIN_Register_SPOT

example : value (do_ (5 : concrete_st) (1, 0, app_op_t.Write 3)) = 3 := by decide

example : value (do_ (5 : concrete_st) (1, 0, app_op_t.Write 7)) = 5 := by decide

example : value (merge (5 : concrete_st) (3 : concrete_st)) = 3 := by decide

/-! ## Negative companions (should-FAIL pins) -/

/-- A larger later write does NOT clobber: this is MIN, not LWW. -/
example : value (do_ (5 : concrete_st) (1, 0, app_op_t.Write 7)) ≠ 7 := by decide

/-- Merge is not max and not left-biased: the other order is not 5. -/
example : value (merge (3 : concrete_st) (5 : concrete_st)) ≠ 5 := by decide

end MIN_Register_SPOT
