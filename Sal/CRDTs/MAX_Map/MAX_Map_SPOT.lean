import Sal.CRDTs.MAX_Map.MAX_Map_CRDT
import Sal.CRDTs.MAX_Map.MAX_Map_ReadSide

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open Classical

/-! # MAX_Map (CRDT): SPOTs -/

namespace MAX_Map_SPOT

example : lookup (do_ init_st (1, 0, app_op_t.Write 1 5)) 1 = 5 := by
  rw [lookup_after_write]; rfl

example :
    lookup
      (do_ (do_ init_st (1, 0, app_op_t.Write 1 5)) (2, 0, app_op_t.Write 1 3))
      1 = 5 := by
  rw [lookup_after_write, lookup_after_write]; rfl

/-- Concurrent Writes at same key converge to the max. -/
example :
    let σ_a := do_ init_st (1, 0, app_op_t.Write 1 5)
    let σ_b := do_ init_st (2, 1, app_op_t.Write 1 3)
    lookup (merge σ_a σ_b) 1 = 5 := by
  simp +decide [lookup, mysel]

end MAX_Map_SPOT
