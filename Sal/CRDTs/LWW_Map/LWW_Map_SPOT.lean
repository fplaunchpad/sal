import Sal.CRDTs.LWW_Map.LWW_Map_CRDT
import Sal.CRDTs.LWW_Map.LWW_Map_ReadSide

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open Classical

/-! # LWW_Map (CRDT): SPOTs -/

namespace LWW_Map_SPOT

example : lookup (do_ init_st (1, 0, app_op_t.Write 1 5)) 1 = 5 := by
  simp +decide [lookup, do_, mysel, lex_max]

example :
    lookup
      (do_ (do_ init_st (1, 0, app_op_t.Write 1 5)) (2, 0, app_op_t.Write 1 3))
      1 = 3 := by
  simp +decide [lookup, do_, mysel, lex_max]

/-- Concurrent writes at same key: higher-ts write wins. -/
example :
    let σ_a := do_ init_st (1, 0, app_op_t.Write 1 5)
    let σ_b := do_ init_st (2, 1, app_op_t.Write 1 3)
    lookup (merge σ_a σ_b) 1 = 3 := by
  simp +decide [lookup, do_, mysel, lex_max]

end LWW_Map_SPOT
