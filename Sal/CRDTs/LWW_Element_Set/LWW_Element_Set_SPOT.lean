import Sal.CRDTs.LWW_Element_Set.LWW_Element_Set_CRDT
import Sal.CRDTs.LWW_Element_Set.LWW_Element_Set_ReadSide

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000
open Classical

/-! # LWW_Element_Set (CRDT): SPOTs -/

namespace LWW_Element_Set_SPOT

example : lookup (do_ init_st (1, 0, app_op_t.Add 5)) 5 := by
  simp [lookup, do_, mysel]

/-- Add at ts=1, then Remove at ts=2: element is dead. -/
example :
    ¬ lookup
        (do_ (do_ init_st (1, 0, app_op_t.Add 5)) (2, 0, app_op_t.Remove 5))
        5 := by
  simp [lookup, do_, mysel]

/-- Concurrent Add ts=2 and Remove ts=1: Add wins. -/
example :
    let σ_a := do_ init_st (2, 0, app_op_t.Add 5)
    let σ_b := do_ init_st (1, 1, app_op_t.Remove 5)
    lookup (merge σ_a σ_b) 5 := by
  simp +decide [lookup, do_, merge, mysel]

end LWW_Element_Set_SPOT
