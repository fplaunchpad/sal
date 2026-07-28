import Sal.MRDTs.Grow_Only_Set.Grow_Only_Set_MRDT
import Sal.MRDTs.Grow_Only_Set.Grow_Only_Set_ReadSide

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000
open Classical

/-! # Grow_Only_Set (MRDT): SPOTs -/

namespace Grow_Only_Set_MRDT_SPOT

example : lookup (do_ init_st (1, 0, 5)) 5 = true :=
  lookup_after_add init_st 1 0 5

example :
    let σ_a := do_ init_st (1, 0, 5)
    let σ_b := do_ init_st (2, 1, 7)
    let σ := merge init_st σ_a σ_b
    lookup σ 5 = true ∧ lookup σ 7 = true := by
  refine ⟨?_, ?_⟩ <;> simp +decide [lookup, mem, union, add]

end Grow_Only_Set_MRDT_SPOT
