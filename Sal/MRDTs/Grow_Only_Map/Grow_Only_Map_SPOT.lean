import Sal.MRDTs.Grow_Only_Map.Grow_Only_Map_MRDT
import Sal.MRDTs.Grow_Only_Map.Grow_Only_Map_ReadSide

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open Classical

/-! # Grow_Only_Map (MRDT): SPOTs -/

namespace Grow_Only_Map_SPOT

example : lookup (do_ init_st (1, 0, (1, 5))) 1 5 = true :=
  lookup_after_put init_st 1 0 1 5

example :
    let σ_a := do_ init_st (1, 0, (1, 5))
    let σ_b := do_ init_st (2, 1, (1, 7))
    let σ := merge init_st σ_a σ_b
    lookup σ 1 5 = true ∧ lookup σ 1 7 = true := by
  refine ⟨?_, ?_⟩ <;> simp +decide [lookup, mysel, mem]

end Grow_Only_Map_SPOT
