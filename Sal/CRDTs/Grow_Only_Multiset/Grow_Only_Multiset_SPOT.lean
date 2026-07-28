import Sal.CRDTs.Grow_Only_Multiset.Grow_Only_Multiset_CRDT
import Sal.CRDTs.Grow_Only_Multiset.Grow_Only_Multiset_ReadSide

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000
open Classical

/-! # Grow_Only_Multiset (CRDT): SPOTs -/

namespace Grow_Only_Multiset_SPOT

example : count_at (do_ init_st (1, 0, app_op_t.Add 5)) 0 5 = 1 :=
  count_at_after_add init_st 1 0 5

example :
    count_at (do_ (do_ init_st (1, 0, app_op_t.Add 5)) (2, 0, app_op_t.Add 5))
      0 5 = 2 := by
  rw [count_at_after_add, count_at_after_add]
  simp [count_at, mysel]

example :
    let σ_a := do_ init_st (1, 0, app_op_t.Add 5)
    let σ_b := do_ init_st (2, 1, app_op_t.Add 5)
    let σ := merge σ_a σ_b
    count_at σ 0 5 = 1 ∧ count_at σ 1 5 = 1 := by
  refine ⟨?_, ?_⟩ <;> simp +decide [count_at, mysel]

end Grow_Only_Multiset_SPOT
