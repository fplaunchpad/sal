import Sal.CRDTs.Shopping_Cart.Shopping_Cart_CRDT
import Sal.CRDTs.Shopping_Cart.Shopping_Cart_ReadSide

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000
open Classical

/-! # Shopping_Cart (CRDT) — SPOTs -/

namespace Shopping_Cart_SPOT

example : add_count (do_ init_st (1, 0, app_op_t.Add 5)) 0 5 = 1 :=
  add_count_after_add init_st 1 0 5

example :
    remove_count (do_ init_st (1, 0, app_op_t.Remove 5)) 0 5 = 1 :=
  remove_count_after_remove init_st 1 0 5

/-- After Add then Remove on same replica/pid: per-replica qty is 0. -/
example :
    per_replica_qty
      (do_ (do_ init_st (1, 0, app_op_t.Add 5)) (2, 0, app_op_t.Remove 5))
      0 5 = 0 := by
  simp +decide [per_replica_qty, add_count, remove_count, mysel]

end Shopping_Cart_SPOT
