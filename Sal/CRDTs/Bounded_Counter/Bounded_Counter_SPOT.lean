import Sal.CRDTs.Bounded_Counter.Bounded_Counter_CRDT
import Sal.CRDTs.Bounded_Counter.Bounded_Counter_ReadSide

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open Classical

/-! # Bounded_Counter (CRDT): SPOTs -/

namespace Bounded_Counter_SPOT

example : inc_count (do_ init_st (1, 0, app_op_t.Inc)) 0 = 1 :=
  inc_count_after_inc init_st 1 0

example : dec_count (do_ init_st (1, 0, app_op_t.Dec)) 0 = 1 :=
  dec_count_after_dec init_st 1 0

example :
    transfer_count
      (do_ init_st (1, 0, app_op_t.Transfer 1)) 0 1 = 1 :=
  transfer_count_after_transfer init_st 1 0 1

end Bounded_Counter_SPOT
