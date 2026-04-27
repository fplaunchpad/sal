import Sal.Interfaces.Map_Extended
import Sal.MRDTs.OR_Set_Efficient.OR_Set_Efficient_MRDT
import Sal.MRDTs.OR_Set_Efficient.OR_Set_Efficient_ReadSide

set_option linter.mathlibStandardSet false

open Classical

/-! # OR-Set Efficient (MRDT) — SPOTs

Small Proof-Oriented Tests for the compressed `(rid, ts, elem)`
variant. Same scenarios as `Sal/MRDTs/OR_Set/OR_Set_SPOT.lean`; the
only difference is the tag shape and the `Add`'s per-replica
filter (drop prior `(rid, _, e)` before inserting). -/

namespace OR_Set_Efficient_MRDT_SPOT

/-- **SPOT 1 — Add makes element live.**

The new tag `(rid = 0, ts = 1, e = 5)` is in the post-state. -/
example :
    lookup (do_ init_st (1, 0, app_op_t.Add 5)) 5 :=
  lookup_after_add init_st 5 1 0

/-- **SPOT 2 — concurrent Add wins over Rem (headline).**

Branch `a` adds `5` at `(rid = 0, ts = 1)`; branch `b` issues
`Rem 5` from the empty LCA (filtering nothing). The new triple
`(0, 1, 5)` sits in `a \ l` and survives the three-way merge. -/
example :
    lookup
      (merge init_st
        (do_ init_st (1, 0, app_op_t.Add 5))
        (do_ init_st (2, 1, app_op_t.Rem 5)))
      5 :=
  add_wins_over_concurrent_remove init_st 5 1 2 0 1 (by decide)

/-- **SPOT 3 — sequential Add then Rem extinguishes.**

`Rem 5` filters every triple with elem = 5, including the just-added
`(0, 1, 5)`. -/
example :
    ¬ lookup
        (do_ (do_ init_st (1, 0, app_op_t.Add 5)) (2, 0, app_op_t.Rem 5))
        5 :=
  add_then_remove_extinguishes init_st 5 1 2 0 0

/-- **SPOT 4 — per-replica Add filter caps growth.**

The same replica adds `5` twice (ts = 1 then ts = 3). The second
`Add` first filters the prior `(0, _, 5)` triple, then inserts
`(0, 3, 5)`. The element remains live, witnessed by the latest
triple. The earlier `(0, 1, 5)` is gone. -/
example :
    let σ : concrete_st :=
      do_ (do_ init_st (1, 0, app_op_t.Add 5)) (3, 0, app_op_t.Add 5)
    lookup σ 5 ∧ ¬ mem (0, 1, 5) σ := by
  refine ⟨⟨0, 3, ?_⟩, ?_⟩
  · decide
  · decide

end OR_Set_Efficient_MRDT_SPOT
