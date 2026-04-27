import Sal.Interfaces.Set_Extended
import Sal.MRDTs.Add_Win_Priority_Queue.Add_Win_Priority_Queue_MRDT
import Sal.MRDTs.Add_Win_Priority_Queue.Add_Win_Priority_Queue_ReadSide

set_option linter.mathlibStandardSet false

open Classical

/-! # Add-Win Priority Queue (MRDT) — SPOTs

Small Proof-Oriented Tests for the canonical AW-CRPQ semantic
claims. State shape: `(A, I)` with no tombstone component (the LCA
carries that information).

Reference: Zhang et al., Internetware 2023. -/

namespace AW_CRPQ_MRDT_SPOT

/-- **SPOT 1 — Add makes element live.**

A single `Add 5 100` stakes `(1, 5, 100)` in the A component, so
`lookup σ 5` finds the witness `ts = 1, v = 100`. -/
example :
    lookup (do_ init_st (1, 0, app_op_t.Add 5 100)) 5 :=
  lookup_after_add init_st 5 100 1 0

/-- **SPOT 2 — concurrent Add wins over Rmv (headline).**

LCA `init_st` is empty. Branch `a` issues `Add 5 100` at ts = 1;
branch `b` issues `Rmv 5` at ts = 2. The new add record `(1, 5, 100)`
sits in `a \ l` and survives the three-way merge. -/
example :
    lookup
      (merge init_st
        (do_ init_st (1, 0, app_op_t.Add 5 100))
        (do_ init_st (2, 1, app_op_t.Rmv 5)))
      5 :=
  add_wins_over_concurrent_rmv init_st 5 100 1 0 2 1 (by decide)

/-- **SPOT 3 — Inc creates an inc-record.**

Applying `Inc 5 10` puts `(2, 5, 10)` into the I component. -/
example :
    (Prod.snd (do_ init_st (2, 0, app_op_t.Inc 5 10))) (2, 5, 10) = true :=
  inc_creates_inc_record init_st 5 10 2 0

/-- **SPOT 4 — Inc increases the acquired value.**

Starting from the empty state (acquired = 0), applying `Inc 5 10`
raises the acquired value of `5` to `10`. -/
example :
    is_acquired (do_ init_st (1, 0, app_op_t.Inc 5 10)) 5 (0 + 10) := by
  apply inc_increases_acquired init_st 5 10 1 0 (by decide) 0
  exact ⟨[], List.nodup_nil, by intro p; simp [init_st], by simp⟩

/-- **SPOT 5 — Rmv extinguishes a sequential Add.**

`Add 5 100` then `Rmv 5` on a single replica leaves `5` not-live:
the Rmv filters every `(_, 5, _)` from A. -/
example :
    ¬ lookup
        (do_ (do_ init_st (1, 0, app_op_t.Add 5 100))
             (2, 0, app_op_t.Rmv 5))
        5 := by
  rintro ⟨ts, v, h_mem⟩
  simp [do_] at h_mem

end AW_CRPQ_MRDT_SPOT
