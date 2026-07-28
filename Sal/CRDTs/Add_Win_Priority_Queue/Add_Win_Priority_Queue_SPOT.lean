import Sal.Interfaces.Set_Extended
import Sal.Interfaces.Map_Extended
import Sal.CRDTs.Add_Win_Priority_Queue.Add_Win_Priority_Queue_CRDT
import Sal.CRDTs.Add_Win_Priority_Queue.Add_Win_Priority_Queue_ReadSide

set_option linter.mathlibStandardSet false

open Classical

/-! # Add-Win Priority Queue (CRDT): SPOTs

CRDT-side mirror of `Sal/MRDTs/Add_Win_Priority_Queue/Add_Win_Priority_Queue_SPOT.lean`.
State shape: `(A, I, R)` where `R` is the tombstone set; `Rmv`
carries a prepare-time snapshot `D ⊆ (elem, add_ts)` in its payload.

Reference: Zhang et al., Internetware 2023. -/

namespace AW_CRPQ_CRDT_SPOT

/-- **SPOT 1: Add makes element live.**

A single `Add 5 100` from the initial state writes `A[(5, 1)] := 100`
and leaves `R` empty, so `lookup σ 5` finds the witness. -/
example :
    lookup (do_ init_st (1, 0, app_op_t.Add 5 100)) 5 :=
  lookup_after_add init_st 5 100 1 0 (by decide)

/-- **SPOT 2: concurrent Add wins over Rmv (headline).**

A single replica issues `Add 5 100` (ts = 1), then later `Rmv 5`
with empty snapshot `D = ∅`, i.e. the Rmv was prepared without
having observed the Add (the state-based stand-in for "concurrent").
The element survives because `D` does not include `(5, 1)`. -/
example :
    lookup
      (do_ (do_ init_st (1, 0, app_op_t.Add 5 100))
           (2, 1, app_op_t.Rmv 5 empty))
      5 :=
  add_wins_over_concurrent_rmv init_st 5 100 1 0 2 1 empty
    (by decide) (by decide) (by decide)

/-- **SPOT 3: Inc creates an inc-record.**

Applying `Inc 5 10` puts `(5, 2, 10)` into the I component
regardless of prior state. -/
example :
    (Prod.fst (Prod.snd (do_ init_st (2, 0, app_op_t.Inc 5 10))))
        (5, 2, 10) = true :=
  inc_creates_inc_record init_st 5 10 2 0

/-- **SPOT 4: Inc increases the acquired value.**

Starting from the empty state (acquired = 0), applying `Inc 5 10`
raises the acquired value of `5` to `10`. -/
example :
    is_acquired (do_ init_st (1, 0, app_op_t.Inc 5 10)) 5 (0 + 10) := by
  apply inc_increases_acquired init_st 5 10 1 0 (by decide) 0
  exact ⟨[], List.nodup_nil, by intro p; simp [init_st], by simp⟩

/-- **SPOT 5: Rmv with the right snapshot extinguishes a prior Add.**

A single replica issues `Add 5 100` (ts = 1), then `Rmv 5 D` whose
prepare-time snapshot `D = {(5, 1)}` includes the just-added record.
After the Rmv, `(5, 1)` sits in `R`, so `lookup σ 5` fails. -/
example :
    ¬ lookup
        (do_ (do_ init_st (1, 0, app_op_t.Add 5 100))
             (2, 0, app_op_t.Rmv 5 (add (5, 1) empty)))
        5 := by
  rintro ⟨ts, h_dom, h_R⟩
  simp [do_, init_st] at h_dom h_R
  grind

/-! ## Negative companion (should-FAIL pin) -/

/-- The read is not constantly true: nothing is live in the initial
state, and an Add of `5` does not make an un-added `6` live. -/
example :
    ¬ lookup (do_ init_st (1, 0, app_op_t.Add 5 100)) 6 := by
  rintro ⟨ts, h_dom, -⟩
  simp [do_, init_st] at h_dom

end AW_CRPQ_CRDT_SPOT
