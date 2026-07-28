import Std.Tactic.BVDecide
import Sal.Interfaces.Map_Extended
import Sal.Tactic.Sal
import Sal.CRDTs.PN_Counter.PN_Counter_CRDT
import Mathlib

set_option linter.mathlibStandardSet false

open scoped Classical
set_option maxHeartbeats 400000
set_option relaxedAutoImplicit false
set_option autoImplicit false
open Classical

/-! # PN_Counter (CRDT): read-side projection

The 24 RA-linearizability VCs in `PN_Counter_CRDT.lean` prove the
state `(incs, decs)` converges under per-key max. The headline
read-side claim is:

  > the per-replica net value at rid `r` is `incs[r] − decs[r]`,
  > and applying `Inc` / `Dec` at `r` adjusts that value by ±1.

Per-replica is the local-by-construction read; a global sum
across replicas is straightforward but requires enumerating
`domain incs ∪ domain decs`. We pin the per-replica view here. -/

/-- Per-replica net value: increments minus decrements at `rid`. -/
def value_at (s : concrete_st) (rid : ℕ) : Int :=
  mysel (Prod.fst s) rid - mysel (Prod.snd s) rid

/-- Convergence at the read: pointwise state equality lifts to
per-replica value equality. -/
theorem value_at_convergent (s₁ s₂ : concrete_st) (rid : ℕ) :
    eq s₁ s₂ → value_at s₁ rid = value_at s₂ rid := by
  intro ⟨h_pos, h_neg⟩
  unfold value_at
  rw [(h_pos rid).2, (h_neg rid).2]

/-- **Inc raises the replica's value by 1.** -/
theorem value_at_after_inc (s : concrete_st) (ts rid : ℕ) :
    value_at (do_ s (ts, rid, app_op_t.Inc)) rid = value_at s rid + 1 := by
  simp [value_at, do_, mysel]; ring

/-- **Dec lowers the replica's value by 1.** -/
theorem value_at_after_dec (s : concrete_st) (ts rid : ℕ) :
    value_at (do_ s (ts, rid, app_op_t.Dec)) rid = value_at s rid - 1 := by
  simp [value_at, do_, mysel]; ring

/-- Inc on replica `rid'` does not affect `rid`'s value when
`rid ≠ rid'`. -/
theorem value_at_unchanged_by_other_inc
    (s : concrete_st) (ts rid rid' : ℕ) (h_ne : rid ≠ rid') :
    value_at (do_ s (ts, rid', app_op_t.Inc)) rid = value_at s rid := by
  simp [value_at, do_, mysel, h_ne]
