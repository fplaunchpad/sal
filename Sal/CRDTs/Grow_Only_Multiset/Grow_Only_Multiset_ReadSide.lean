import Std.Tactic.BVDecide
import Sal.Interfaces.Map_Extended
import Sal.Tactic.Sal
import Sal.CRDTs.Grow_Only_Multiset.Grow_Only_Multiset_CRDT
import Mathlib

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000
set_option relaxedAutoImplicit false
set_option autoImplicit false
open Classical

/-! # Grow_Only_Multiset (CRDT) — read-side projection

The 24 VCs prove the per-`(rid, eid)` count map converges under
per-slot max. The headline read is the **per-replica add count** —
how many times replica `rid` has added element `eid`. The
multiset's true multiplicity for `eid` is `Σ_rid count_at(rid, eid)`,
which is left as a derived client-side computation. -/

def count_at (s : concrete_st) (rid eid : ℕ) : Int := mysel s (rid, eid)

theorem count_at_convergent (s₁ s₂ : concrete_st) (rid eid : ℕ) :
    eq s₁ s₂ → count_at s₁ rid eid = count_at s₂ rid eid := by
  intro h_eq
  unfold count_at
  exact (h_eq (rid, eid)).2

/-- **Add eid by replica rid raises that replica's count for eid by 1.** -/
theorem count_at_after_add (s : concrete_st) (ts rid eid : ℕ) :
    count_at (do_ s (ts, rid, app_op_t.Add eid)) rid eid =
      count_at s rid eid + 1 := by
  simp [count_at, do_, mysel]

/-- An `Add eid'` by replica `rid'` does not affect `(rid, eid)`'s
count when the slot is different. -/
theorem count_at_unchanged_by_other_slot
    (s : concrete_st) (ts rid eid rid' eid' : ℕ)
    (h_ne : (rid, eid) ≠ (rid', eid')) :
    count_at (do_ s (ts, rid', app_op_t.Add eid')) rid eid =
      count_at s rid eid := by
  simp [count_at, do_, mysel, h_ne, Ne.symm h_ne]
