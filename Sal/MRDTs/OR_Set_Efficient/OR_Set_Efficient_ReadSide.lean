import Std.Tactic.BVDecide
import Sal.Interfaces.Set_Extended
import Sal.Tactic.Sal
import Sal.MRDTs.OR_Set_Efficient.OR_Set_Efficient_MRDT
import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 0
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Classical

/-! # OR-Set Efficient (MRDT): read-side projection

MRDT readside for the compressed OR-Set variant whose tags are
`(rid, ts, elem)` triples (one tag per `(rid, elem)` pair). The
state is a flat `set (ℕ × ℕ × ℕ)`. Same headline claims as
`OR_Set_ReadSide.lean`; the only difference is the tag shape.

The do_ for `Add` first filters any prior `(rid, _, e)` tag from
the same replica before inserting the new one, capping per-replica
growth at one tag per element. Convergence at the read is unchanged. -/

/-- Element `e` is live iff some tag `(rid, ts, e)` is in the set. -/
def lookup (s : concrete_st) (e : ℕ) : Prop :=
  ∃ rid ts : ℕ, mem (rid, ts, e) s = true

theorem lookup_convergent (s₁ s₂ : concrete_st) (e : ℕ) :
    eq s₁ s₂ → (lookup s₁ e ↔ lookup s₂ e) := by
  intro h_eq; unfold eq at h_eq; subst h_eq; rfl

/-- **Lookup after Add.** The new tag `(rid, ts, e)` is in the
post-state, so `e` is live. -/
theorem lookup_after_add
    (s : concrete_st) (e ts rid : ℕ) :
    lookup (do_ s (ts, rid, app_op_t.Add e)) e := by
  refine ⟨rid, ts, ?_⟩
  simp [do_]

/-- **Add-wins over concurrent Remove.** The fresh tag sits in
`a \ l` after the three-way merge and is not filtered by the Rem
on the other branch. Premise: the new tag is fresh in the LCA, and
no `(rid, _, e)` tag from the same replica was previously present
(otherwise the `Add`'s filter would have just renamed it, not
created a new tag, but the headline still holds). -/
theorem add_wins_over_concurrent_remove
    (l : concrete_st) (e ts ts_rem rid_add rid_rem : ℕ)
    (h_fresh : mem (rid_add, ts, e) l = false) :
    lookup
      (merge l
        (do_ l (ts, rid_add, app_op_t.Add e))
        (do_ l (ts_rem, rid_rem, app_op_t.Rem e)))
      e := by
  refine ⟨rid_add, ts, ?_⟩
  simp [merge, do_]
  grind

/-- **Add-then-Remove extinguishes.** `Rem e` filters every tag
with elem = e, including the just-added one. -/
theorem add_then_remove_extinguishes
    (s : concrete_st) (e ts1 ts2 rid1 rid2 : ℕ) :
    ¬ lookup
        (do_ (do_ s (ts1, rid1, app_op_t.Add e)) (ts2, rid2, app_op_t.Rem e))
        e := by
  rintro ⟨rid, ts, h_mem⟩
  simp [do_] at h_mem
