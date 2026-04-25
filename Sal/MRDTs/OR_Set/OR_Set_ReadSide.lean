import Std.Tactic.BVDecide
import Sal.Interfaces.Set_Extended
import Sal.Tactic.Sal
import Sal.MRDTs.OR_Set.OR_Set_MRDT
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

/-! # OR-Set (MRDT) — read-side projection

MRDT counterpart to `Sal/CRDTs/OR_Set/OR_Set_ReadSide.lean`. The MRDT
state is `set (ts, elem)`; there is no tombstone component because
the LCA carries that information and the standard three-way set
merge `(l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)` realises Add-Wins directly.

The four read-side claims:

1. `lookup s e` — element `e` is live iff some `(ts, e)` tag is in `s`.
2. **Convergence at the read** — trivial since `eq` is `=` on this side.
3. **`lookup_after_add`** — fresh `Add` makes `e` live.
4. **`add_wins_over_concurrent_remove`** — the new tag sits in
   `a \ l` and survives the Rem-on-other-branch.
5. **`add_then_remove_extinguishes`** — `Rem` filters every tag for
   `e`, including the just-added one. -/

/-- Element `e` is live iff some tag `(ts, e)` is in the set. -/
def lookup (s : concrete_st) (e : ℕ) : Prop :=
  ∃ ts : ℕ, mem (ts, e) s = true

theorem lookup_convergent (s₁ s₂ : concrete_st) (e : ℕ) :
    eq s₁ s₂ → (lookup s₁ e ↔ lookup s₂ e) := by
  intro h_eq; unfold eq at h_eq; subst h_eq; rfl

/-- **Lookup after Add.** Applying `Add e` at `ts` immediately makes
`e` live: the new tag `(ts, e)` is unionised in. -/
theorem lookup_after_add
    (s : concrete_st) (e ts rid : ℕ) :
    lookup (do_ s (ts, rid, app_op_t.Add e)) e := by
  refine ⟨ts, ?_⟩
  simp [do_]

/-- **Add-wins over concurrent Remove (headline).** Two branches
diverge from common LCA `l`. One applies `Add e` at fresh `ts`; the
other applies `Rem e`. The new tag `(ts, e)` is in `a \ l` and
therefore survives the standard three-way merge. -/
theorem add_wins_over_concurrent_remove
    (l : concrete_st) (e ts ts_rem rid_add rid_rem : ℕ)
    (h_fresh : mem (ts, e) l = false) :
    lookup
      (merge l
        (do_ l (ts, rid_add, app_op_t.Add e))
        (do_ l (ts_rem, rid_rem, app_op_t.Rem e)))
      e := by
  refine ⟨ts, ?_⟩
  simp [merge, do_]
  grind

/-- **Add-then-Remove extinguishes.** `Rem e` filters out every tag
with elem = e from the set, so applying `Add e; Rem e` sequentially
on the same replica leaves `e` not-live (and any prior live tags
for `e` are filtered too). -/
theorem add_then_remove_extinguishes
    (s : concrete_st) (e ts1 ts2 rid1 rid2 : ℕ) :
    ¬ lookup
        (do_ (do_ s (ts1, rid1, app_op_t.Add e)) (ts2, rid2, app_op_t.Rem e))
        e := by
  rintro ⟨ts, h_mem⟩
  -- The filter strips every (_, e), so any survivor would have a
  -- different elem — but our witness has elem = e.
  simp [do_] at h_mem
