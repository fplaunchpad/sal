import Std.Tactic.BVDecide
import Sal.Interfaces.Set_Extended
import Sal.Tactic.Sal
import Sal.CRDTs.OR_Set.OR_Set_CRDT
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

/-! # OR-Set (CRDT) — read-side projection

The 24 RA-linearizability VCs in `OR_Set_CRDT.lean` prove that the
state `(adds, tombstones)` converges under merge — both are grow-only
sets, joined by union. They say nothing about the headline OR-Set
semantics: an element `e` is live iff it has an add-tag that has
not been observed-removed, and a concurrent `Rem` that did not
observe a particular `Add` does not retract it.

This file lifts those headline claims into Lean, mirroring the
Peritext / AW-CRPQ readside methodology:

1. `lookup s e` — element `e` is live iff some `(e, ts)` add-tag is
   not in the tombstones set.
2. **Convergence at the read.**
3. **Three intent theorems:**
   - `lookup_after_add` — fresh `Add` makes the element live.
   - `add_wins_over_concurrent_remove` — an `Add` whose tag is not
     in the merged tombstones survives.
   - `add_then_remove_extinguishes` — sequential `Add e; Rem e`
     leaves `e` not-live.

Reference: Marc Shapiro, Nuno Preguiça, Carlos Baquero, Marek
Zawirski. "A comprehensive study of Convergent and Commutative
Replicated Data Types." INRIA Research Report RR-7506, 2011. -/

/-! ## Read-side primitives -/

/-- Element `e` is live iff some add-tag for `e` is not tombstoned. -/
def lookup (s : concrete_st) (e : ℕ) : Prop :=
  ∃ ts : ℕ,
    mem (e, ts) (Prod.fst s) = true ∧
    mem (e, ts) (Prod.snd s) = false

/-! ## Convergence at the read -/

theorem lookup_convergent (s₁ s₂ : concrete_st) (e : ℕ) :
    eq s₁ s₂ → (lookup s₁ e ↔ lookup s₂ e) := by
  rintro ⟨h_adds, h_tombs⟩
  unfold lookup
  refine exists_congr fun ts => and_congr (h_adds (e, ts)) ?_
  have h := h_tombs (e, ts)
  constructor
  · intro h_f
    cases hh : mem (e, ts) (Prod.snd s₂)
    · rfl
    · exact Bool.noConfusion (h_f.symm.trans (h.mpr hh))
  · intro h_f
    cases hh : mem (e, ts) (Prod.snd s₁)
    · rfl
    · exact Bool.noConfusion (h_f.symm.trans (h.mp hh))

/-! ## Intent-preservation theorems -/

/-- **Lookup after Add.** If the new add-tag `(e, ts)` is fresh in
the tombstones (true under `distinct_ops`: globally unique `ts`),
then applying `Add e` at `ts` makes `e` live. -/
theorem lookup_after_add
    (s : concrete_st) (e ts rid : ℕ)
    (h_fresh : mem (e, ts) (Prod.snd s) = false) :
    lookup (do_ s (ts, rid, app_op_t.Add e)) e := by
  simp only [mem] at h_fresh
  refine ⟨ts, ?_, ?_⟩
  · simp [do_]
  · simp [do_, h_fresh]

/-- **Add-wins over concurrent Remove (headline).** Two replicas
diverge from common state `s`: one applies `Add e` at fresh `ts`,
the other applies `Rem e`. The `Rem`'s effect is a state-read at
its replica — it tombstones every `(e, _)` it observed locally,
which does *not* include the new `(e, ts)` (concurrent on the other
replica). After merge, `(e, ts)` is in the union of `adds` and is
not in the union of tombstones, so `lookup` finds it.

Premises: `(e, ts) ∉ Prod.fst s` and `(e, ts) ∉ Prod.snd s` —
both follow from `distinct_ops`/state freshness in any reachable
execution. -/
theorem add_wins_over_concurrent_remove
    (s : concrete_st) (e ts ts_rem rid_add rid_rem : ℕ)
    (h_fresh_adds : mem (e, ts) (Prod.fst s) = false)
    (h_fresh_tombs : mem (e, ts) (Prod.snd s) = false) :
    lookup
      (merge
        (do_ s (ts, rid_add, app_op_t.Add e))
        (do_ s (ts_rem, rid_rem, app_op_t.Rem e)))
      e := by
  simp only [mem] at h_fresh_adds h_fresh_tombs
  refine ⟨ts, ?_, ?_⟩
  · simp [merge, do_]
  · simp [merge, do_, h_fresh_adds, h_fresh_tombs]

/-- **Add-then-Remove extinguishes.** Sequential `Add e` followed
by `Rem e` on a single replica leaves `e` not-live. The `Rem`'s
state-read sees the just-added tag (and any prior live tags for
`e`) and tombstones them all. -/
theorem add_then_remove_extinguishes
    (s : concrete_st) (e ts1 ts2 rid1 rid2 : ℕ) :
    ¬ lookup
        (do_ (do_ s (ts1, rid1, app_op_t.Add e)) (ts2, rid2, app_op_t.Rem e))
        e := by
  rintro ⟨ts, h_in, h_not_tomb⟩
  -- After Add e: adds = add (e, ts1) s.1.
  -- After Rem e: tombs = s.2 ∪ filter (add (e, ts1) s.1) (·.1 = e).
  -- Any (e, ts) in the new adds has first coord = e and so is in the filter,
  -- hence in the new tombs — contradicting h_not_tomb.
  simp [do_] at h_in h_not_tomb
  grind
