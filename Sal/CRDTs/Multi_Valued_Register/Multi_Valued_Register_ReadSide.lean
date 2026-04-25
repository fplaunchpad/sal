import Std.Tactic.BVDecide
import Sal.Interfaces.Set_Extended
import Sal.Tactic.Sal
import Sal.CRDTs.Multi_Valued_Register.Multi_Valued_Register_CRDT
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

/-! # Multi-Valued Register (CRDT, classical) — read-side projection

The 24 RA-linearizability VCs in `Multi_Valued_Register_CRDT.lean`
prove that the state `(writes, removed)` converges under pointwise
union — both components are grow-only sets joined by ∪. They say
nothing about the headline classical-MVR claims:

1. **Concurrent writes both survive.** Two replicas issuing
   `Write v₁` and `Write v₂` concurrently from a common pre-state
   end up with both values visible after merge.
2. **Sequential writes overwrite.** A subsequent `Write v` on the
   same replica retracts the prior visible value(s) by including
   their `ts`s in its snapshot `O`.

This file lifts both into Lean.

The visible-value predicate is the read-side counterpart of the
paper's `value()` query (Spec 14 line 14):

    visible_value v ≔ ∃ ts, (ts, v) ∈ writes ∧ ts ∉ removed

Reference: Marc Shapiro, Nuno Preguiça, Carlos Baquero, Marek
Zawirski. "A comprehensive study of Convergent and Commutative
Replicated Data Types." INRIA Research Report RR-7506, 2011 §3.2.2
Spec 14. -/

/-! ## Read-side primitives -/

/-- Value `v` is visible iff some `(ts, v)` write-record exists
that has not been superseded (its `ts` is not in `removed`). -/
def is_visible_value (s : concrete_st) (v : ℕ) : Prop :=
  ∃ ts : ℕ,
    mem (ts, v) (Prod.fst s) = true ∧
    mem ts (Prod.snd s) = false

/-! ## Convergence at the read -/

theorem is_visible_value_convergent (s₁ s₂ : concrete_st) (v : ℕ) :
    eq s₁ s₂ → (is_visible_value s₁ v ↔ is_visible_value s₂ v) := by
  rintro ⟨h_w, h_r⟩
  unfold is_visible_value
  refine exists_congr fun ts => and_congr (h_w (ts, v)) ?_
  have h := h_r ts
  constructor
  · intro h_f
    cases hh : mem ts (Prod.snd s₂)
    · rfl
    · exact Bool.noConfusion (h_f.symm.trans (h.mpr hh))
  · intro h_f
    cases hh : mem ts (Prod.snd s₁)
    · rfl
    · exact Bool.noConfusion (h_f.symm.trans (h.mp hh))

/-! ## Intent-preservation theorems -/

/-- **Lookup after Write.** Applying `Write v O` at fresh `ts` makes
`v` visible: the new `(ts, v)` is in writes, and `ts` is not yet in
removed (premise: `ts ∉ O`, which holds because the snapshot is
taken before the new ts is generated, and `ts ∉ Prod.snd s`, true
by `distinct_ops` for any reachable state). -/
theorem visible_after_write
    (s : concrete_st) (v ts rid : ℕ) (O : set ℕ)
    (h_fresh_O : mem ts O = false)
    (h_fresh_removed : mem ts (Prod.snd s) = false) :
    is_visible_value (do_ s (ts, rid, app_op_t.Write v O)) v := by
  refine ⟨ts, ?_, ?_⟩
  · simp [do_]
  · simp only [mem] at h_fresh_O h_fresh_removed
    simp [do_, h_fresh_O, h_fresh_removed]

/-- **Concurrent writes both survive (headline).** Two replicas
diverge from common state `s`. Each applies its own `Write` with a
snapshot that does NOT include the other's fresh `ts` (true by
`distinct_ops` for any reachable execution: each replica's snapshot
was taken before the other's write existed). After merge, both
`v₁` and `v₂` are visible.

Premise list:
  * The two new ts values are fresh (not in `s.writes`, not in `s.removed`).
  * Neither snapshot includes its own ts nor the other's ts.

These all hold structurally for any well-formed replica execution. -/
theorem concurrent_writes_both_visible
    (s : concrete_st) (v₁ v₂ ts₁ ts₂ rid₁ rid₂ : ℕ) (O₁ O₂ : set ℕ)
    (h_fresh_t1_O1 : mem ts₁ O₁ = false)
    (h_fresh_t2_O1 : mem ts₂ O₁ = false)
    (h_fresh_t1_O2 : mem ts₁ O₂ = false)
    (h_fresh_t2_O2 : mem ts₂ O₂ = false)
    (h_fresh_t1_R  : mem ts₁ (Prod.snd s) = false)
    (h_fresh_t2_R  : mem ts₂ (Prod.snd s) = false) :
    is_visible_value
      (merge
        (do_ s (ts₁, rid₁, app_op_t.Write v₁ O₁))
        (do_ s (ts₂, rid₂, app_op_t.Write v₂ O₂))) v₁ ∧
    is_visible_value
      (merge
        (do_ s (ts₁, rid₁, app_op_t.Write v₁ O₁))
        (do_ s (ts₂, rid₂, app_op_t.Write v₂ O₂))) v₂ := by
  simp only [mem] at h_fresh_t1_O1 h_fresh_t2_O1 h_fresh_t1_O2 h_fresh_t2_O2
                      h_fresh_t1_R h_fresh_t2_R
  refine ⟨⟨ts₁, ?_, ?_⟩, ⟨ts₂, ?_, ?_⟩⟩
  · simp [merge, do_]
  · simp [merge, do_, h_fresh_t1_O1, h_fresh_t1_O2, h_fresh_t1_R]
  · simp [merge, do_]
  · simp [merge, do_, h_fresh_t2_O1, h_fresh_t2_O2, h_fresh_t2_R]

/-- **Sequential write overwrites prior writes.** If a write at `ts₁`
is currently visible, and we apply `Write v₂ O₂` where `O₂` includes
`ts₁` (which is what a well-formed sequential write would do — its
prepare-time snapshot includes all currently-visible ts), then
`v₁` is no longer visible at the witness `ts₁`. -/
theorem sequential_write_supersedes
    (s : concrete_st) (v₁ v₂ ts₁ ts₂ rid : ℕ) (O₂ : set ℕ)
    (h_t1_in_O2 : mem ts₁ O₂ = true) :
    mem ts₁ (Prod.snd (do_ s (ts₂, rid, app_op_t.Write v₂ O₂))) = true := by
  simp only [mem] at h_t1_in_O2
  simp [do_, h_t1_in_O2]
