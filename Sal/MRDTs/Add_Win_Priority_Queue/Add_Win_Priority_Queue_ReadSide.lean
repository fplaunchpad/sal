import Std.Tactic.BVDecide
import Sal.Interfaces.Set_Extended
import Sal.Tactic.Sal
import Sal.MRDTs.Add_Win_Priority_Queue.Add_Win_Priority_Queue_MRDT
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

/-! # Add-Win Priority Queue (MRDT) — read-side projection

MRDT counterpart to `Sal/CRDTs/Add_Win_Priority_Queue_ReadSide.lean`.
The 24 RA-linearizability VCs in `Add_Win_Priority_Queue_MRDT.lean`
prove convergence of the state `(A, I)` under three-way merge. They
say nothing about whether queries against that state behave the way
the paper claims.

This file lifts `lookup` and the LWW innate property into Lean and
proves three intent theorems:

1. **`lookup_convergent`** — convergence at the read.
2. **`add_wins_over_concurrent_rmv`** — headline: an Add on one branch
   that is *not present* in the LCA survives a concurrent Rmv on the
   other branch. The state-based stand-in for "concurrent" is "the
   Add record sits in `a \ l`" — the merge term that bypasses the
   Rmv branch. (See `Add_Win_Priority_Queue_MRDT.lean:36–39`.)
3. **`innate_record_unique`** — uniqueness of the LWW innate record.

`acquired`, `priority`, `get_max`, and `is_empty` are out of scope.
**Faithfulness caveat:** the paper's acquired-value resolution is
**Most-Change-Win** (Alg 2 line 8), not summation. Our state shape
omits the per-record `count` field needed to express MCW. See
`docs/aw-crpq-vs-paper.md` for the full divergence list. -/

/-! ## Read-side primitives

State shape on this side: `Prod.fst : set (add_ts, elem, value)` and
`Prod.snd : set (inc_ts, elem, amount)`. There is no tombstone
component (`R`) — the LCA carries that information. -/

/-- **Lookup.** Element `e` is live iff there is at least one add
record `(ts, e, v)` for it in `A`. No separate tombstone check on
this side: a Rmv is implemented as a local filter on `A`. -/
def lookup (s : concrete_st) (e : ℕ) : Prop :=
  ∃ ts v : ℕ, mem (ts, e, v) (Prod.fst s) = true

/-- **Innate-record predicate.** `(ts, v)` is the LWW innate record
for element `e` in state `s` iff `(ts, e, v)` is present in `A` and
no record with strictly larger `add_ts` is present for the same `e`. -/
def is_innate_record (s : concrete_st) (e ts v : ℕ) : Prop :=
  mem (ts, e, v) (Prod.fst s) = true ∧
  ∀ ts' v', ts' > ts → mem (ts', e, v') (Prod.fst s) = false

/-! ## Convergence at the read -/

/-- Pointwise state equality (here, plain `=` on the pair of sets)
implies that lookup agrees on every element. -/
theorem lookup_convergent (s₁ s₂ : concrete_st) (e : ℕ) :
    eq s₁ s₂ → (lookup s₁ e ↔ lookup s₂ e) := by
  intro h_eq
  unfold eq at h_eq
  subst h_eq
  rfl

/-- Pointwise state equality lifts to `is_innate_record`. -/
theorem is_innate_record_convergent
    (s₁ s₂ : concrete_st) (e ts v : ℕ) :
    eq s₁ s₂ → (is_innate_record s₁ e ts v ↔ is_innate_record s₂ e ts v) := by
  intro h_eq
  unfold eq at h_eq
  subst h_eq
  rfl

/-! ## Intent-preservation theorems -/

/-- **Add-wins over concurrent Rmv (headline).** Two branches diverge
from a common LCA `l`: one applies `Add e v` at `ts1`, the other
applies `Rmv e`. If `(ts1, e, v)` is fresh in `l` (not previously
present), then after the standard three-way merge `e` is still live.

The merge term `a \ l` contains the fresh Add record, which is
preserved disjointly from the `b \ l` term holding any other branch
work. This is the structural reason the MRDT does not need a
tombstone payload on `Rmv`. -/
theorem add_wins_over_concurrent_rmv
    (l : concrete_st) (e v ts1 rid1 ts2 rid2 : ℕ) :
    mem (ts1, e, v) (Prod.fst l) = false →
    lookup
      (merge l
        (do_ l (ts1, rid1, app_op_t.Add e v))
        (do_ l (ts2, rid2, app_op_t.Rmv e)))
      e := by
  intro h_fresh
  refine ⟨ts1, v, ?_⟩
  simp [merge, do_]
  grind

/-- **Lookup after Add.** Applying `Add e v` immediately makes `e`
live. The new record `(ts, e, v)` is unionised into `A`. -/
theorem lookup_after_add
    (s : concrete_st) (e v ts rid : ℕ) :
    lookup (do_ s (ts, rid, app_op_t.Add e v)) e := by
  refine ⟨ts, v, ?_⟩
  simp [do_]

/-- **Innate is LWW (uniqueness of the max-`ts` record).** At most
one `(ts, v)` is the innate record for any element. Same argument as
the CRDT side: each innate record's max-clause forbids the other's
`ts`. -/
theorem innate_record_unique
    (s : concrete_st) (e ts1 ts2 v1 v2 : ℕ) :
    is_innate_record s e ts1 v1 →
    is_innate_record s e ts2 v2 →
    ts1 = ts2 := by
  intro h1 h2
  obtain ⟨h1_mem, h1_max⟩ := h1
  obtain ⟨h2_mem, h2_max⟩ := h2
  rcases lt_trichotomy ts1 ts2 with h | h | h
  · exact Bool.noConfusion (h2_mem.symm.trans (h1_max ts2 v2 h))
  · exact h
  · exact Bool.noConfusion (h1_mem.symm.trans (h2_max ts1 v1 h))

/-! ## Closing the gap: is_empty, acquired, priority, get_max

These complete the paper's query set (§2.2 and Algorithm 1).
Faithfulness rationale and the flat-observation simplification are
discussed in `docs/aw-crpq-vs-paper.md` and the CRDT-side
`Add_Win_Priority_Queue_ReadSide.lean` docstrings.

The MRDT state is `set (add_ts, elem, value) × set (inc_ts, elem, amount)`,
so witness lists carry `(inc_ts, amount)` pairs and look up
membership at `(p.1, e, p.2)` (different field ordering from the
CRDT). Convergence is trivial since `eq` on the MRDT is plain `=`. -/

/-- **Empty.** No element is currently live. -/
def is_empty (s : concrete_st) : Prop := ∀ e : ℕ, ¬ lookup s e

/-- `is_empty` converges with state. -/
theorem is_empty_convergent (s₁ s₂ : concrete_st) :
    eq s₁ s₂ → (is_empty s₁ ↔ is_empty s₂) := by
  intro h_eq; unfold eq at h_eq; subst h_eq; rfl

/-- The initial state is empty. -/
theorem is_empty_init : is_empty init_st := by
  intro e ⟨ts, v, h_mem⟩
  simp [init_st] at h_mem

/-- Propositional spec for **acquired**: `v = Σ amount` over inc
records `(_, e, amount)` in `Prod.snd s`. Same flat-observation
rationale as the CRDT side. -/
def is_acquired (s : concrete_st) (e : ℕ) (v : ℤ) : Prop :=
  ∃ l : List (ℕ × ℤ),
    l.Nodup ∧
    (∀ p : ℕ × ℤ, p ∈ l ↔ (Prod.snd s) (p.1, e, p.2) = true) ∧
    v = (l.map Prod.snd).sum

/-- `is_acquired` converges with state. -/
theorem is_acquired_convergent (s₁ s₂ : concrete_st) (e : ℕ) (v : ℤ) :
    eq s₁ s₂ → (is_acquired s₁ e v ↔ is_acquired s₂ e v) := by
  intro h_eq; unfold eq at h_eq; subst h_eq; rfl

/-- **Priority.** `priority(e) = innate(e) + acquired(e)`. -/
def is_priority (s : concrete_st) (e : ℕ) (p : ℤ) : Prop :=
  ∃ ts x v,
    is_innate_record s e ts x ∧ is_acquired s e v ∧ p = (x : ℤ) + v

/-- `is_priority` converges with state. -/
theorem is_priority_convergent (s₁ s₂ : concrete_st) (e : ℕ) (p : ℤ) :
    eq s₁ s₂ → (is_priority s₁ e p ↔ is_priority s₂ e p) := by
  intro h_eq; unfold eq at h_eq; subst h_eq; rfl

/-- **Get-max.** Element `e_max` has the highest priority among all
live elements. -/
def is_get_max (s : concrete_st) (e_max : ℕ) (p_max : ℤ) : Prop :=
  is_priority s e_max p_max ∧
  ∀ e' p', is_priority s e' p' → p' ≤ p_max

/-- `is_get_max` converges with state. -/
theorem is_get_max_convergent (s₁ s₂ : concrete_st) (e : ℕ) (p : ℤ) :
    eq s₁ s₂ → (is_get_max s₁ e p ↔ is_get_max s₂ e p) := by
  intro h_eq; unfold eq at h_eq; subst h_eq; rfl

/-- **Inc creates an inc-record.** Sanity check that `Inc e amount`
adds `(ts, e, amount)` to the I component. -/
theorem inc_creates_inc_record
    (s : concrete_st) (e : ℕ) (amount : ℤ) (ts rid : ℕ) :
    (Prod.snd (do_ s (ts, rid, app_op_t.Inc e amount))) (ts, e, amount) = true := by
  simp [do_]

/-- **Inc increases acquired by `amount` (headline intent).** Same
shape as the CRDT version: cons the new inc-record to the witness
list. The MRDT's I-component lookup uses tuple ordering
`(inc_ts, elem, amount)`, so `(p.1, e, p.2)` is the lookup key. -/
theorem inc_increases_acquired
    (s : concrete_st) (e : ℕ) (amount : ℤ) (ts rid : ℕ)
    (h_fresh : (Prod.snd s) (ts, e, amount) = false) (v : ℤ) :
    is_acquired s e v →
    is_acquired (do_ s (ts, rid, app_op_t.Inc e amount)) e (v + amount) := by
  rintro ⟨l, h_nodup, h_bij, rfl⟩
  refine ⟨(ts, amount) :: l, ?_, ?_, ?_⟩
  · rw [List.nodup_cons]
    refine ⟨fun h_in => ?_, h_nodup⟩
    have := (h_bij (ts, amount)).mp h_in
    rw [h_fresh] at this
    exact Bool.noConfusion this
  · intro p
    rw [List.mem_cons]
    constructor
    · rintro (rfl | h_in)
      · simp [do_]
      · simp [do_, (h_bij p).mp h_in]
    · intro h_new
      simp [do_] at h_new
      rcases h_new with h_orig | ⟨h_t, h_a⟩
      · right; exact (h_bij p).mpr h_orig
      · left; exact Prod.ext h_t h_a
  · simp [List.map_cons, List.sum_cons]
    ring
