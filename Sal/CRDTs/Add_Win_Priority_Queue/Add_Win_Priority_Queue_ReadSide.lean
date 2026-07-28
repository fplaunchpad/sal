import Std.Tactic.BVDecide
import Sal.Interfaces.Set_Extended
import Sal.Interfaces.Map_Extended
import Sal.Tactic.Sal
import Sal.CRDTs.Add_Win_Priority_Queue.Add_Win_Priority_Queue_CRDT
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

/-! # Add-Win Priority Queue (CRDT): read-side projection

The 24 RA-linearizability VCs in `Add_Win_Priority_Queue_CRDT.lean`
prove that the state `(A, I, R)` converges under merge. They say
nothing about whether the *queries* the user runs against that state
behave according to the paper:

  - `lookup(e)`: is element `e` live (has at least one un-tombstoned
    add record)?
  - `innate(e)`: the LWW innate value (max over live add records'
    `add_ts`).
  - `acquired(e)`: sum of increment amounts for `e`.
  - `priority(e)`: `innate + acquired`.

This file lifts the first two (`lookup` and the LWW innate property)
into Lean and proves three intent theorems mirroring the Peritext
methodology. `acquired`, `priority`, `get_max`, and `is_empty` are out
of scope.

**Faithfulness caveat: read `docs/aw-crpq-vs-paper.md`.** The paper
resolves the acquired value via **Most-Change-Win** (Alg 2 line 8 +
§3.3.2): the inc-field of the live record with maximum
change-magnitude `count`. The upstream `Add_Win_Priority_Queue_CRDT.lean`
docstring informally describes acquired as `Σ over I records`, which
is neither the paper's MCW nor expressible in our split state shape
(no per-record `count` field). The docs file enumerates this and
the other state-shape divergences. The theorems here cover only the
parts that are paper-faithful in our state model, `lookup`, LWW
innate, and the Add-Wins headline.

Reference: Zhang, Ouyang, Huang, Ma. "Conflict-free Replicated
Priority Queue: Design, Verification and Evaluation." Internetware
2023. ACM 10.1145/3609437.3609452. -/

/-! ## Read-side primitives -/

/-- **Lookup.** Element `e` is live iff there is an add record for it
that has not been tombstoned. Translated from
`Add_Win_Priority_Queue_CRDT.lean:53`. -/
def lookup (s : concrete_st) (e : ℕ) : Prop :=
  ∃ ts : ℕ,
    contains (Prod.fst s) (e, ts) = true ∧
    (Prod.snd (Prod.snd s)) (e, ts) = false

/-- **Innate-record predicate.** `(ts, v)` is the LWW innate record
for element `e` in state `s`: it is a live add record with value `v`,
and no live add record for `e` has a strictly larger `add_ts`. -/
def is_innate_record (s : concrete_st) (e ts v : ℕ) : Prop :=
  contains (Prod.fst s) (e, ts) = true ∧
  (Prod.snd (Prod.snd s)) (e, ts) = false ∧
  mysel (Prod.fst s) (e, ts) = v ∧
  ∀ ts', ts' > ts →
    ¬ (contains (Prod.fst s) (e, ts') = true ∧
       (Prod.snd (Prod.snd s)) (e, ts') = false)

/-! ## Convergence at the read -/

/-- Pointwise state equality implies that lookup agrees on every
element. The read-side analogue of merge convergence. -/
theorem lookup_convergent (s₁ s₂ : concrete_st) (e : ℕ) :
    eq s₁ s₂ → (lookup s₁ e ↔ lookup s₂ e) := by
  intro h_eq
  obtain ⟨h_A, _, h_R⟩ := h_eq
  unfold lookup
  constructor
  · rintro ⟨ts, h_dom, h_R_false⟩
    refine ⟨ts, ?_, ?_⟩
    · exact ((h_A (e, ts)).1.symm.trans h_dom)
    · exact ((h_R (e, ts)).symm.trans h_R_false)
  · rintro ⟨ts, h_dom, h_R_false⟩
    refine ⟨ts, ?_, ?_⟩
    · exact ((h_A (e, ts)).1.trans h_dom)
    · exact ((h_R (e, ts)).trans h_R_false)

/-- Pointwise state equality lifts to `is_innate_record`. -/
theorem is_innate_record_convergent
    (s₁ s₂ : concrete_st) (e ts v : ℕ) :
    eq s₁ s₂ → (is_innate_record s₁ e ts v ↔ is_innate_record s₂ e ts v) := by
  intro h_eq
  obtain ⟨h_A, _, h_R⟩ := h_eq
  unfold is_innate_record
  have h_dom : ∀ k, contains (Prod.fst s₁) k = contains (Prod.fst s₂) k :=
    fun k => (h_A k).1
  have h_val : ∀ k, mysel (Prod.fst s₁) k = mysel (Prod.fst s₂) k :=
    fun k => (h_A k).2
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(h_dom (e, ts)).symm.trans h1,
            (h_R (e, ts)).symm.trans h2,
            (h_val (e, ts)).symm.trans h3, ?_⟩
    intro ts' h_gt ⟨h5, h6⟩
    exact h4 ts' h_gt ⟨(h_dom (e, ts')).trans h5, (h_R (e, ts')).trans h6⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(h_dom (e, ts)).trans h1,
            (h_R (e, ts)).trans h2,
            (h_val (e, ts)).trans h3, ?_⟩
    intro ts' h_gt ⟨h5, h6⟩
    exact h4 ts' h_gt ⟨(h_dom (e, ts')).symm.trans h5, (h_R (e, ts')).symm.trans h6⟩

/-! ## Intent-preservation theorems -/

/-- **Add-wins over concurrent Rmv (headline).** Starting from any
state, applying `Add e v` at `ts1` and then `Rmv e D` whose snapshot
`D` does not include `(e, ts1)`, the state-based stand-in for "the
Add was concurrent with the Rmv", leaves the element live.

The premise `D (e, ts1) = false` captures the paper's prepare-time
snapshot: `D` is the set of records visible at the Rmv's originating
replica, so an Add at `ts1` not in `D` was either concurrent or
posterior to that snapshot, and survives the merge. -/
theorem add_wins_over_concurrent_rmv
    (s : concrete_st) (e v ts1 rid1 ts2 rid2 : ℕ) (D : set (ℕ × ℕ)) :
    contains (Prod.fst s) (e, ts1) = false →  -- ts1 fresh in `s`
    (Prod.snd (Prod.snd s)) (e, ts1) = false →  -- not pre-tombstoned
    D (e, ts1) = false →                          -- snapshot misses Add
    lookup
      (do_ (do_ s (ts1, rid1, app_op_t.Add e v))
           (ts2, rid2, app_op_t.Rmv e D))
      e := by
  intro _ h_pre_R h_not_in_D
  refine ⟨ts1, ?_, ?_⟩
  · simp [do_]
  · simp [do_, h_pre_R, h_not_in_D]

/-- **Lookup after Add.** A fresh `Add e v` immediately makes `e`
live: applying the op writes `(e, ts)` into `A` and leaves `R`
untouched, so `lookup` finds `(e, ts)` as a live witness. -/
theorem lookup_after_add
    (s : concrete_st) (e v ts rid : ℕ) :
    (Prod.snd (Prod.snd s)) (e, ts) = false →
    lookup (do_ s (ts, rid, app_op_t.Add e v)) e := by
  intro h_R
  refine ⟨ts, ?_, ?_⟩
  · simp [do_]
  · simp [do_, h_R]

/-- **Innate is LWW (uniqueness of the max-`ts` live record).** At
most one `(ts, v)` is the innate record for any element in any
state. Two innate records would each forbid the other's `ts`, so
they must coincide; equal `ts` then forces equal `v` via the
LWW/`mysel` selector. -/
theorem innate_record_unique
    (s : concrete_st) (e ts1 ts2 v1 v2 : ℕ) :
    is_innate_record s e ts1 v1 →
    is_innate_record s e ts2 v2 →
    ts1 = ts2 ∧ v1 = v2 := by
  intro h1 h2
  obtain ⟨h1_dom, h1_R, h1_v, h1_max⟩ := h1
  obtain ⟨h2_dom, h2_R, h2_v, h2_max⟩ := h2
  have h_ts : ts1 = ts2 := by
    rcases lt_trichotomy ts1 ts2 with h | h | h
    · exact absurd ⟨h2_dom, h2_R⟩ (h1_max ts2 h)
    · exact h
    · exact absurd ⟨h1_dom, h1_R⟩ (h2_max ts1 h)
  refine ⟨h_ts, ?_⟩
  subst h_ts
  exact h1_v.symm.trans h2_v

/-! ## Closing the gap: is_empty, acquired, priority, get_max

These complete the paper's query set (§2.2 and Algorithm 1: `is_empty`,
`lookup`, `get_pri`, `get_max`). The `acquired` resolution uses the
flat-observation simplification documented in
`docs/aw-crpq-vs-paper.md`: in our state model every Inc record for
element `e` applies to every live add-record for `e`, so the paper's
Most-Change-Win (Alg 2 line 8) collapses to summation over the
matching inc records. Each query is defined propositionally via a
list-witness so we do not need to expose Mathlib's `Finset` machinery
in our state model, the codebase deliberately avoids it to keep
`grind` and `aesop` effective on the convergence VCs. -/

/-- **Empty.** No element is currently live. Paper §2.2 `is_empty()`. -/
def is_empty (s : concrete_st) : Prop := ∀ e : ℕ, ¬ lookup s e

/-- `is_empty` converges with state. -/
theorem is_empty_convergent (s₁ s₂ : concrete_st) :
    eq s₁ s₂ → (is_empty s₁ ↔ is_empty s₂) := by
  intro h_eq
  unfold is_empty
  refine ⟨fun h e h_lk => h e ?_, fun h e h_lk => h e ?_⟩
  · exact (lookup_convergent s₁ s₂ e h_eq).mpr h_lk
  · exact (lookup_convergent s₁ s₂ e h_eq).mp h_lk

/-- The initial state is empty: `init_st`'s A component is `const_on
empty 0`, so no `(e, ts)` key is contained, and `lookup` finds no
witness. -/
theorem is_empty_init : is_empty init_st := by
  intro e ⟨ts, h_dom, _⟩
  simp [init_st] at h_dom

/-- Propositional spec for the **acquired** value of element `e`:
`v = Σ amount` over all `(e, _, amount)` records currently in `I`.
The witness list `l` enumerates the `(inc_ts, amount)` pairs whose
matching triple sits in the I-component.

**Faithfulness to paper's MCW.** In our flattened state, every live
add-record for `e` "observes" every inc-record for `e` (there is no
per-record observation set). Paper's MCW selects the record with
maximum accumulated change-magnitude `count`; under the
flat-observation assumption, every live record has the same `count`
and the same accumulated `inc`, so MCW collapses to "inc-field of
any live record" = `Σ amount`. See `docs/aw-crpq-vs-paper.md`. -/
def is_acquired (s : concrete_st) (e : ℕ) (v : ℤ) : Prop :=
  ∃ l : List (ℕ × ℤ),
    l.Nodup ∧
    (∀ p : ℕ × ℤ, p ∈ l ↔ (Prod.fst (Prod.snd s)) (e, p.1, p.2) = true) ∧
    v = (l.map Prod.snd).sum

/-- `is_acquired` converges with state. -/
theorem is_acquired_convergent (s₁ s₂ : concrete_st) (e : ℕ) (v : ℤ) :
    eq s₁ s₂ → (is_acquired s₁ e v ↔ is_acquired s₂ e v) := by
  intro h_eq
  obtain ⟨_, h_I, _⟩ := h_eq
  unfold is_acquired
  simp_rw [show ∀ p : ℕ × ℤ,
              (Prod.fst (Prod.snd s₁)) (e, p.1, p.2) =
                (Prod.fst (Prod.snd s₂)) (e, p.1, p.2)
            from fun p => h_I (e, p.1, p.2)]

/-- **Priority.** Paper Alg 2 line 9: `priority(e) = innate(e) + acquired(e)`.
The innate value `x` comes from the LWW selector (Alg 2 line 7);
`v` is the acquired value (line 8). -/
def is_priority (s : concrete_st) (e : ℕ) (p : ℤ) : Prop :=
  ∃ ts x v,
    is_innate_record s e ts x ∧ is_acquired s e v ∧ p = (x : ℤ) + v

/-- `is_priority` converges with state. -/
theorem is_priority_convergent (s₁ s₂ : concrete_st) (e : ℕ) (p : ℤ) :
    eq s₁ s₂ → (is_priority s₁ e p ↔ is_priority s₂ e p) := by
  intro h_eq
  unfold is_priority
  refine ⟨fun ⟨ts, x, v, h1, h2, h3⟩ => ⟨ts, x, v, ?_, ?_, h3⟩,
          fun ⟨ts, x, v, h1, h2, h3⟩ => ⟨ts, x, v, ?_, ?_, h3⟩⟩
  · exact (is_innate_record_convergent s₁ s₂ e ts x h_eq).mp h1
  · exact (is_acquired_convergent s₁ s₂ e v h_eq).mp h2
  · exact (is_innate_record_convergent s₁ s₂ e ts x h_eq).mpr h1
  · exact (is_acquired_convergent s₁ s₂ e v h_eq).mpr h2

/-- **Get-max.** Element `e_max` has the highest priority among all
live elements. Paper §2.2 `get_max()`. -/
def is_get_max (s : concrete_st) (e_max : ℕ) (p_max : ℤ) : Prop :=
  is_priority s e_max p_max ∧
  ∀ e' p', is_priority s e' p' → p' ≤ p_max

/-- `is_get_max` converges with state. -/
theorem is_get_max_convergent (s₁ s₂ : concrete_st) (e : ℕ) (p : ℤ) :
    eq s₁ s₂ → (is_get_max s₁ e p ↔ is_get_max s₂ e p) := by
  intro h_eq
  unfold is_get_max
  refine ⟨fun ⟨h_p, h_max⟩ => ⟨?_, fun e' p' h_p' => h_max e' p' ?_⟩,
          fun ⟨h_p, h_max⟩ => ⟨?_, fun e' p' h_p' => h_max e' p' ?_⟩⟩
  · exact (is_priority_convergent s₁ s₂ e p h_eq).mp h_p
  · exact (is_priority_convergent s₁ s₂ e' p' h_eq).mpr h_p'
  · exact (is_priority_convergent s₁ s₂ e p h_eq).mpr h_p
  · exact (is_priority_convergent s₁ s₂ e' p' h_eq).mp h_p'

/-- **Inc creates an inc-record.** Applying `Inc e amount` puts
`(e, ts, amount)` into the I component, regardless of prior state.
Sanity-check tying `Inc` to its observable effect. -/
theorem inc_creates_inc_record
    (s : concrete_st) (e : ℕ) (amount : ℤ) (ts rid : ℕ) :
    (Prod.fst (Prod.snd (do_ s (ts, rid, app_op_t.Inc e amount))))
        (e, ts, amount) = true := by
  simp [do_]

/-- **Inc increases acquired by `amount` (headline intent).** Given a
state `s` whose inc-component has no prior `(e, ts, amount)` triple
(`distinct_ops` guarantees freshness of the new inc's `ts`), if `v`
is the acquired value of `e` in `s`, then the post-`Inc` state has
acquired value `v + amount` for `e`.

Proof: the witness list for the post-state is the pre-state's witness
list `cons` `(ts, amount)`. Freshness of `(e, ts, amount)` in the
pre-state's I gives `Nodup`; the bijection follows from boolean
distributivity over the union form of `do_`'s effect; the sum
becomes `amount + (old sum)` via `List.sum_cons`. -/
theorem inc_increases_acquired
    (s : concrete_st) (e : ℕ) (amount : ℤ) (ts rid : ℕ)
    (h_fresh : (Prod.fst (Prod.snd s)) (e, ts, amount) = false) (v : ℤ) :
    is_acquired s e v →
    is_acquired (do_ s (ts, rid, app_op_t.Inc e amount)) e (v + amount) := by
  rintro ⟨l, h_nodup, h_bij, rfl⟩
  refine ⟨(ts, amount) :: l, ?_, ?_, ?_⟩
  · -- Nodup of the cons: head is fresh by h_fresh; tail is h_nodup.
    rw [List.nodup_cons]
    refine ⟨fun h_in => ?_, h_nodup⟩
    have := (h_bij (ts, amount)).mp h_in
    rw [h_fresh] at this
    exact Bool.noConfusion this
  · -- Bijection: p ∈ (ts, amount) :: l  ↔  new_I (e, p.1, p.2) = true.
    intro p
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
  · -- Sum: ((ts, amount) :: l).map Prod.snd .sum = (l.map Prod.snd).sum + amount.
    simp [List.map_cons, List.sum_cons]
    ring
