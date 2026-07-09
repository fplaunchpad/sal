import Std.Tactic.BVDecide
import Sal.Interfaces.Set_Extended
import Sal.Tactic.Sal
import Sal.MRDTs.RGA_with_tombstones.RGA_MRDT
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

/-! # RGA MRDT — read-side projection and intent-preservation theorems

MRDT counterpart to `Sal/CRDTs/RGA_ReadSide.lean`. The 24 RA-linearizability
VCs in `Replicated_Growable_Array_MRDT.lean` prove convergence of the
state under three-way merge. They say nothing about whether the visible
sequence the user reads is the canonical RGA traversal.

This file fills that gap with a minimum-viable read-side layer:

1. **Per-id read.** `readSeq_visible s id ele` is a relational read —
   "in state `s`, the visible character at OpId `id` is `ele`". The
   relational form sidesteps the `Classical.choose` ambiguity that an
   `Option`-valued read would carry over a set-of-triples state.
2. **Convergence at the read.** `eq s₁ s₂ → readSeq_visible s₁ … ↔ readSeq_visible s₂ …`.
3. **Three intent theorems** mirroring the CRDT side:
   - causal-order preservation
   - tombstone monotonicity
   - deterministic concurrent-insert tiebreak (here, plain `>` on `ts`,
     since `ts` is globally unique by `distinct_ops`).

The state is `set (ts × (afterId × elem)) × set ts`: insert records and
tombstones. -/

/-! ## Read-side primitives -/

/-- Is the OpId `id` currently visible in state `s` — there exists an
insert record with that `id` and it is not tombstoned? -/
def visible (s : concrete_st) (id : ℕ) : Prop :=
  (∃ r e, mem (id, r, e) (Prod.fst s) = true) ∧ mem id (Prod.snd s) = false

/-- Direct-after relation: `c` was inserted with `afterId = parent`. -/
def after_of (s : concrete_st) (c parent : ℕ) : Prop :=
  ∃ e, mem (c, parent, e) (Prod.fst s) = true

/-- Reflexive-transitive closure of `after_of`. -/
inductive afters_reach (s : concrete_st) : ℕ → ℕ → Prop where
  | refl (c : ℕ) : afters_reach s c c
  | step {c c_parent anc : ℕ} :
      after_of s c c_parent →
      afters_reach s c_parent anc →
      afters_reach s c anc

/-- RGA visible-order on the MRDT substrate. Tiebreaking on direct
siblings uses plain `>` on the unique `ts`, since the MRDT's
`distinct_ops` guarantees globally-unique timestamps. -/
inductive visible_lt (s : concrete_st) : ℕ → ℕ → Prop where
  | parent_child {p c : ℕ} : after_of s c p → visible_lt s p c
  | sibling {p c₁ c₂ : ℕ} :
      after_of s c₁ p → after_of s c₂ p →
      c₁ ≠ c₂ → c₁ > c₂ →
      visible_lt s c₁ c₂
  | left_descendant_of_sibling {p c₁ c₂ d : ℕ} :
      after_of s c₁ p → after_of s c₂ p →
      c₁ ≠ c₂ → c₁ > c₂ →
      afters_reach s d c₁ → d ≠ c₁ →
      visible_lt s d c₂
  | trans {c₁ c₂ c₃ : ℕ} :
      visible_lt s c₁ c₂ → visible_lt s c₂ c₃ → visible_lt s c₁ c₃

/-- Relational per-id read. `readSeq_visible s id ele` holds iff `id`
is visible in `s` and its insert record carries element `ele`. The
relational form is robust to non-uniqueness of `(afterId, elem)`
pairs sharing an `id`; under `distinct_ops` (globally-unique `ts`)
the relation is functional in `ele` for any fixed `id`. -/
def readSeq_visible (s : concrete_st) (id ele : ℕ) : Prop :=
  visible s id ∧ ∃ r, mem (id, r, ele) (Prod.fst s) = true

/-! ## Convergence at the read -/

/-- Pointwise state equality implies pointwise read-equality. Trivial
since `eq` on the MRDT state shape collapses to set equality on each
component (via `equal_intro'`). -/
theorem readSeq_visible_convergent (s₁ s₂ : concrete_st) (id ele : ℕ) :
    eq s₁ s₂ → (readSeq_visible s₁ id ele ↔ readSeq_visible s₂ id ele) := by
  intro h_eq
  obtain ⟨h_inserts, h_tombs⟩ := h_eq
  rw [equal_intro'] at h_inserts h_tombs
  simp [readSeq_visible, visible, h_inserts, h_tombs]

/-! ## Intent-preservation theorems -/

/-- **Causal-order preservation.** Walking the `afters` chain from a
descendant to an ancestor gives a `visible_lt` from ancestor to
descendant. Same proof shape as the CRDT side. -/
theorem causal_order_visible_lt
    (s : concrete_st) (c anc : ℕ) :
    afters_reach s c anc → c ≠ anc → visible_lt s anc c := by
  intro h_reach h_ne
  induction h_reach with
  | refl c => exact absurd rfl h_ne
  | @step c mid anc h_after _ ih =>
    by_cases h_eq : mid = anc
    · subst h_eq
      exact visible_lt.parent_child h_after
    · have h_mid : visible_lt s anc mid := ih h_eq
      have h_c : visible_lt s mid c := visible_lt.parent_child h_after
      exact visible_lt.trans h_mid h_c

/-- **Tombstone monotonicity (remove never resurrects).** If `c` is
visible after applying a `Remove target`, then `c` was visible before.
The MRDT `Remove` adds `target` to the tombstone set; visibility
status of every id other than `target` is preserved. -/
theorem tombstone_monotone_under_remove
    (s : concrete_st) (ts rid : ℕ) (target c : ℕ) :
    visible (do_ s (ts, rid, app_op_t.Remove target)) c → visible s c := by
  intro h
  obtain ⟨h_rec, h_not_tomb⟩ := h
  refine ⟨h_rec, ?_⟩
  -- After Remove target, tombstones = add target old_tombs.
  -- For c ≠ target this leaves c's tombstone bit unchanged; for c = target
  -- the post-state has c tombstoned, contradicting h_not_tomb.
  by_cases h_eq : c = target
  · subst h_eq
    simp [do_] at h_not_tomb
  · simp [do_] at h_not_tomb
    grind

/-- **Remove tombstones its target.** After applying `Remove target`,
`target` is no longer visible. -/
theorem remove_tombstones_target
    (s : concrete_st) (ts rid : ℕ) (target : ℕ) :
    ¬ visible (do_ s (ts, rid, app_op_t.Remove target)) target := by
  intro h
  obtain ⟨_, h_not_tomb⟩ := h
  simp [do_] at h_not_tomb

/-- **Deterministic concurrent-insert tiebreak.** Two inserts that
share the same `afterId` parent get ordered by `>` on `ts` regardless
of merge order. -/
theorem concurrent_insert_tiebreak_deterministic
    (s : concrete_st) (p c₁ c₂ : ℕ) :
    after_of s c₁ p → after_of s c₂ p →
    c₁ ≠ c₂ → c₁ > c₂ →
    visible_lt s c₁ c₂ :=
  visible_lt.sibling
