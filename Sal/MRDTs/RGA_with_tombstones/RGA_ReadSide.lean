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

/-! # RGA MRDT: read-side projection and intent-preservation theorems

MRDT counterpart to `Sal/CRDTs/RGA_ReadSide.lean`. The 24 RA-linearizability
VCs in `Replicated_Growable_Array_MRDT.lean` prove convergence of the
state under three-way merge. They say nothing about whether the visible
sequence the user reads is the canonical RGA traversal.

This file fills that gap with a minimum-viable read-side layer:

1. **Per-id read.** `readSeq_visible s id ele` is a relational read,
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

/-- Is the OpId `id` currently visible in state `s`, there exists an
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

/-! ## Delete preserves the visible order (tombstoned RGA)

The **positive contrast** to the tombstone-free RGA. That variant reorders
survivors on a *single* delete: splicing a deleted node physically out rehomes
its children, which then re-sort among their new siblings by the newest-first
tiebreak, a sequential-spec violation certified invisibly by our
RA-linearizability (`RGA_TF_SPOT.tombstone_free_violates_delete_order`,
`Sal/MRDTs/RGA_Rehoming/RGA_Tombstone_Free_SPOT.lean`; open question `oq:linspec`).

The tombstoned RGA cannot exhibit this. Its visible order `visible_lt` is
defined entirely through `after_of`, which reads only the insert records
`Prod.fst s`. A `Remove` touches only the tombstone set `Prod.snd s`:
`do_ s (_,_,.Remove x) = (Prod.fst s, add x (Prod.snd s))`
(`RGA_MRDT.lean:101`). Hence `after_of`, and with it the entire order relation,
is *invariant* under `Remove`: deletion flips a node's liveness (`visible`)
but never moves any survivor. The dead node stays put as a position holder;
nothing rehomes. `remove_preserves_visible_lt` is the machine-checked statement,
a genuine `↔` (its non-vacuity is witnessed just below). -/

/-- `after_of` reads only `Prod.fst`, and `Remove` leaves `Prod.fst` untouched,
so the direct-after relation is unchanged by a `Remove`. -/
theorem remove_preserves_after_of (s : concrete_st) (t r x c p : ℕ) :
    after_of (do_ s (t, r, app_op_t.Remove x)) c p ↔ after_of s c p := by
  have hfst : (do_ s (t, r, app_op_t.Remove x)).1 = s.1 := rfl
  simp only [after_of, hfst]

/-- The reflexive-transitive closure `afters_reach` is built only from
`after_of`, so it too is invariant under a `Remove`. -/
theorem remove_preserves_afters_reach (s : concrete_st) (t r x a b : ℕ) :
    afters_reach (do_ s (t, r, app_op_t.Remove x)) a b ↔ afters_reach s a b := by
  constructor
  · intro h
    induction h with
    | refl c => exact afters_reach.refl c
    | step hstep _ ih =>
        exact afters_reach.step ((remove_preserves_after_of s t r x _ _).mp hstep) ih
  · intro h
    induction h with
    | refl c => exact afters_reach.refl c
    | step hstep _ ih =>
        exact afters_reach.step ((remove_preserves_after_of s t r x _ _).mpr hstep) ih

/-- **Delete preserves the visible order (tombstoned RGA).** For every pair of
identities `a`, `b`, applying a `Remove x` leaves the visible-order relation
`visible_lt` on them exactly as it was. This is the tombstoned RGA's
delete-order-preservation, the property the tombstone-free RGA *violates*
(`tombstone_free_violates_delete_order`). The proof replays each `visible_lt`
constructor across the `after_of`/`afters_reach` invariance established above; no
node is rehomed, because the tombstone lives outside the substrate `visible_lt`
reads. -/
theorem remove_preserves_visible_lt (s : concrete_st) (t r x a b : ℕ) :
    visible_lt (do_ s (t, r, app_op_t.Remove x)) a b ↔ visible_lt s a b := by
  constructor
  · intro h
    induction h with
    | parent_child hp =>
        exact visible_lt.parent_child ((remove_preserves_after_of s t r x _ _).mp hp)
    | sibling hp1 hp2 hne hgt =>
        exact visible_lt.sibling ((remove_preserves_after_of s t r x _ _).mp hp1)
          ((remove_preserves_after_of s t r x _ _).mp hp2) hne hgt
    | left_descendant_of_sibling hp1 hp2 hne hgt hreach hdne =>
        exact visible_lt.left_descendant_of_sibling
          ((remove_preserves_after_of s t r x _ _).mp hp1)
          ((remove_preserves_after_of s t r x _ _).mp hp2) hne hgt
          ((remove_preserves_afters_reach s t r x _ _).mp hreach) hdne
    | trans _ _ ih1 ih2 => exact visible_lt.trans ih1 ih2
  · intro h
    induction h with
    | parent_child hp =>
        exact visible_lt.parent_child ((remove_preserves_after_of s t r x _ _).mpr hp)
    | sibling hp1 hp2 hne hgt =>
        exact visible_lt.sibling ((remove_preserves_after_of s t r x _ _).mpr hp1)
          ((remove_preserves_after_of s t r x _ _).mpr hp2) hne hgt
    | left_descendant_of_sibling hp1 hp2 hne hgt hreach hdne =>
        exact visible_lt.left_descendant_of_sibling
          ((remove_preserves_after_of s t r x _ _).mpr hp1)
          ((remove_preserves_after_of s t r x _ _).mpr hp2) hne hgt
          ((remove_preserves_afters_reach s t r x _ _).mpr hreach) hdne
    | trans _ _ ih1 ih2 => exact visible_lt.trans ih1 ih2

/-- Non-vacuity of `remove_preserves_visible_lt`: `visible_lt` is inhabited on a
small state, and the equivalence transports a *real* derivation across a
`Remove`. Here `σ` inserts `A` (id `1`) after the root and `B` (id `2`) after
`A`; `visible_lt σ 1 2` holds by `parent_child`, and it survives removing the
unrelated id `1`. -/
example :
    visible_lt
      (do_ (do_ (do_ init_st (1, 0, app_op_t.Add_after 0 65))
                (2, 0, app_op_t.Add_after 1 66))
           (3, 0, app_op_t.Remove 1)) 1 2 := by
  rw [remove_preserves_visible_lt]
  exact visible_lt.parent_child ⟨66, by decide⟩

section AxiomAudit
#print axioms remove_preserves_visible_lt
end AxiomAudit
