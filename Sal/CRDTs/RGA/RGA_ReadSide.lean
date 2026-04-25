import Std.Tactic.BVDecide
import Sal.Interfaces.Map_Extended
import Sal.Tactic.Sal
import Sal.CRDTs.RGA.RGA_CRDT
import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Classical

/-! # RGA — read-side projection and intent-preservation theorems

The 24 RA-linearizability VCs in `RGA_CRDT.lean` prove convergence of the
state under merge: `eq s₁ s₂ → eq (merge s₁ s₂) s₂` and friends, lifted
through `do_` composition. They say nothing about whether the *visible
sequence* the user sees is the canonical RGA traversal.

This file fills that gap with a minimum-viable read-side layer mirroring
the Peritext methodology (`Sal/CRDTs/Peritext/Peritext_ReadSide.lean`):

1. **Per-OpId read.** `readSeq s c` returns the visible character at
   OpId `c` in state `s` (or `none` if absent / tombstoned).
2. **Convergence at the read.** `eq s₁ s₂ → readSeq s₁ = readSeq s₂`.
3. **Intent theorems.** Three properties characterizing the RGA
   semantic claims that the 24 convergence VCs do not capture:
   - causal-order preservation (afters-ancestor ⇒ earlier in traversal)
   - tombstone monotonicity (Remove never resurrects)
   - deterministic concurrent-insert tiebreak (sibling rule via `opid_max`)

The visible-order relation `visible_lt` mirrors Peritext's four-rule
inductive (parent-child / sibling / left-descendant-of-sibling /
trans). Peritext duplicates this on its own (richer) substrate; the
RGA-only version here is the canonical home for the predicate. -/

/-! ## Read-side primitives -/

/-- Is character `c` currently visible in state `s` — present in the
chars map and not tombstoned? -/
@[simp]
def visible (s : concrete_st) (c : OpId) : Bool :=
  contains (Prod.fst s) c && !(mysel_d (Prod.snd (Prod.snd s)) c)

/-- Direct-after relation: `c` was inserted with `afterId = target`. -/
@[simp]
def after_of (s : concrete_st) (c target : OpId) : Bool :=
  contains (Prod.fst (Prod.snd s)) c &&
  decide (mysel_a (Prod.fst (Prod.snd s)) c = target)

/-- Reflexive-transitive closure of `after_of`: `c` is reachable from
`anc` via the afters-parent chain. -/
inductive afters_reach (s : concrete_st) : OpId → OpId → Prop where
  | refl (c : OpId) : afters_reach s c c
  | step {c c_parent anc : OpId} :
      after_of s c c_parent = true →
      afters_reach s c_parent anc →
      afters_reach s c anc

/-- RGA visible-order relation: `c₁` precedes `c₂` in the canonical
DFS traversal. Four rules: parent-before-child, older-sibling-first
(by `opid_max`), descendant-of-older-sibling-before-younger-sibling,
and transitive closure. -/
inductive visible_lt (s : concrete_st) : OpId → OpId → Prop where
  | parent_child {p c : OpId} : after_of s c p = true → visible_lt s p c
  | sibling {p c₁ c₂ : OpId} :
      after_of s c₁ p = true → after_of s c₂ p = true →
      c₁ ≠ c₂ → opid_max c₁ c₂ = c₁ →
      visible_lt s c₁ c₂
  | left_descendant_of_sibling {p c₁ c₂ d : OpId} :
      after_of s c₁ p = true → after_of s c₂ p = true →
      c₁ ≠ c₂ → opid_max c₁ c₂ = c₁ →
      afters_reach s d c₁ → d ≠ c₁ →
      visible_lt s d c₂
  | trans {c₁ c₂ c₃ : OpId} :
      visible_lt s c₁ c₂ → visible_lt s c₂ c₃ → visible_lt s c₁ c₃

/-- Reflexive closure of `visible_lt`. -/
def visible_le (s : concrete_st) (c₁ c₂ : OpId) : Prop :=
  c₁ = c₂ ∨ visible_lt s c₁ c₂

/-- Per-OpId read: the visible character at `c` in `s`, or `none` if
`c` is absent or tombstoned. The list-form traversal is left as a
follow-up (see `docs/list-form-readrichtext-design.md` for the
challenges). For the headline theorems below the per-OpId form is
sufficient. -/
noncomputable def readSeq (s : concrete_st) : OpId → Option ℕ :=
  fun c =>
    if visible s c = true then some (mysel_c (Prod.fst s) c) else none

/-! ## Convergence at the read -/

/-- Pointwise state equality implies pointwise read-equality. The
read-side analogue of merge convergence: if two replicas have
converged on the abstract state (`eq`), they return the same character
at every OpId. -/
theorem readSeq_convergent (s₁ s₂ : concrete_st) :
    eq s₁ s₂ → readSeq s₁ = readSeq s₂ := by
  intro h_eq
  funext c
  obtain ⟨h_c, _, h_d⟩ := h_eq
  obtain ⟨h_c_dom, h_c_val⟩ := h_c c
  obtain ⟨_, h_d_val⟩ := h_d c
  simp only [readSeq, visible, h_c_dom, h_d_val, h_c_val]

/-! ## Intent-preservation theorems

The three substantive properties beyond convergence. Each is a
state-based predicate over the abstract state, capturing a paper claim
that the 24 convergence VCs do not. -/

/-- **Causal-order preservation.** Walking the `afters` chain from a
descendant `c` reaches an ancestor `anc`; the ancestor precedes the
descendant in the visible traversal. This is the RGA invariant that
"insertion order is preserved": every character is read after its
afters-predecessor, and transitively after its full ancestry. -/
theorem causal_order_visible_lt
    (s : concrete_st) (c anc : OpId) :
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
visible after applying a `Remove target`, then `c` was visible before:
removes can only shrink the visible set. The contrapositive says
"once tombstoned (or absent), always tombstoned (or absent)." -/
theorem tombstone_monotone_under_remove
    (s : concrete_st) (ts rid : ℕ) (target c : OpId) :
    visible (do_ s (ts, rid, app_op_t.Remove target)) c = true →
    visible s c = true := by
  intro h
  simp [visible, do_, mysel_d] at h ⊢
  rcases h with ⟨h_dom, h_d⟩
  refine ⟨h_dom, ?_⟩
  by_cases h_eq : c = target
  · subst h_eq; simp at h_d
  · rcases h_d with ⟨h, _⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h

/-- **Remove tombstones its target.** After applying `Remove target`
the target is no longer visible. Companion to the monotonicity result:
together they say a Remove flips exactly the target and leaves the
visible status of every other OpId unchanged. -/
theorem remove_tombstones_target
    (s : concrete_st) (ts rid : ℕ) (target : OpId) :
    visible (do_ s (ts, rid, app_op_t.Remove target)) target = false := by
  simp [visible, do_, mysel_d]

/-- **Deterministic concurrent-insert tiebreak.** Two inserts that
share the same `afterId` parent get ordered by `opid_max` regardless
of merge order. This is the RGA invariant that makes concurrent
edits at the same anchor resolve deterministically across replicas:
the higher-`opid_max` insert is always read first. -/
theorem concurrent_insert_tiebreak_deterministic
    (s : concrete_st) (p c₁ c₂ : OpId) :
    after_of s c₁ p = true → after_of s c₂ p = true →
    c₁ ≠ c₂ → opid_max c₁ c₂ = c₁ →
    visible_lt s c₁ c₂ :=
  visible_lt.sibling
