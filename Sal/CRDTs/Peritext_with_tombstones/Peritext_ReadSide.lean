import Std.Tactic.BVDecide
import Sal.Interfaces.Set_Extended
import Sal.Interfaces.Map_Extended
import Sal.Tactic.Sal
import Mathlib
import Sal.CRDTs.Peritext_with_tombstones.Peritext_CRDT

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Classical

/-! ## Read-side projection and rich-text merge-semantic characterizations

This section goes beyond the 24 state-convergence VCs and captures the
paper's *interesting* merge semantics — the claims that differentiate
Peritext from "a plain RGA with a flat set of formatting ranges":

1. **Expand/contract via anchor sides.** `startSide` / `endSide` decide
   whether a concurrent boundary insert falls inside the mark.
2. **Priority rule.** Add beats Remove; otherwise highest-opId.
3. **Anchors survive tombstones.** Removing an interior char does not
   change the formatting of the rest of the span.

All three are **read-side** properties, so the file defines a
paper-faithful read-side projection (`formatted_visible` /
`readRichText_visible`) built on top of the visible-order predicate
`in_span_visible`. The paper's claims become theorems about those.

### Scope and caveats

- `in_span_visible` uses the RGA visible-order relation `visible_lt`
  (DFS traversal with `opid_max` sibling tie-breaking) as the ordering
  backbone. This matches the paper's §3.3 link-contract semantics
  faithfully; bold-expand past `endId` is not captured (see
  `docs/peritext-vs-paper.md` for the known gap).
- The "concurrent" premise in the Add-beats-Remove characterization
  is rendered in state-based form: both mark ops are present in the
  final state. In an op-based formulation this would be a
  happens-before claim; the state-based stand-in is that delivery
  order cannot be recovered from a merged state, so presence alone
  is the closest observable analogue.
- Block structure, embedded non-text objects, and the open mark-type
  registry remain out of scope (the suite's Peritext port is still
  "text-only").
-/

/-- Accessors for the `MarkOp` tuple `(opId, sId, sSd, eId, eSd, mt, isAdd)`. -/
@[simp] def mark_opId     (m : MarkOp) : OpId := m.1
@[simp] def mark_startId  (m : MarkOp) : OpId := m.2.1
@[simp] def mark_startSide(m : MarkOp) : Bool := m.2.2.1
@[simp] def mark_endId    (m : MarkOp) : OpId := m.2.2.2.1
@[simp] def mark_endSide  (m : MarkOp) : Bool := m.2.2.2.2.1
@[simp] def mark_markType (m : MarkOp) : ℕ    := m.2.2.2.2.2.1
@[simp] def mark_isAdd    (m : MarkOp) : Bool := m.2.2.2.2.2.2

/-- The `marks` component of state. -/
@[simp]
def marks_of (s : concrete_st) : set AnchorAttachment :=
  Prod.snd (Prod.snd (Prod.snd s))

/-- Is a mark op `m` present in state `s`?  A mark op is considered
present iff either of its two canonical anchor attachments
(at `(startId, startSide)` and at `(endId, endSide)`) is in the
marks set. In a well-formed state produced by `do_` + `merge` both
attachments are always added together, so either side suffices. -/
@[simp]
def mark_present (s : concrete_st) (m : MarkOp) : Bool :=
  marks_of s (mark_startId m, mark_startSide m, m) ||
  marks_of s (mark_endId m, mark_endSide m, m)

/-- Is character `c` currently visible in state `s` (present and not
tombstoned)?  Inherits directly from the RGA substrate. -/
@[simp]
def visible (s : concrete_st) (c : OpId) : Bool :=
  contains (Prod.fst s) c && !(mysel_d (Prod.fst (Prod.snd (Prod.snd s))) c)

/-- Direct-after relation on the RGA `afters` map: `c_new` was
inserted with `afterId = target`. This is the observable shape of
"inserted immediately after `target`" from a given replica's view. -/
@[simp]
def after_of (s : concrete_st) (c target : OpId) : Bool :=
  contains (Prod.fst (Prod.snd s)) c &&
  decide (mysel_a (Prod.fst (Prod.snd s)) c = target)

/-- Priority comparison between two mark ops for the *same character
and mark type*. Returns `true` iff `a` wins over `b`.

Paper §4.4: LWW on opId — the highest-opId op wins, regardless of
its `isAdd` bit. -/
@[simp]
def mark_beats (a b : MarkOp) : Bool :=
  decide (opid_max (mark_opId a) (mark_opId b) = mark_opId a)

set_option maxHeartbeats 0

/-! ### Expand/contract at span boundaries

The paper's §3.3 expand/contract distinction is captured by the
paper-faithful visible-order theorems later in this file, not by
`in_span_boundary`:

- **Ex 7 (bold-expand, cross-sibling case):** `ex7_bold_older_sibling_in_span`
  covers the common scenario where a concurrent insert lands in an
  older-sibling subtree of `endId` — the insert is before `endId` in
  visible order and is correctly included in the span.
- **Ex 8 (link-contract):** `ex8_link_descendant_not_in_span_visible_of_wf` (genuine; the `visible_lt_endId` positive is a definitional helper).
  demonstrates that afters-descendants of `endId` come *after* `endId`
  in visible order, and are correctly excluded from `in_span_visible`.
- **Ex 1 (insert-within-span):** `insert_within_span_in_span_visible`
  and `insert_within_span_cross_subtree_in_span` cover the general
  interior-insert case.

Earlier versions of this file had four `expand_contract_*` theorems
stated against `in_span_boundary`. Those theorems were true about the
boundary approximation but its `endSide`/`after_of endId` clause
encodes the opposite of the paper's expand/contract semantics (see
`docs/peritext-vs-paper.md`). They have been removed in favour of the
visible-order theorems above. -/

/-! ## Afters-reachability

Reflexive-transitive closure of `after_of`, used by `visible_lt`'s
`left_descendant_of_sibling` rule and by the insert-monotonicity
lemmas. -/

/-- Reflexive-transitive closure of `after_of`: `c` is reachable from
`anc` by following `after_of` links, i.e. `c` is an afters-descendant
of `anc` in the RGA insertion tree. -/
inductive afters_reach (s : concrete_st) : OpId → OpId → Prop where
  | refl (c : OpId) : afters_reach s c c
  | step {c c_parent anc : OpId} :
      after_of s c c_parent = true →
      afters_reach s c_parent anc →
      afters_reach s c anc

/-! ## RGA visible-order relation

The inductive `visible_lt` captures the RGA traversal order on
characters: c₁ precedes c₂ in the visible sequence iff
`visible_lt s c₁ c₂` holds. The relation is defined by four rules
that together characterize DFS traversal with sibling tie-breaking
by `opid_max`:

1. **`parent_child`** — a character's parent (via `after_of`) is
   visited before it.
2. **`sibling`** — among direct siblings (same `after_of`-parent),
   the one with the higher `opId` (by `opid_max`) is visited first.
3. **`left_descendant_of_sibling`** — any descendant of the older
   sibling is visited before the younger sibling (the older subtree
   is fully consumed before the younger).
4. **`trans`** — transitive closure.

`visible_lt` is the foundation for `in_span_visible` below, which
captures paper-faithful span membership. -/

/-- The "visited before" relation in the RGA traversal of state `s`.

The smallest relation containing: (1) parent-child edges, (2) direct
older-sibling → younger-sibling edges, (3) descendant-of-older-sibling
→ younger-sibling edges (left-subtree-precedes-younger-sibling), and
closed under transitivity. -/
inductive visible_lt (s : concrete_st) : OpId → OpId → Prop where
  /-- A character's parent (via `after_of`) is visited before it. -/
  | parent_child {p c : OpId} : after_of s c p = true → visible_lt s p c
  /-- Among direct siblings (sharing an `after_of`-parent), the one
  with the higher `opId` by `opid_max` is visited first. `c₁ ≠ c₂`
  rules out the degenerate reflexive case. -/
  | sibling {p c₁ c₂ : OpId} :
      after_of s c₁ p = true → after_of s c₂ p = true →
      c₁ ≠ c₂ → opid_max c₁ c₂ = c₁ →
      visible_lt s c₁ c₂
  /-- Any descendant of the older sibling precedes the younger
  sibling in the traversal. "Older" is measured by `opid_max` on
  the direct-child OpIds. -/
  | left_descendant_of_sibling {p c₁ c₂ d : OpId} :
      after_of s c₁ p = true → after_of s c₂ p = true →
      c₁ ≠ c₂ → opid_max c₁ c₂ = c₁ →
      afters_reach s d c₁ → d ≠ c₁ →
      visible_lt s d c₂
  /-- Transitive closure. -/
  | trans {c₁ c₂ c₃ : OpId} :
      visible_lt s c₁ c₂ → visible_lt s c₂ c₃ → visible_lt s c₁ c₃

/-- Reflexive closure: `visible_le s c₁ c₂` iff `c₁ = c₂` or
`c₁` precedes `c₂` in the RGA traversal. -/
def visible_le (s : concrete_st) (c₁ c₂ : OpId) : Prop :=
  c₁ = c₂ ∨ visible_lt s c₁ c₂

/-! ### RGA well-formedness: `wf_afters`

A state is *well-formed* on its afters map iff the induced visible-
order relation `visible_lt` is irreflexive — equivalently, the
afters-parent chain has no cycles. Every state produced by a finite
sequence of `do_` ops starting from `init_st` is well-formed: each
`Insert`'s opId is fresh (by `distinct_ops`), so the afters-parent
chain must terminate rather than loop back. We take this as a
state-level invariant; a preservation proof for `do_` and `merge`
is a deferred follow-up. -/

/-- A Peritext state is well-formed on its afters map iff the induced
visible-order relation is irreflexive. Equivalent to acyclicity of
the afters-parent relation. -/
def wf_afters (s : concrete_st) : Prop :=
  ∀ c, ¬ visible_lt s c c

/-- Under `wf_afters`, `visible_lt` is antisymmetric: no two characters
each precede the other. -/
theorem visible_lt_asymm_of_wf
    (s : concrete_st) (h_wf : wf_afters s) (c₁ c₂ : OpId) :
    visible_lt s c₁ c₂ → ¬ visible_lt s c₂ c₁ :=
  fun h₁₂ h₂₁ => h_wf c₁ (visible_lt.trans h₁₂ h₂₁)

/-- Under `wf_afters`, `visible_le` is antisymmetric. -/
theorem visible_le_antisymm_of_wf
    (s : concrete_st) (h_wf : wf_afters s) (c₁ c₂ : OpId) :
    visible_le s c₁ c₂ → visible_le s c₂ c₁ → c₁ = c₂ := by
  intro h12 h21
  rcases h12 with h12 | h12
  · exact h12
  · rcases h21 with h21 | h21
    · exact h21.symm
    · exact absurd h21 (visible_lt_asymm_of_wf s h_wf _ _ h12)

/-- A multi-hop `afters_reach` gives a `visible_lt` from ancestor
to descendant (the parent-child edge lifted through transitivity). -/
theorem visible_lt_of_afters_reach
    (s : concrete_st) (c anc : OpId) :
    afters_reach s c anc → c ≠ anc → visible_lt s anc c := by
  intro h_reach h_ne
  induction h_reach with
  | refl c => exact absurd rfl h_ne
  | @step c mid anc h_after h_reach' ih =>
    by_cases h_eq : mid = anc
    · -- Single-hop: c is direct child of anc.
      subst h_eq
      exact visible_lt.parent_child h_after
    · -- Multi-hop: anc < mid (by IH) and mid < c (by parent_child), chain.
      have h_mid : visible_lt s anc mid := ih h_eq
      have h_c : visible_lt s mid c := visible_lt.parent_child h_after
      exact visible_lt.trans h_mid h_c

/-- `visible_le` is reflexive. -/
theorem visible_le_refl (s : concrete_st) (c : OpId) : visible_le s c c :=
  Or.inl rfl

/-- `visible_le` is transitive. -/
theorem visible_le_trans
    (s : concrete_st) (c₁ c₂ c₃ : OpId) :
    visible_le s c₁ c₂ → visible_le s c₂ c₃ → visible_le s c₁ c₃ := by
  intro h12 h23
  rcases h12 with h12 | h12
  · subst h12; exact h23
  · rcases h23 with h23 | h23
    · subst h23; exact Or.inr h12
    · exact Or.inr (visible_lt.trans h12 h23)

/-- `visible_lt` composed with `visible_le` on the right still gives
`visible_lt`. -/
theorem visible_lt_of_lt_le
    (s : concrete_st) (c₁ c₂ c₃ : OpId) :
    visible_lt s c₁ c₂ → visible_le s c₂ c₃ → visible_lt s c₁ c₃ := by
  intro h12 h23
  rcases h23 with h23 | h23
  · subst h23; exact h12
  · exact visible_lt.trans h12 h23

/-- `visible_le` composed with `visible_lt` on the right gives
`visible_lt`. -/
theorem visible_lt_of_le_lt
    (s : concrete_st) (c₁ c₂ c₃ : OpId) :
    visible_le s c₁ c₂ → visible_lt s c₂ c₃ → visible_lt s c₁ c₃ := by
  intro h12 h23
  rcases h12 with h12 | h12
  · subst h12; exact h23
  · exact visible_lt.trans h12 h23

/-- **Cross-sibling traversal.** If `c₁_top` and `c₂_top` are direct
siblings under some common `after_of`-parent `p`, with `c₁_top` older
(higher `opid_max`), and `c₁` is a descendant of `c₁_top` while `c₂`
is a descendant of `c₂_top`, then `c₁` precedes `c₂` in the RGA
traversal.

This generalizes `left_descendant_of_sibling`: it lets `c₂` be
anywhere in the younger sibling's subtree, not just `c₂_top` itself.
Proved by chaining `left_descendant_of_sibling` (c₁ < c₂_top) with
`visible_lt_of_afters_reach` (c₂_top < c₂), with the edge case
`c₂ = c₂_top` handled separately. -/
theorem visible_lt_of_cross_sibling
    (s : concrete_st) (p c₁_top c₂_top c₁ c₂ : OpId) :
    after_of s c₁_top p = true →
    after_of s c₂_top p = true →
    c₁_top ≠ c₂_top →
    opid_max c₁_top c₂_top = c₁_top →
    afters_reach s c₁ c₁_top →
    afters_reach s c₂ c₂_top →
    visible_lt s c₁ c₂ := by
  intro h_after_1 h_after_2 h_ne h_order h_reach_1 h_reach_2
  -- Step A: c₁ < c₂_top.
  -- Either c₁ = c₁_top (use sibling rule directly) or c₁ is a strict
  -- descendant (use left_descendant_of_sibling).
  have step_a : visible_lt s c₁ c₂_top := by
    by_cases h_eq1 : c₁ = c₁_top
    · subst h_eq1
      exact visible_lt.sibling h_after_1 h_after_2 h_ne h_order
    · exact visible_lt.left_descendant_of_sibling h_after_1 h_after_2 h_ne
        h_order h_reach_1 h_eq1
  -- Step B: c₂_top ≤ c₂ (equal or ancestor, both give visible_lt or =).
  by_cases h_eq2 : c₂ = c₂_top
  · subst h_eq2; exact step_a
  · have step_b : visible_lt s c₂_top c₂ :=
      visible_lt_of_afters_reach s c₂ c₂_top h_reach_2 h_eq2
    exact visible_lt.trans step_a step_b

/-! ### `in_span_visible` — paper-faithful span membership

The covering predicate that mirrors the paper's semantics. A character
`c` is in the span of mark `m` iff its visible-order position is
bounded by the anchors:

- **Left bound**: `c` is at or after `startId`, with `startSide`
  choosing whether `startId` itself counts.
  `startSide = false` (before): `visible_le startId c` — startId is in.
  `startSide = true`  (after):  `visible_lt startId c` — startId is out.

- **Right bound**: `c` is at or before `endId`, *or* in `endId`'s
  bold-expand region if `endSide = true`:
  `endSide = false` (before, link/contract): `visible_lt c endId` —
  endId and everything after are out.
  `endSide = true`  (after,  bold/expand):  `visible_le c endId ∨
  bold_expand_reach s m c` — endId is in, plus post-endId inserts
  whose afters-chain back to endId consists entirely of
  post-mark-opId characters. See `bold_expand_reach` below.

-/

/-- The bold-expand region past `endId`. A character `c` reaches `endId`
via afters along a chain where every step's character has opId strictly
greater than the mark's own opId — i.e., every intermediate was inserted
after the mark was created.

This captures paper §3.3 bold-expand via opId comparison: sibling
siblings that pre-date the mark block the expand region, while
post-mark siblings are grabbed.

**Example (Ex 7).** State has `..., k, ' ', f, o, x` with bold
`[q..k, endSide=after]`. Later (or concurrently), "brown" is
inserted with `afters = k`. Each brown char has opId > mark.opId.
The afters-chain `brown.last → brown[n-1] → ... → brown.first → k`
goes through only post-mark nodes, so brown is in the expand
region. The space `' '` has opId < mark.opId, so it blocks the
chain — chars reachable only through the space (like `f`) are not
in the expand region. -/
inductive bold_expand_reach (s : concrete_st) (m : MarkOp) : OpId → Prop where
  /-- Base: endId reaches itself. -/
  | at_endId : bold_expand_reach s m (mark_endId m)
  /-- Step: if `c_parent` is in the expand region and `c` is a direct
  afters-child of `c_parent` with `c.opId > mark.opId`, then `c` is
  also in the expand region. -/
  | step {c c_parent : OpId} :
      after_of s c c_parent = true →
      bold_expand_reach s m c_parent →
      opid_max (mark_opId m) c = c →
      bold_expand_reach s m c

def in_span_visible (s : concrete_st) (m : MarkOp) (c : OpId) : Prop :=
  (if mark_startSide m = true then visible_lt s (mark_startId m) c
   else visible_le s (mark_startId m) c) ∧
  (if mark_endSide m = true then
      visible_le s c (mark_endId m) ∨ bold_expand_reach s m c
   else visible_lt s c (mark_endId m))

/-- Sanity: `startId` is in the span when `startSide = false` and
the mark's span is non-degenerate (`startId` comes before `endId`
in visible order per the `endSide` bit). -/
theorem startId_in_span_visible
    (s : concrete_st) (m : MarkOp) :
    mark_startSide m = false →
    (if mark_endSide m = true then visible_le s (mark_startId m) (mark_endId m)
     else visible_lt s (mark_startId m) (mark_endId m)) →
    in_span_visible s m (mark_startId m) := by
  intro h_sSide h_nondeg
  refine ⟨?_, ?_⟩
  · show (if mark_startSide m = true then visible_lt s (mark_startId m) (mark_startId m)
          else visible_le s (mark_startId m) (mark_startId m))
    rw [h_sSide]; simp
    exact visible_le_refl s (mark_startId m)
  · show (if mark_endSide m = true then
            visible_le s (mark_startId m) (mark_endId m) ∨ bold_expand_reach s m (mark_startId m)
          else visible_lt s (mark_startId m) (mark_endId m))
    split_ifs with h_eSide
    · rw [if_pos h_eSide] at h_nondeg; exact Or.inl h_nondeg
    · rw [if_neg h_eSide] at h_nondeg; exact h_nondeg

/-- Sanity: `endId` is in the span when `endSide = true` and
the mark's span is non-degenerate. -/
theorem endId_in_span_visible
    (s : concrete_st) (m : MarkOp) :
    mark_endSide m = true →
    (if mark_startSide m = true then visible_lt s (mark_startId m) (mark_endId m)
     else visible_le s (mark_startId m) (mark_endId m)) →
    in_span_visible s m (mark_endId m) := by
  intro h_eSide h_nondeg
  refine ⟨h_nondeg, ?_⟩
  show (if mark_endSide m = true then
          visible_le s (mark_endId m) (mark_endId m) ∨ bold_expand_reach s m (mark_endId m)
        else visible_lt s (mark_endId m) (mark_endId m))
  rw [h_eSide]; simp
  exact Or.inl (visible_le_refl s (mark_endId m))

/-- **Paper Ex 1 (propagation step, visible-order form).**

If `c_parent` is in the span (paper-faithfully), `c_new` was inserted
immediately after `c_parent` (i.e. `after_of s c_new c_parent = true`),
and the user certifies that `c_new` still stays within the span's
right-side bound (a bound the afters-relation alone can't verify,
since a descendant of `c_parent` could be traversed past `endId` as
a younger sibling of `endId`'s subtree), then `c_new` is in the span.

This is the "insertion within a span inherits the mark" claim. The
right-side bound hypothesis is necessary because a pure afters-chain
could over-approximate — if the caller proves the bound,
`in_span_visible` gives the paper-faithful "c_new is in the span"
conclusion. -/
theorem in_span_visible_propagate
    (s : concrete_st) (m : MarkOp) (c_new c_parent : OpId) :
    in_span_visible s m c_parent →
    after_of s c_new c_parent = true →
    (if mark_endSide m = true then visible_le s c_new (mark_endId m)
     else visible_lt s c_new (mark_endId m)) →
    in_span_visible s m c_new := by
  intro ⟨h_left, _⟩ h_after h_right
  refine ⟨?_, ?_⟩
  · have h_pc : visible_lt s c_parent c_new := visible_lt.parent_child h_after
    split_ifs with h_sSide
    · rw [if_pos h_sSide] at h_left
      exact visible_lt.trans h_left h_pc
    · rw [if_neg h_sSide] at h_left
      exact Or.inr (visible_lt_of_le_lt s (mark_startId m) c_parent c_new h_left h_pc)
  · split_ifs with h_eSide
    · rw [if_pos h_eSide] at h_right; exact Or.inl h_right
    · rw [if_neg h_eSide] at h_right; exact h_right

/-- **Paper Ex 1 (chain form, visible-order).**

Generalizes `in_span_visible_propagate` to arbitrary-length
afters-chains: if `c_start` is in-span-visible, `c` reaches
`c_start` via an `afters_reach` chain, and `c` stays within the
right-side bound, then `c` is in-span-visible.

The right-side bound is the key hypothesis: afters-reachability
alone can't guarantee `c` is before `endId` in visible order (a
distant afters-descendant could be traversed as a younger sibling
past `endId`'s subtree). -/
theorem in_span_visible_of_reach
    (s : concrete_st) (m : MarkOp) (c c_start : OpId) :
    in_span_visible s m c_start →
    afters_reach s c c_start →
    (if mark_endSide m = true then visible_le s c (mark_endId m)
     else visible_lt s c (mark_endId m)) →
    in_span_visible s m c := by
  intro ⟨h_left, _⟩ h_reach h_right
  refine ⟨?_, ?_⟩
  · by_cases h_eq : c = c_start
    · subst h_eq
      exact h_left
    · have h_lt : visible_lt s c_start c :=
        visible_lt_of_afters_reach s c c_start h_reach h_eq
      split_ifs with h_sSide
      · rw [if_pos h_sSide] at h_left
        exact visible_lt.trans h_left h_lt
      · rw [if_neg h_sSide] at h_left
        exact Or.inr (visible_lt_of_le_lt s _ _ _ h_left h_lt)
  · split_ifs with h_eSide
    · rw [if_pos h_eSide] at h_right; exact Or.inl h_right
    · rw [if_neg h_eSide] at h_right; exact h_right

/-! ### Ex 7 / Ex 8 visible-order demonstrations

These theorems exercise the visible-order machinery to replay the
paper's Ex 7 (bold-expand) and Ex 8 (link-no-expand) at the
paper-faithful level. Ex 7's bold-expand behavior is a *theorem*
here because the right-side bound can be derived from the
older-sibling structure. Ex 8's link-no-expand is only a theorem
under the "visible_lt endId c_new → ¬ visible_le c_new endId"
irreflexivity assumption, which we don't have in full generality
(it needs `distinct_ops`-style invariants). Ex 8 is therefore
captured directly by the `if mark_endSide m then visible_le ...
else visible_lt ...` shape of `in_span_visible` — a descendant of
`endId` fails the `visible_le c_new endId` check. -/

/-- **Paper Ex 7 (bold expand) — older sibling of `endId` is in span.**

For a bold-style mark (`startSide = false`, `endSide = false`), a
new char inserted as a direct sibling of `endId` with a higher
`opId` (hence traversed before `endId` as an older sibling) is in
the span, provided the mark's left-side bound is satisfied via
the parent. This captures Ex 7's "text inserted immediately before
`endId` (i.e. between the last bold char and the period) inherits
the bold." -/
theorem ex7_bold_older_sibling_in_span
    (s : concrete_st) (m : MarkOp) (p c_new : OpId) :
    mark_startSide m = false →
    mark_endSide m = false →
    visible_le s (mark_startId m) p →
    after_of s c_new p = true →
    after_of s (mark_endId m) p = true →
    c_new ≠ mark_endId m →
    opid_max c_new (mark_endId m) = c_new →
    c_new ≠ mark_startId m →
    in_span_visible s m c_new := by
  intro h_sSide h_eSide h_left_bound h_after_new h_after_end h_ne h_order _
  refine ⟨?_, ?_⟩
  · -- Left: visible_le startId c_new. startId ≤ p and p < c_new (parent_child).
    split_ifs with h
    · exact absurd h (by rw [h_sSide]; decide)
    · have h_pc : visible_lt s p c_new := visible_lt.parent_child h_after_new
      exact Or.inr (visible_lt_of_le_lt s _ _ _ h_left_bound h_pc)
  · -- Right: visible_lt c_new endId, via sibling rule.
    split_ifs with h
    · exact absurd h (by rw [h_eSide]; decide)
    · exact visible_lt.sibling h_after_new h_after_end h_ne h_order

/-- **Paper Ex 7 (bold-expand) — post-endId inserts in the bold-expand region.**

Under bold-expand semantics (`endSide = true`), a character `c` in
`bold_expand_reach s m c` is in the span, provided the left bound
is also satisfied. This is the "new text inserted at or after the
bold boundary is grabbed by the bold" case of paper §3.3.

`bold_expand_reach` identifies the region past `endId` reachable via
afters-chains through post-mark-opId characters only — pre-mark
siblings block the region, matching the paper's behavior where
older text at the boundary is not re-formatted. -/
theorem bold_expand_in_span_visible
    (s : concrete_st) (m : MarkOp) (c : OpId) :
    mark_endSide m = true →
    (if mark_startSide m = true then visible_lt s (mark_startId m) c
     else visible_le s (mark_startId m) c) →
    bold_expand_reach s m c →
    in_span_visible s m c := by
  intro h_eSide h_left h_reach
  refine ⟨h_left, ?_⟩
  rw [if_pos h_eSide]
  exact Or.inr h_reach

/-- **Paper Ex 8 (link no-expand) — direct descendant of `endId` is not in span.**

For a link-style mark (`endSide = true`), a new char inserted as
a direct `afters`-descendant of `endId` has `visible_lt endId c_new`
(by `parent_child`), so `visible_le c_new endId` requires
`visible_lt c_new endId` — which together with the prior
`visible_lt endId c_new` would give a cycle. Without an
irreflexivity invariant on `visible_lt` (equivalent to asserting
`distinct_ops`-style well-formedness of the RGA state), we can't
derive `¬ in_span_visible` constructively.

Instead, this theorem records the **observable** fact that any
`c_new` with `after_of c_new endId = true` satisfies
`visible_lt endId c_new`, which is precisely the failure condition
for `in_span_visible`'s right-side bound when `endSide = true`.
A user who wants the "not in span" conclusion can combine this
with a well-formedness premise. -/
/-- Constructor-level helper: an afters-descendant of `endId` is `visible_lt`
after it. This is a `visible_lt` constructor applied to its hypothesis
(definitional — it restates how `visible_lt` is built, so it catches no bug);
it is NOT itself the Ex 8 guarantee. The genuine Ex 8 ("link-boundary
insertion does not expand") is the *negative* theorem
`ex8_link_descendant_not_in_span_visible_of_wf`, which uses `wf_afters`
acyclicity to exclude the inserted character from the span. This helper only
feeds that proof. -/
theorem ex8_link_descendant_visible_lt_endId
    (s : concrete_st) (m : MarkOp) (c_new : OpId) :
    after_of s c_new (mark_endId m) = true →
    visible_lt s (mark_endId m) c_new :=
  fun h => visible_lt.parent_child h

/-- **Paper Ex 8 full negation (link case).**

Under link semantics (`endSide = false`), an afters-descendant
`c_new` of `endId` with `c_new ≠ endId` is *not* in the span.

Under bold-expand semantics (`endSide = true`) this is **no longer
universally true** — post-endId descendants with opId > mark.opId
are now in span via `bold_expand_reach`. The theorem is therefore
restricted to the link case here; the bold case is characterized
positively by `bold_expand_in_span_visible` below.

Takes `¬ visible_lt s endId endId` as a hypothesis (acyclicity of
`afters` at `endId`); the `_of_wf` form below discharges this via
the state-level `wf_afters` invariant. -/
theorem ex8_link_descendant_not_in_span_visible
    (s : concrete_st) (m : MarkOp) (c_new : OpId) :
    mark_endSide m = false →
    after_of s c_new (mark_endId m) = true →
    ¬ visible_lt s (mark_endId m) (mark_endId m) →
    ¬ in_span_visible s m c_new := by
  intro h_eSide h_after h_acyclic h_in_span
  have h_lt : visible_lt s (mark_endId m) c_new :=
    ex8_link_descendant_visible_lt_endId s m c_new h_after
  rcases h_in_span with ⟨_, h_right⟩
  rw [if_neg (by rw [h_eSide]; decide)] at h_right
  exact h_acyclic (visible_lt.trans h_lt h_right)

/-- **Paper Ex 8 full negation (link), `wf_afters` form.** -/
theorem ex8_link_descendant_not_in_span_visible_of_wf
    (s : concrete_st) (m : MarkOp) (c_new : OpId) :
    wf_afters s →
    mark_endSide m = false →
    after_of s c_new (mark_endId m) = true →
    ¬ in_span_visible s m c_new := fun h_wf h_eSide h_after =>
  ex8_link_descendant_not_in_span_visible s m c_new h_eSide h_after (h_wf _)

/-! ### Preservation of `visible_lt` / `in_span_visible` under `Insert`

Visible-order relations monotone under fresh-opId insertions. If
`(ts, rid)` is fresh in state `s` (not already an afters-key), then
every existing `visible_lt`/`afters_reach`/`in_span_visible`
relation persists in `do_ s (Insert ch after)` — the new entry
added to `afters` at the fresh key doesn't invalidate any existing
lookup since all existing lookups are at keys ≠ `(ts, rid)`.

This is the monotonicity lemma needed to chain with
`in_span_visible_propagate` for the Ex 1 insert-within-span claim. -/

/-- Key observation: `after_of s c target` agrees with
`after_of (do_ s (ts, rid, Insert ch after)) c target` whenever
`c ≠ (ts, rid)`. -/
theorem after_of_preserved_under_insert
    (s : concrete_st) (ts rid : ℕ) (ch : ℕ) (after c target : OpId) :
    c ≠ (ts, rid) →
    after_of s c target = after_of (do_ s (ts, rid, app_op_t.Insert ch after)) c target := by
  intro h_ne
  simp only [after_of, do_]
  have h_c : contains (Prod.fst (Prod.snd s)) c =
             contains (upd (Prod.fst (Prod.snd s)) (ts, rid) after) c := by
    grind
  have h_v : mysel_a (Prod.fst (Prod.snd s)) c =
             mysel_a (upd (Prod.fst (Prod.snd s)) (ts, rid) after) c := by
    simp only [mysel_a]; grind
  rw [h_c, h_v]

/-- Helper: if `(ts, rid)` isn't an afters-key in `s`, then
`after_of s c target = true` forces `c ≠ (ts, rid)`. -/
theorem after_of_true_implies_ne_fresh
    (s : concrete_st) (ts rid : ℕ) (c target : OpId) :
    contains (Prod.fst (Prod.snd s)) (ts, rid) = false →
    after_of s c target = true →
    c ≠ (ts, rid) := by
  intro h_fresh h_after h_eq
  subst h_eq
  simp only [after_of, h_fresh, Bool.false_and] at h_after
  exact Bool.false_ne_true h_after

/-- `afters_reach` persists under fresh-opId insertion. -/
theorem afters_reach_preserved_under_insert
    (s : concrete_st) (ts rid : ℕ) (ch : ℕ) (after : OpId) :
    contains (Prod.fst (Prod.snd s)) (ts, rid) = false →
    ∀ c anc, afters_reach s c anc →
      afters_reach (do_ s (ts, rid, app_op_t.Insert ch after)) c anc := by
  intro h_fresh c anc h
  induction h with
  | refl c => exact afters_reach.refl c
  | @step c c_parent anc h_after _ ih =>
    have h_ne : c ≠ (ts, rid) := after_of_true_implies_ne_fresh s ts rid c c_parent h_fresh h_after
    have h_after' : after_of (do_ s (ts, rid, app_op_t.Insert ch after)) c c_parent = true := by
      rw [← after_of_preserved_under_insert s ts rid ch after c c_parent h_ne]
      exact h_after
    exact afters_reach.step h_after' ih

/-- `visible_lt` persists under fresh-opId insertion. -/
theorem visible_lt_preserved_under_insert
    (s : concrete_st) (ts rid : ℕ) (ch : ℕ) (after : OpId) :
    contains (Prod.fst (Prod.snd s)) (ts, rid) = false →
    ∀ c₁ c₂, visible_lt s c₁ c₂ →
      visible_lt (do_ s (ts, rid, app_op_t.Insert ch after)) c₁ c₂ := by
  intro h_fresh c₁ c₂ h
  induction h with
  | @parent_child p c h_after =>
    have h_ne : c ≠ (ts, rid) := after_of_true_implies_ne_fresh s ts rid c p h_fresh h_after
    have h_after' : after_of (do_ s (ts, rid, app_op_t.Insert ch after)) c p = true := by
      rw [← after_of_preserved_under_insert s ts rid ch after c p h_ne]
      exact h_after
    exact visible_lt.parent_child h_after'
  | @sibling p ca cb h_after_a h_after_b h_ne_sib h_order =>
    have h_ne_a : ca ≠ (ts, rid) := after_of_true_implies_ne_fresh s ts rid ca p h_fresh h_after_a
    have h_ne_b : cb ≠ (ts, rid) := after_of_true_implies_ne_fresh s ts rid cb p h_fresh h_after_b
    have h_after_a' : after_of (do_ s (ts, rid, app_op_t.Insert ch after)) ca p = true := by
      rw [← after_of_preserved_under_insert s ts rid ch after ca p h_ne_a]; exact h_after_a
    have h_after_b' : after_of (do_ s (ts, rid, app_op_t.Insert ch after)) cb p = true := by
      rw [← after_of_preserved_under_insert s ts rid ch after cb p h_ne_b]; exact h_after_b
    exact visible_lt.sibling h_after_a' h_after_b' h_ne_sib h_order
  | @left_descendant_of_sibling p ca cb d h_after_a h_after_b h_ne_sib h_order h_reach h_d_ne =>
    have h_ne_a : ca ≠ (ts, rid) := after_of_true_implies_ne_fresh s ts rid ca p h_fresh h_after_a
    have h_ne_b : cb ≠ (ts, rid) := after_of_true_implies_ne_fresh s ts rid cb p h_fresh h_after_b
    have h_after_a' : after_of (do_ s (ts, rid, app_op_t.Insert ch after)) ca p = true := by
      rw [← after_of_preserved_under_insert s ts rid ch after ca p h_ne_a]; exact h_after_a
    have h_after_b' : after_of (do_ s (ts, rid, app_op_t.Insert ch after)) cb p = true := by
      rw [← after_of_preserved_under_insert s ts rid ch after cb p h_ne_b]; exact h_after_b
    have h_reach' : afters_reach (do_ s (ts, rid, app_op_t.Insert ch after)) d ca :=
      afters_reach_preserved_under_insert s ts rid ch after h_fresh d ca h_reach
    exact visible_lt.left_descendant_of_sibling h_after_a' h_after_b' h_ne_sib h_order h_reach' h_d_ne
  | @trans c₁ c₂ c₃ _ _ ih_12 ih_23 =>
    exact visible_lt.trans ih_12 ih_23

/-- `visible_le` persists under fresh-opId insertion. -/
theorem visible_le_preserved_under_insert
    (s : concrete_st) (ts rid : ℕ) (ch : ℕ) (after : OpId) :
    contains (Prod.fst (Prod.snd s)) (ts, rid) = false →
    ∀ c₁ c₂, visible_le s c₁ c₂ →
      visible_le (do_ s (ts, rid, app_op_t.Insert ch after)) c₁ c₂ := by
  intro h_fresh c₁ c₂ h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (visible_lt_preserved_under_insert s ts rid ch after h_fresh c₁ c₂ h)

/-- `bold_expand_reach` persists under fresh-opId Insert. -/
theorem bold_expand_reach_preserved_under_insert
    (s : concrete_st) (ts rid : ℕ) (ch : ℕ) (after : OpId) (m : MarkOp) :
    contains (Prod.fst (Prod.snd s)) (ts, rid) = false →
    ∀ c, bold_expand_reach s m c →
      bold_expand_reach (do_ s (ts, rid, app_op_t.Insert ch after)) m c := by
  intro h_fresh c h
  induction h with
  | at_endId => exact bold_expand_reach.at_endId
  | @step c c_parent h_after _ h_opid ih =>
    have h_ne : c ≠ (ts, rid) :=
      after_of_true_implies_ne_fresh s ts rid c c_parent h_fresh h_after
    have h_after' :
        after_of (do_ s (ts, rid, app_op_t.Insert ch after)) c c_parent = true := by
      rw [← after_of_preserved_under_insert s ts rid ch after c c_parent h_ne]
      exact h_after
    exact bold_expand_reach.step h_after' ih h_opid

/-- **Ex 1 — insert-within-span fully paper-faithful.**

If `c_after` is in the span (paper-faithfully) in `s_pre`, and we
insert a new char `(ts, rid)` with `afters = c_after` in a state
where that opId is fresh, the new char is in the span in `s_post`.

**Caveat.** The "right-side bound holds in s_post" hypothesis is
still required — RGA geometry doesn't automatically guarantee the
new char lands before `endId` in visible order (the new char could
be a younger sibling of `endId`'s ancestor, traversed past `endId`
as a late-in-opId-order descendant of `c_after`). The common case
where `c_after` is not an ancestor of `endId` is the one where
the bound is trivially derivable; a future commit could add that
specific corollary. -/
theorem insert_within_span_in_span_visible
    (s_pre : concrete_st) (m : MarkOp)
    (ts rid : ℕ) (ch : ℕ) (c_after : OpId) :
    contains (Prod.fst (Prod.snd s_pre)) (ts, rid) = false →
    in_span_visible s_pre m c_after →
    (if mark_endSide m = true
     then visible_le (do_ s_pre (ts, rid, app_op_t.Insert ch c_after)) (ts, rid) (mark_endId m)
     else visible_lt (do_ s_pre (ts, rid, app_op_t.Insert ch c_after)) (ts, rid) (mark_endId m)) →
    in_span_visible (do_ s_pre (ts, rid, app_op_t.Insert ch c_after)) m (ts, rid) := by
  intro h_fresh h_span_pre h_right_post
  set s_post := do_ s_pre (ts, rid, app_op_t.Insert ch c_after) with h_sp_def
  -- c_after is in span in s_post (by preservation)
  have h_span_c_after_post : in_span_visible s_post m c_after := by
    rcases h_span_pre with ⟨h_left_pre, h_right_pre⟩
    refine ⟨?_, ?_⟩
    · split_ifs with h_sSide
      · rw [if_pos h_sSide] at h_left_pre
        exact visible_lt_preserved_under_insert s_pre ts rid ch c_after h_fresh _ _ h_left_pre
      · rw [if_neg h_sSide] at h_left_pre
        exact visible_le_preserved_under_insert s_pre ts rid ch c_after h_fresh _ _ h_left_pre
    · split_ifs with h_eSide
      · rw [if_pos h_eSide] at h_right_pre
        rcases h_right_pre with h_le | h_be
        · exact Or.inl (visible_le_preserved_under_insert s_pre ts rid ch c_after h_fresh _ _ h_le)
        · exact Or.inr (bold_expand_reach_preserved_under_insert s_pre ts rid ch c_after m h_fresh _ h_be)
      · rw [if_neg h_eSide] at h_right_pre
        exact visible_lt_preserved_under_insert s_pre ts rid ch c_after h_fresh _ _ h_right_pre
  -- New char has afters = c_after in s_post
  have h_after_new : after_of s_post (ts, rid) c_after = true := by
    simp only [h_sp_def, after_of, do_, mysel_a]
    grind
  -- Apply in_span_visible_propagate
  exact in_span_visible_propagate s_post m (ts, rid) c_after
    h_span_c_after_post h_after_new h_right_post

/-- **Ex 1 bound auto-derivation for the cross-subtree case.**

If `c_after` and `endId` live in the subtrees of different direct
siblings `c_a_top` / `c_e_top` under a common afters-parent `p`,
with `c_a_top` the older sibling (`opid_max c_a_top c_e_top = c_a_top`),
then the right-side bound `visible_lt (do_ …) (ts, rid) endId`
holds *automatically* — no caller-provided bound needed.

The insertion places the new char in `c_a_top`'s subtree (since
`afters((ts, rid)) = c_after` and `afters_reach s c_after c_a_top`).
`c_e_top`'s subtree contains `endId`. By `visible_lt_of_cross_sibling`,
anything in the older-sibling subtree precedes anything in the
younger-sibling subtree.

This corollary covers the common "insert inside a bold span where
the bold starts below some ancestor level" case in the paper's
Ex 1, removing the bound from the user's obligation. For the
in-subtree-of-endId case (where `c_after` IS an afters-ancestor of
`endId`), the right-bound depends on opid ordering and is best
provided explicitly via `insert_within_span_in_span_visible`. -/
theorem insert_within_span_cross_subtree_in_span
    (s_pre : concrete_st) (m : MarkOp)
    (ts rid : ℕ) (ch : ℕ) (c_after p c_a_top c_e_top : OpId) :
    contains (Prod.fst (Prod.snd s_pre)) (ts, rid) = false →
    in_span_visible s_pre m c_after →
    mark_endSide m = false →
    afters_reach s_pre c_after c_a_top →
    afters_reach s_pre (mark_endId m) c_e_top →
    after_of s_pre c_a_top p = true →
    after_of s_pre c_e_top p = true →
    c_a_top ≠ c_e_top →
    opid_max c_a_top c_e_top = c_a_top →
    in_span_visible (do_ s_pre (ts, rid, app_op_t.Insert ch c_after)) m (ts, rid) := by
  intro h_fresh h_span_pre h_eSide h_reach_after h_reach_end
    h_after_a h_after_e h_ne h_order
  set s_post := do_ s_pre (ts, rid, app_op_t.Insert ch c_after) with h_sp_def
  -- Transfer the afters-reach chains and sibling relations to s_post
  -- (all via preservation, since the new opId is fresh).
  have h_reach_after_post : afters_reach s_post c_after c_a_top :=
    afters_reach_preserved_under_insert s_pre ts rid ch c_after h_fresh _ _ h_reach_after
  have h_reach_end_post : afters_reach s_post (mark_endId m) c_e_top :=
    afters_reach_preserved_under_insert s_pre ts rid ch c_after h_fresh _ _ h_reach_end
  have h_ne_a : c_a_top ≠ (ts, rid) := by
    exact after_of_true_implies_ne_fresh s_pre ts rid c_a_top p h_fresh h_after_a
  have h_ne_e : c_e_top ≠ (ts, rid) := by
    exact after_of_true_implies_ne_fresh s_pre ts rid c_e_top p h_fresh h_after_e
  have h_after_a_post : after_of s_post c_a_top p = true := by
    rw [h_sp_def, ← after_of_preserved_under_insert s_pre ts rid ch c_after c_a_top p h_ne_a]
    exact h_after_a
  have h_after_e_post : after_of s_post c_e_top p = true := by
    rw [h_sp_def, ← after_of_preserved_under_insert s_pre ts rid ch c_after c_e_top p h_ne_e]
    exact h_after_e
  -- New char reaches c_a_top via step + existing chain.
  have h_after_new : after_of s_post (ts, rid) c_after = true := by
    simp only [h_sp_def, after_of, do_, mysel_a]; grind
  have h_reach_new : afters_reach s_post (ts, rid) c_a_top :=
    afters_reach.step h_after_new h_reach_after_post
  -- Apply cross-sibling: new char in c_a_top's subtree, endId in c_e_top's.
  have h_right : visible_lt s_post (ts, rid) (mark_endId m) :=
    visible_lt_of_cross_sibling s_post p c_a_top c_e_top (ts, rid) (mark_endId m)
      h_after_a_post h_after_e_post h_ne h_order h_reach_new h_reach_end_post
  -- Now combine with the main insert theorem.
  apply insert_within_span_in_span_visible s_pre m ts rid ch c_after h_fresh h_span_pre
  rw [if_neg (by rw [h_eSide]; decide)]
  exact h_right

/-! ### Paper-faithful read-side using `in_span_visible`

Paper-faithful read-side projection built on the visible-order
covering predicate `in_span_visible`:

- **Link-no-expand (Ex 8):** chars inserted as direct descendants
  of `endId` are correctly excluded (they come after `endId` in
  visible order).
- **Bold-expand cross-sibling (Ex 7, partial):** chars inserted in
  older-sibling subtrees of `endId` are correctly included.
- **Ex 2 / 3 / 5 / anchors-survive-tombstones:** `_visible` theorems
  below. -/

/-- Paper-faithful "mark wins" predicate using `in_span_visible`. -/
noncomputable def mark_wins_visible
    (s : concrete_st) (m : MarkOp) (c : OpId) (mt : ℕ) : Prop :=
  mark_present s m = true ∧
  in_span_visible s m c ∧
  mark_markType m = mt ∧
  ∀ m', mark_present s m' = true →
        in_span_visible s m' c →
        mark_markType m' = mt →
        m' ≠ m →
        mark_beats m m' = true

/-- Paper-faithful rendered formatting using `mark_wins_visible`. -/
noncomputable def formatted_visible
    (s : concrete_st) (c : OpId) (mt : ℕ) : Bool :=
  if visible s c = true then
    decide (∃ m, mark_wins_visible s m c mt ∧ mark_isAdd m = true)
  else false

/-- Paper-faithful rich-text read. -/
noncomputable def readRichText_visible (s : concrete_st) :
    OpId → Option (ℕ × (ℕ → Bool)) :=
  fun c =>
    if visible s c = true then
      some (mysel_c (Prod.fst s) c, fun mt => formatted_visible s c mt)
    else
      none

/-- **Paper-faithful LWW-add-winner.**

If an `AddMark` is visibly-covering `c` and beats every other same-
type visibly-covering mark, `c` is formatted in the paper-faithful
projection. -/
theorem formatted_visible_of_lww_add_winner
    (s : concrete_st) (c : OpId) (mt : ℕ) (addOp : MarkOp) :
    mark_isAdd addOp = true →
    mark_markType addOp = mt →
    mark_present s addOp = true →
    in_span_visible s addOp c →
    visible s c = true →
    (∀ m', mark_present s m' = true →
           in_span_visible s m' c →
           mark_markType m' = mt →
           m' ≠ addOp →
           mark_beats addOp m' = true) →
    formatted_visible s c mt = true := by
  intro h_add h_mt_a h_pres_a h_cov_a h_vis h_beats
  simp only [formatted_visible, h_vis, if_true]
  refine decide_eq_true (Exists.intro addOp ?_)
  refine ⟨⟨h_pres_a, h_cov_a, h_mt_a, h_beats⟩, h_add⟩

/-- **No covering Add → unformatted, visible-order version.**

Paper Ex 5 negative case, restated against `in_span_visible`. -/
theorem no_add_cover_implies_unformatted_visible
    (s : concrete_st) (c : OpId) (mt : ℕ) :
    (∀ m, mark_present s m = true →
          in_span_visible s m c →
          mark_markType m = mt →
          mark_isAdd m = false) →
    formatted_visible s c mt = false := by
  intro h_all_removes
  have h_nex : ¬ ∃ m, mark_wins_visible s m c mt ∧ mark_isAdd m = true := by
    rintro ⟨w, ⟨h_pres_w, h_cov_w, h_mt_w, _⟩, h_w_add⟩
    have : mark_isAdd w = false := h_all_removes w h_pres_w h_cov_w h_mt_w
    grind
  simp only [formatted_visible]
  split_ifs with h_vis
  · exact decide_eq_false h_nex
  · rfl

/-- **Paper Ex 5 positive: an Add with the highest opId wins.**

"Concurrent Add wins over concurrent Remove" holds iff the Add's
opId is higher than every other same-mt covering mark — including
the Remove. The caller discharges that as part of the "beats every
other covering mark" universal. -/
theorem add_wins_over_concurrent_remove_visible
    (s : concrete_st) (c : OpId) (mt : ℕ)
    (addOp remOp : MarkOp) :
    mark_isAdd addOp = true →
    mark_isAdd remOp = false →
    mark_markType addOp = mt →
    mark_markType remOp = mt →
    mark_present s addOp = true →
    mark_present s remOp = true →
    in_span_visible s addOp c →
    in_span_visible s remOp c →
    visible s c = true →
    (∀ m', mark_present s m' = true →
           in_span_visible s m' c →
           mark_markType m' = mt →
           m' ≠ addOp →
           mark_beats addOp m' = true) →
    formatted_visible s c mt = true := by
  intro h_add _ h_mt_a _ h_pres_a _ h_cov_a _ h_vis h_beats
  exact formatted_visible_of_lww_add_winner s c mt addOp
    h_add h_mt_a h_pres_a h_cov_a h_vis h_beats

/-! ### `visible_lt` congruence under afters-agreement

`visible_lt` depends on state only through `after_of`, which reads
the `afters` component (`Prod.fst (Prod.snd s)`). When two states
agree pointwise on `afters`, `visible_lt` (and `afters_reach`, and
`in_span_visible`) give identical relations. These congruence
lemmas let us lift state equality to read-side equality. -/

/-- Pointwise `afters` agreement implies pointwise `after_of` agreement. -/
theorem after_of_eq_of_afters_eq
    (s₁ s₂ : concrete_st) (c target : OpId) :
    contains (Prod.fst (Prod.snd s₁)) c = contains (Prod.fst (Prod.snd s₂)) c →
    mysel_a (Prod.fst (Prod.snd s₁)) c = mysel_a (Prod.fst (Prod.snd s₂)) c →
    after_of s₁ c target = after_of s₂ c target := by
  intro h_c h_v
  simp only [after_of, h_c, h_v]

/-- `afters_reach` transfers across states with pointwise-equal `afters`. -/
theorem afters_reach_of_afters_eq
    (s₁ s₂ : concrete_st) :
    (∀ c, contains (Prod.fst (Prod.snd s₁)) c = contains (Prod.fst (Prod.snd s₂)) c) →
    (∀ c, mysel_a (Prod.fst (Prod.snd s₁)) c = mysel_a (Prod.fst (Prod.snd s₂)) c) →
    ∀ c anc, afters_reach s₁ c anc → afters_reach s₂ c anc := by
  intro h_c h_v c anc h
  induction h with
  | refl c => exact afters_reach.refl c
  | @step c c_parent anc h_after _ ih =>
    have h_after' : after_of s₂ c c_parent = true := by
      rw [← after_of_eq_of_afters_eq s₁ s₂ c c_parent (h_c c) (h_v c)]
      exact h_after
    exact afters_reach.step h_after' ih

/-- `visible_lt` transfers across states with pointwise-equal `afters`. -/
theorem visible_lt_of_afters_eq
    (s₁ s₂ : concrete_st) :
    (∀ c, contains (Prod.fst (Prod.snd s₁)) c = contains (Prod.fst (Prod.snd s₂)) c) →
    (∀ c, mysel_a (Prod.fst (Prod.snd s₁)) c = mysel_a (Prod.fst (Prod.snd s₂)) c) →
    ∀ c₁ c₂, visible_lt s₁ c₁ c₂ → visible_lt s₂ c₁ c₂ := by
  intro h_c h_v c₁ c₂ h
  induction h with
  | @parent_child p c h_after =>
    have h_after' : after_of s₂ c p = true := by
      rw [← after_of_eq_of_afters_eq s₁ s₂ c p (h_c c) (h_v c)]
      exact h_after
    exact visible_lt.parent_child h_after'
  | @sibling p ca cb h_after_a h_after_b h_ne h_order =>
    have h_after_a' : after_of s₂ ca p = true := by
      rw [← after_of_eq_of_afters_eq s₁ s₂ ca p (h_c ca) (h_v ca)]
      exact h_after_a
    have h_after_b' : after_of s₂ cb p = true := by
      rw [← after_of_eq_of_afters_eq s₁ s₂ cb p (h_c cb) (h_v cb)]
      exact h_after_b
    exact visible_lt.sibling h_after_a' h_after_b' h_ne h_order
  | @left_descendant_of_sibling p ca cb d h_after_a h_after_b h_ne h_order h_reach h_d_ne =>
    have h_after_a' : after_of s₂ ca p = true := by
      rw [← after_of_eq_of_afters_eq s₁ s₂ ca p (h_c ca) (h_v ca)]
      exact h_after_a
    have h_after_b' : after_of s₂ cb p = true := by
      rw [← after_of_eq_of_afters_eq s₁ s₂ cb p (h_c cb) (h_v cb)]
      exact h_after_b
    have h_reach' : afters_reach s₂ d ca :=
      afters_reach_of_afters_eq s₁ s₂ h_c h_v d ca h_reach
    exact visible_lt.left_descendant_of_sibling h_after_a' h_after_b' h_ne h_order h_reach' h_d_ne
  | @trans c₁ c₂ c₃ _ _ ih_12 ih_23 =>
    exact visible_lt.trans ih_12 ih_23

/-- `visible_le` version of the congruence. -/
theorem visible_le_of_afters_eq
    (s₁ s₂ : concrete_st) :
    (∀ c, contains (Prod.fst (Prod.snd s₁)) c = contains (Prod.fst (Prod.snd s₂)) c) →
    (∀ c, mysel_a (Prod.fst (Prod.snd s₁)) c = mysel_a (Prod.fst (Prod.snd s₂)) c) →
    ∀ c₁ c₂, visible_le s₁ c₁ c₂ → visible_le s₂ c₁ c₂ := by
  intro h_c h_v c₁ c₂ h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (visible_lt_of_afters_eq s₁ s₂ h_c h_v c₁ c₂ h)

/-- `bold_expand_reach` transfers across states with pointwise-equal afters. -/
theorem bold_expand_reach_of_afters_eq
    (s₁ s₂ : concrete_st) :
    (∀ c, contains (Prod.fst (Prod.snd s₁)) c = contains (Prod.fst (Prod.snd s₂)) c) →
    (∀ c, mysel_a (Prod.fst (Prod.snd s₁)) c = mysel_a (Prod.fst (Prod.snd s₂)) c) →
    ∀ m c, bold_expand_reach s₁ m c → bold_expand_reach s₂ m c := by
  intro h_c h_v m c h
  induction h with
  | at_endId => exact bold_expand_reach.at_endId
  | @step c c_parent h_after _ h_opid ih =>
    have h_after' : after_of s₂ c c_parent = true := by
      rw [← after_of_eq_of_afters_eq s₁ s₂ c c_parent (h_c c) (h_v c)]
      exact h_after
    exact bold_expand_reach.step h_after' ih h_opid

/-- `in_span_visible` transfers across states with pointwise-equal afters. -/
theorem in_span_visible_of_afters_eq
    (s₁ s₂ : concrete_st) (m : MarkOp) (c : OpId) :
    (∀ c, contains (Prod.fst (Prod.snd s₁)) c = contains (Prod.fst (Prod.snd s₂)) c) →
    (∀ c, mysel_a (Prod.fst (Prod.snd s₁)) c = mysel_a (Prod.fst (Prod.snd s₂)) c) →
    in_span_visible s₁ m c → in_span_visible s₂ m c := by
  intro h_c h_v h
  rcases h with ⟨h_left, h_right⟩
  refine ⟨?_, ?_⟩
  · split_ifs with h_sSide
    · -- startSide=true: visible_lt
      rw [if_pos h_sSide] at h_left
      exact visible_lt_of_afters_eq s₁ s₂ h_c h_v _ _ h_left
    · rw [if_neg h_sSide] at h_left
      exact visible_le_of_afters_eq s₁ s₂ h_c h_v _ _ h_left
  · split_ifs with h_eSide
    · rw [if_pos h_eSide] at h_right
      rcases h_right with h_le | h_be
      · exact Or.inl (visible_le_of_afters_eq s₁ s₂ h_c h_v _ _ h_le)
      · exact Or.inr (bold_expand_reach_of_afters_eq s₁ s₂ h_c h_v m c h_be)
    · rw [if_neg h_eSide] at h_right
      exact visible_lt_of_afters_eq s₁ s₂ h_c h_v _ _ h_right

/-- Helper: the `∃ m, mark_wins_visible s m c mt ∧ isAdd m` predicate
is invariant under pointwise state equality. -/
theorem exists_mark_wins_visible_add_iff
    (s₁ s₂ : concrete_st) (c : OpId) (mt : ℕ) :
    (∀ x : AnchorAttachment, Prod.snd (Prod.snd (Prod.snd s₁)) x =
                              Prod.snd (Prod.snd (Prod.snd s₂)) x) →
    (∀ k, contains (Prod.fst (Prod.snd s₁)) k = contains (Prod.fst (Prod.snd s₂)) k) →
    (∀ k, mysel_a (Prod.fst (Prod.snd s₁)) k = mysel_a (Prod.fst (Prod.snd s₂)) k) →
    ((∃ m, mark_wins_visible s₁ m c mt ∧ mark_isAdd m = true) ↔
     (∃ m, mark_wins_visible s₂ m c mt ∧ mark_isAdd m = true)) := by
  intro hm h_afc h_afv
  constructor
  · rintro ⟨m, ⟨h_pres, h_cov, h_mt, h_beats⟩, h_add⟩
    refine ⟨m, ⟨?_, ?_, h_mt, ?_⟩, h_add⟩
    · simp only [mark_present, marks_of, ← hm]; exact h_pres
    · exact in_span_visible_of_afters_eq s₁ s₂ _ _ h_afc h_afv h_cov
    · intro m' h_pres' h_cov' h_mt' h_ne
      apply h_beats m' _ _ h_mt' h_ne
      · simp only [mark_present, marks_of, hm]; exact h_pres'
      · exact in_span_visible_of_afters_eq s₂ s₁ _ _
          (fun k => (h_afc k).symm) (fun k => (h_afv k).symm) h_cov'
  · rintro ⟨m, ⟨h_pres, h_cov, h_mt, h_beats⟩, h_add⟩
    refine ⟨m, ⟨?_, ?_, h_mt, ?_⟩, h_add⟩
    · simp only [mark_present, marks_of, hm]; exact h_pres
    · exact in_span_visible_of_afters_eq s₂ s₁ _ _
        (fun k => (h_afc k).symm) (fun k => (h_afv k).symm) h_cov
    · intro m' h_pres' h_cov' h_mt' h_ne
      apply h_beats m' _ _ h_mt' h_ne
      · simp only [mark_present, marks_of, ← hm]; exact h_pres'
      · exact in_span_visible_of_afters_eq s₁ s₂ _ _ h_afc h_afv h_cov'

/-- **Formatting-level convergence (the useful core).** -/
theorem formatted_visible_convergent
    (s₁ s₂ : concrete_st) (c : OpId) (mt : ℕ) :
    eq s₁ s₂ → formatted_visible s₁ c mt = formatted_visible s₂ c mt := by
  intro h
  rcases h with ⟨hc, haf, hd, hm⟩
  have h_afc : ∀ k, contains (Prod.fst (Prod.snd s₁)) k =
                     contains (Prod.fst (Prod.snd s₂)) k := fun k => (haf k).1
  have h_afv : ∀ k, mysel_a (Prod.fst (Prod.snd s₁)) k =
                     mysel_a (Prod.fst (Prod.snd s₂)) k := fun k => (haf k).2
  have h_vis : visible s₁ c = visible s₂ c := by
    simp only [visible, (hc c).1, (hd c).2]
  have h_iff : (∃ m, mark_wins_visible s₁ m c mt ∧ mark_isAdd m = true) ↔
               (∃ m, mark_wins_visible s₂ m c mt ∧ mark_isAdd m = true) :=
    exists_mark_wins_visible_add_iff s₁ s₂ c mt hm h_afc h_afv
  simp only [formatted_visible, h_vis]
  split_ifs with h_v
  · exact decide_eq_decide.mpr h_iff
  · rfl

/-- **Convergence of the paper-faithful read-side projection.** -/
theorem readRichText_visible_convergent (s₁ s₂ : concrete_st) :
    eq s₁ s₂ → readRichText_visible s₁ = readRichText_visible s₂ := by
  intro h
  funext c
  have h_eq := h
  rcases h with ⟨hc, _, hd, _⟩
  have h_vis : visible s₁ c = visible s₂ c := by
    simp only [visible, (hc c).1, (hd c).2]
  have h_payload : mysel_c (Prod.fst s₁) c = mysel_c (Prod.fst s₂) c := (hc c).2
  have h_fmt : ∀ mt, formatted_visible s₁ c mt = formatted_visible s₂ c mt :=
    fun mt => formatted_visible_convergent s₁ s₂ c mt h_eq
  simp only [readRichText_visible, h_vis, h_payload]
  split_ifs with h_v
  · exact congrArg some (Prod.ext rfl (funext h_fmt))
  · rfl

/-! ### Remaining paper-faithful analogues

The expand/contract, overlap, and anchors-survive-tombstones
theorems from the boundary-predicate track get clean `_visible`
analogues. -/

/-- **Paper Ex 2, visible version — overlapping same-type Adds.**

If no Remove of type `mt` visibly covers `c`, and some Add visibly
covers `c` and beats every other covering Add by LWW, then `c` is
formatted. -/
theorem partial_overlap_all_adds_formatted_visible
    (s : concrete_st) (c : OpId) (mt : ℕ) (m : MarkOp) :
    mark_isAdd m = true →
    mark_markType m = mt →
    mark_present s m = true →
    in_span_visible s m c →
    visible s c = true →
    (∀ m', mark_present s m' = true →
           in_span_visible s m' c →
           mark_markType m' = mt →
           mark_isAdd m' = false →
           False) →
    (∀ m', mark_present s m' = true →
           in_span_visible s m' c →
           mark_markType m' = mt →
           mark_isAdd m' = true →
           m' ≠ m →
           mark_beats m m' = true) →
    formatted_visible s c mt = true := by
  intro h_add h_mt h_pres h_cov h_vis h_no_rem h_beats_adds
  simp only [formatted_visible, h_vis, if_true]
  refine decide_eq_true (Exists.intro m ?_)
  refine ⟨⟨h_pres, h_cov, h_mt, ?_⟩, h_add⟩
  intro m' h_pres' h_cov' h_mt' h_ne
  match h_isAdd : mark_isAdd m' with
  | true  => exact h_beats_adds m' h_pres' h_cov' h_mt' h_isAdd h_ne
  | false => exact absurd (h_no_rem m' h_pres' h_cov' h_mt' h_isAdd) id

/-- **Paper Ex 3, visible version — different-type Adds coexist.** -/
theorem different_type_adds_coexist_visible
    (s : concrete_st) (c : OpId) (mB mI : MarkOp) :
    mark_isAdd mB = true →
    mark_isAdd mI = true →
    mark_markType mB ≠ mark_markType mI →
    mark_present s mB = true →
    mark_present s mI = true →
    in_span_visible s mB c →
    in_span_visible s mI c →
    visible s c = true →
    (∀ m', mark_present s m' = true → in_span_visible s m' c →
           mark_markType m' = mark_markType mB → m' ≠ mB →
           mark_beats mB m' = true) →
    (∀ m', mark_present s m' = true → in_span_visible s m' c →
           mark_markType m' = mark_markType mI → m' ≠ mI →
           mark_beats mI m' = true) →
    formatted_visible s c (mark_markType mB) = true ∧
    formatted_visible s c (mark_markType mI) = true := by
  intro h_addB h_addI _ h_presB h_presI h_covB h_covI h_vis h_beatsB h_beatsI
  refine ⟨?_, ?_⟩
  · simp only [formatted_visible, h_vis, if_true]
    exact decide_eq_true (Exists.intro mB ⟨⟨h_presB, h_covB, rfl, h_beatsB⟩, h_addB⟩)
  · simp only [formatted_visible, h_vis, if_true]
    exact decide_eq_true (Exists.intro mI ⟨⟨h_presI, h_covI, rfl, h_beatsI⟩, h_addI⟩)

/-- **Anchors survive tombstones, visible version.**

`Remove c_rm` only changes the `deleted` component at `c_rm`; chars,
afters, and marks are unchanged. `formatted_visible` at `c ≠ c_rm`
reads `deleted` only at `c` (invariant), and `mark_wins_visible`
doesn't touch `deleted` at all. Proved by combining h_vis invariance
on the outer `if` with `exists_mark_wins_visible_add_iff` via the
reflexive refl-equalities on chars/afters/marks. -/
theorem anchors_survive_tombstones_visible
    (s : concrete_st) (c c_rm : OpId) (mt : ℕ) (ts rid : ℕ) :
    c ≠ c_rm →
    formatted_visible s c mt =
      formatted_visible (do_ s (ts, rid, app_op_t.Remove c_rm)) c mt := by
  intro hne
  set s' := do_ s (ts, rid, app_op_t.Remove c_rm) with hs'_def
  have h_afc : ∀ k, contains (Prod.fst (Prod.snd s)) k =
                     contains (Prod.fst (Prod.snd s')) k := fun _ => rfl
  have h_afv : ∀ k, mysel_a (Prod.fst (Prod.snd s)) k =
                     mysel_a (Prod.fst (Prod.snd s')) k := fun _ => rfl
  have h_marks : ∀ x : AnchorAttachment,
                  Prod.snd (Prod.snd (Prod.snd s)) x =
                  Prod.snd (Prod.snd (Prod.snd s')) x := fun _ => rfl
  have h_vis : visible s c = visible s' c := by
    simp only [visible, hs'_def, do_, mysel_d]; grind
  simp only [formatted_visible, h_vis]
  split_ifs with h_v
  · exact decide_eq_decide.mpr
      (exists_mark_wins_visible_add_iff s s' c mt h_marks h_afc h_afv)
  · rfl


/-! ### List-form traversal specification

Rather than produce an RGA traversal `List OpId` computationally
(which would require framework-level finite enumeration over
`set OpId := OpId → Bool`), we specify **what it means for a list
to be the traversal** via a Prop-valued relation. Callers that
produce traversals by any means (e.g., the TypeScript demo's
`traverse`) can prove their lists satisfy `is_rga_traversal` and
then use the result with the list-form `readRichText_list` below.

Three-part characterization of a valid traversal:
1. Exactly-visible: `c ∈ l ↔ visible s c = true` (visibility
   membership).
2. No duplicates: each char appears at most once.
3. Visible-order sorted: for any two chars at positions i < j in
   `l`, `visible_lt s l[i] l[j]`. -/

def is_rga_traversal (s : concrete_st) (l : List OpId) : Prop :=
  (∀ c, c ∈ l ↔ visible s c = true) ∧
  l.Nodup ∧
  l.Pairwise (visible_lt s)

/-- List-form rich-text projection: given a traversal, produce
the list of `(OpId, codepoint, formatting)` records. -/
noncomputable def readRichText_list
    (s : concrete_st) (l : List OpId) :
    List (OpId × ℕ × (ℕ → Bool)) :=
  l.map (fun c => (c, mysel_c (Prod.fst s) c, fun mt => formatted_visible s c mt))

/-- **Traversal-spec convergence.** Pointwise-`eq` states agree on
which lists are valid traversals. -/
theorem is_rga_traversal_convergent (s₁ s₂ : concrete_st) :
    eq s₁ s₂ → ∀ l, is_rga_traversal s₁ l ↔ is_rga_traversal s₂ l := by
  intro h l
  rcases h with ⟨hc, haf, hd, _⟩
  have h_afc : ∀ k, contains (Prod.fst (Prod.snd s₁)) k =
                     contains (Prod.fst (Prod.snd s₂)) k := fun k => (haf k).1
  have h_afv : ∀ k, mysel_a (Prod.fst (Prod.snd s₁)) k =
                     mysel_a (Prod.fst (Prod.snd s₂)) k := fun k => (haf k).2
  have h_vis : ∀ c, visible s₁ c = visible s₂ c := fun c => by
    simp only [visible, (hc c).1, (hd c).2]
  unfold is_rga_traversal
  refine ⟨fun ⟨h_mem, h_nd, h_pw⟩ => ⟨?_, h_nd, ?_⟩,
          fun ⟨h_mem, h_nd, h_pw⟩ => ⟨?_, h_nd, ?_⟩⟩
  · intro c; rw [h_mem c, h_vis c]
  · exact h_pw.imp (fun {a b} h => visible_lt_of_afters_eq s₁ s₂ h_afc h_afv a b h)
  · intro c; rw [h_mem c, ← h_vis c]
  · exact h_pw.imp (fun {a b} h =>
      visible_lt_of_afters_eq s₂ s₁
        (fun k => (h_afc k).symm) (fun k => (h_afv k).symm) a b h)

/-- **List-form `readRichText_list` convergence.** If two pointwise-equal
states produce traversals `l₁` and `l₂`, the list renderings may
differ only by *identical* reorderings — but by traversal
uniqueness (nodup + pairwise visible_lt), any traversal of a given
state is unique as a list (given visible_lt is antisymmetric on
distinct chars, which it is under `distinct_ops`). In particular,
if both take the same list `l`, the renderings agree. -/
theorem readRichText_list_eq_of_traversal_eq
    (s₁ s₂ : concrete_st) (l : List OpId) :
    eq s₁ s₂ →
    readRichText_list s₁ l = readRichText_list s₂ l := by
  intro h_eq
  have h_payload : ∀ c, mysel_c (Prod.fst s₁) c = mysel_c (Prod.fst s₂) c :=
    fun c => (h_eq.1 c).2
  have h_fmt : ∀ c mt, formatted_visible s₁ c mt = formatted_visible s₂ c mt :=
    fun c mt => formatted_visible_convergent s₁ s₂ c mt h_eq
  unfold readRichText_list
  apply List.map_congr_left
  intro c _
  exact Prod.ext rfl (Prod.ext (h_payload c) (funext (h_fmt c)))
