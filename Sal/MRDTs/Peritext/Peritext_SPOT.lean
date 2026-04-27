import Sal.Interfaces.Set_Extended
import Sal.MRDTs.Peritext.Peritext_MRDT
import Sal.MRDTs.Peritext.Peritext_ReadSide

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

open Classical

/-! # Peritext (MRDT) — SPOTs

Small Proof-Oriented Tests for the paper-faithful read-side. Each
SPOT pins one of the Peritext paper's example figures (§3) onto a
small concrete `do_`-built state, and discharges the conclusion by
**applying the corresponding general theorem from `Peritext_ReadSide`
with concrete witnesses** rather than by operational unfolding.

Why theorem-application discharge: a SPOT's value is testing whether
the general spec-level theorem is strong enough to be invoked on the
scenario it's named after. If a hypothesis weren't provable on the
small state, that would flag a too-strong hypothesis (or a too-weak
state model). All nine SPOTs below close, so the relevant theorems
admit their canonical paper instances cleanly.

Coverage:

* SPOTs 1-4: RGA structure + tombstone-anchor-survival (Ex 7, Ex 8).
* SPOTs 5-6: rich-text formatting layer (Ex 1, Ex 5 negative).
* SPOTs 7-9: rich-text formatting layer (Ex 2, Ex 3, Ex 5 positive)
  via the `mark_present` uniqueness pattern documented after SPOT 6.

Conventions:

* OpIds are `(ts, rid) : ℕ × ℕ`. We treat `(0, 0)` as a sentinel
  "before-first" parent — no character is inserted at it; subsequent
  inserts use it as their `after_id`.
* `after_of` membership reduces under `simp [after_of, do_, ...]`
  to a Boolean characteristic-function expression; the tail step is
  exhibiting the inserted-char witness explicitly.
* For `mark_present` premises: with one or two AddMarks in state,
  any `m'` satisfying `mark_present σ m' = true` is forced to equal
  one of the constructed marks (extracted by `simp` on the marks set).
  Universally-quantified "no other mark interferes" premises become
  vacuous via this uniqueness. -/

namespace Peritext_SPOT

/-! ## SPOT 1 — Insert chain produces `afters_reach`

Two sequential inserts: `(1, 0)` after sentinel `(0, 0)`, then
`(2, 0)` after `(1, 0)`. The descendant `(2, 0)` reaches the parent
`(0, 0)` via the `afters_reach` chain. -/
example :
    let σ₀ := do_ init_st (1, 0, app_op_t.Insert 65 (0, 0))   -- 'A' after sentinel
    let σ  := do_ σ₀     (2, 0, app_op_t.Insert 66 (1, 0))    -- 'B' after 'A'
    afters_reach σ (2, 0) (0, 0) := by
  set σ₀ := do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)) with hσ₀
  set σ  := do_ σ₀     (2, 0, app_op_t.Insert 66 (1, 0)) with hσ
  -- after_of σ (2, 0) (1, 0) = true (the second Insert stakes (2,0)→(1,0))
  have h_step2 : after_of σ (2, 0) (1, 0) = true := by
    simp only [hσ, after_of, do_, chars_of, add, union, _root_.singleton,
               Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨66, Or.inr rfl⟩
  -- after_of σ (1, 0) (0, 0) = true (the first Insert stakes (1,0)→(0,0))
  -- Inner-add entry: outer Or.inl skips the (2,0)→(1,0)/66 add, inner Or.inr matches.
  have h_step1 : after_of σ (1, 0) (0, 0) = true := by
    simp only [hσ, hσ₀, after_of, do_, chars_of, add, union, _root_.singleton,
               Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨65, Or.inl (Or.inr rfl)⟩
  exact afters_reach.step (c_parent := (1, 0)) h_step2
          (afters_reach.step (c_parent := (0, 0)) h_step1 (afters_reach.refl _))

/-! ## SPOT 2 — Ex 8 partial: link-descendant has `visible_lt endId c_new`

The fragment of paper Ex 8 that holds without a well-formedness
premise: any `c_new` inserted as a direct afters-descendant of the
mark's `endId` satisfies `visible_lt s endId c_new`. This is the
"failure direction" of `in_span_visible` for closed-end (`endSide =
false`) marks. Applies `ex8_link_descendant_visible_lt_endId`. -/
example :
    -- Pre-state: a single char '!'@(1,0) inserted after the sentinel,
    -- to act as the mark's endId.
    let σ₀ := do_ init_st (1, 0, app_op_t.Insert 33 (0, 0))
    -- A new char '?'@(2, 0) inserted as a direct afters-child of (1, 0).
    let σ  := do_ σ₀     (2, 0, app_op_t.Insert 63 (1, 0))
    -- Mark: link from (0,0) to (1,0), markType = 0.
    let m  : MarkOp := ⟨(10, 0), (0, 0), false, (1, 0), false, 0, true⟩
    visible_lt σ m.endId (2, 0) := by
  set σ₀ := do_ init_st (1, 0, app_op_t.Insert 33 (0, 0)) with hσ₀
  set σ  := do_ σ₀     (2, 0, app_op_t.Insert 63 (1, 0)) with hσ
  have h_after : after_of σ (2, 0) (1, 0) = true := by
    simp only [hσ, after_of, do_, chars_of, add, union, _root_.singleton,
               Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨63, Or.inr rfl⟩
  -- m.endId reduces to (1, 0) by projection.
  exact ex8_link_descendant_visible_lt_endId σ
    ⟨(10, 0), (0, 0), false, (1, 0), false, 0, true⟩ (2, 0) h_after

/-! ## SPOT 3 — Ex 7: bold-style older sibling is in span

Two siblings inserted at `(1, 0)` and `(2, 0)`, both rooted at the
sentinel `(0, 0)`. The mark spans from sentinel-as-startId to the
younger-sibling `(1, 0)` as endId, both sides closed (`startSide =
false`, `endSide = false`). The older sibling `(2, 0)` (greater
`opid_max`) is in the visible-span. Applies
`ex7_bold_older_sibling_in_span`. -/
example :
    let σ₀ := do_ init_st (1, 0, app_op_t.Insert 65 (0, 0))   -- 'A' (younger)
    let σ  := do_ σ₀     (2, 0, app_op_t.Insert 66 (0, 0))    -- 'B' (older)
    let m  : MarkOp := ⟨(10, 0), (0, 0), false, (1, 0), false, 0, true⟩
    in_span_visible σ m (2, 0) := by
  set σ₀ := do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)) with hσ₀
  set σ  := do_ σ₀     (2, 0, app_op_t.Insert 66 (0, 0)) with hσ
  have h_after_new : after_of σ (2, 0) (0, 0) = true := by
    simp only [hσ, after_of, do_, chars_of, add, union, _root_.singleton,
               Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨66, Or.inr rfl⟩
  have h_after_end : after_of σ (1, 0) (0, 0) = true := by
    simp only [hσ, hσ₀, after_of, do_, chars_of, add, union, _root_.singleton,
               Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨65, Or.inl (Or.inr rfl)⟩
  refine ex7_bold_older_sibling_in_span σ
    ⟨(10, 0), (0, 0), false, (1, 0), false, 0, true⟩ (0, 0) (2, 0)
    rfl rfl ?_ h_after_new h_after_end ?_ ?_ ?_
  · exact visible_le_refl σ (0, 0)
  · decide                                          -- (2, 0) ≠ (1, 0)
  · decide                                          -- opid_max (2, 0) (1, 0) = (2, 0)
  · decide                                          -- (2, 0) ≠ (0, 0)

/-! ## SPOT 4 — Anchors survive tombstones

A formatted-character query at `c` is unchanged when a *different*
character `c_rm` is tombstoned. Direct application of
`anchors_survive_tombstones_visible`; the only premise is
`c ≠ c_rm`, which holds by `decide`. -/
example :
    formatted_visible
        (do_ (do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)))
             (2, 0, app_op_t.AddMark (0, 0) false (1, 0) false 0))
        (1, 0) 0
      =
    formatted_visible
        (do_ (do_ (do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)))
                  (2, 0, app_op_t.AddMark (0, 0) false (1, 0) false 0))
             (3, 0, app_op_t.Remove (0, 0)))
        (1, 0) 0 :=
  anchors_survive_tombstones_visible _ (1, 0) (0, 0) 0 3 0 (by decide)

/-! ## SPOT 5 — Ex 1: insert-within-span propagates

Pre-state: `'A'@(1,0)` after sentinel, then `'B'@(2,0)` after `'A'`.
Mark `m` covers `[(1,0), (2,0)]` closed-left, open-right (bold-expand
shape: `endSide = true`). The character `(1,0)` is the mark's
`startId`, hence trivially in span.

Insert `(3,0)` after `(1,0)` — it lands as an older sibling of
`(2,0)` under common parent `(1,0)`, with `opid_max (3,0) (2,0) =
(3,0)`. Visible-order: `(3,0)` precedes `(2,0)`, and is a
parent_child descendant of `(1,0)`. So `(3,0)` is *within* the span
in the post-state. Applies `insert_within_span_in_span_visible`. -/
example :
    let σ_pre := do_ (do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)))
                     (2, 0, app_op_t.Insert 66 (1, 0))
    let σ_post := do_ σ_pre (3, 0, app_op_t.Insert 67 (1, 0))
    let m  : MarkOp := ⟨(10, 0), (1, 0), false, (2, 0), true, 0, true⟩
    in_span_visible σ_post m (3, 0) := by
  set σ₀  := do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)) with hσ₀
  set σ_pre  := do_ σ₀ (2, 0, app_op_t.Insert 66 (1, 0)) with hσ_pre
  set σ_post := do_ σ_pre (3, 0, app_op_t.Insert 67 (1, 0)) with hσ_post
  let m : MarkOp := ⟨(10, 0), (1, 0), false, (2, 0), true, 0, true⟩
  -- Freshness premise: (3, 0) is not yet a CharRec key in σ_pre.
  have h_fresh : ∀ t ch, Prod.fst σ_pre ((3, 0), t, ch) = false := by
    intro t ch
    -- `Prod.fst σ_pre = add ((2,0),(1,0),66) (add ((1,0),(0,0),65) ∅)`. At first-coord
    -- (3, 0), neither stored record matches (their first coords are (1,0) and (2,0)).
    simp [hσ_pre, hσ₀, do_, init_st]
  -- Step 1: in_span_visible σ_pre m (1, 0) (i.e. at the mark's startId).
  -- after_of σ_pre (2, 0) (1, 0) = true (from the second Insert).
  have h_after_2_pre : after_of σ_pre (2, 0) (1, 0) = true := by
    simp only [hσ_pre, after_of, do_, chars_of, add, union, _root_.singleton,
               Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨66, Or.inr rfl⟩
  have h_span_pre : in_span_visible σ_pre m (1, 0) := by
    refine ⟨?_, ?_⟩
    · -- Left bound: m.startSide = false, so visible_le σ_pre m.startId (1,0). m.startId = (1,0).
      show (if (m.startSide = true) then visible_lt σ_pre m.startId (1, 0)
            else visible_le σ_pre m.startId (1, 0))
      simp only [show m.startSide = false from rfl, if_false]
      show visible_le σ_pre (1, 0) (1, 0)
      exact visible_le_refl _ _
    · -- Right bound: m.endSide = true, so visible_le σ_pre (1,0) m.endId ∨ bold_expand.
      show (if (m.endSide = true) then
              visible_le σ_pre (1, 0) m.endId ∨ bold_expand_reach σ_pre m (1, 0)
            else visible_lt σ_pre (1, 0) m.endId)
      simp only [show m.endSide = true from rfl, if_true]
      show visible_le σ_pre (1, 0) (2, 0) ∨ bold_expand_reach σ_pre m (1, 0)
      exact Or.inl (Or.inr (visible_lt.parent_child h_after_2_pre))
  -- Step 2: right-side bound on σ_post.
  -- after_of σ_post (3, 0) (1, 0) = true (the new Insert).
  have h_after_3_post : after_of σ_post (3, 0) (1, 0) = true := by
    simp only [hσ_post, after_of, do_, chars_of, add, union, _root_.singleton,
               Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨67, Or.inr rfl⟩
  -- after_of σ_post (2, 0) (1, 0) = true (preserved from σ_pre).
  have h_after_2_post : after_of σ_post (2, 0) (1, 0) = true := by
    simp only [hσ_post, hσ_pre, after_of, do_, chars_of, add, union, _root_.singleton,
               Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨66, Or.inl (Or.inr rfl)⟩
  -- Sibling rule: (3, 0) and (2, 0) are siblings under (1, 0); opid_max picks (3, 0).
  have h_sib : visible_lt σ_post (3, 0) (2, 0) :=
    visible_lt.sibling h_after_3_post h_after_2_post (by decide) (by decide)
  -- Apply Ex 1.
  refine insert_within_span_in_span_visible σ_pre m 3 0 67 (1, 0) h_fresh h_span_pre ?_
  -- Right-side bound for the post-state: m.endSide = true, so visible_le σ_post (3, 0) m.endId.
  show (if (m.endSide = true) then visible_le σ_post (3, 0) m.endId
        else visible_lt σ_post (3, 0) m.endId)
  simp only [show m.endSide = true from rfl, if_true]
  exact Or.inr h_sib

/-! ## SPOT 6 — Ex 5 negative: no Add cover ⇒ unformatted

A state with one Insert and zero marks. The "no Add of mark-type
`mt` covers `c`" antecedent is vacuously true (no marks at all
satisfy `mark_present`), so `formatted_visible σ (1, 0) 0 = false`.
Applies `no_add_cover_implies_unformatted_visible`. -/
example :
    let σ := do_ init_st (1, 0, app_op_t.Insert 65 (0, 0))
    formatted_visible σ (1, 0) 0 = false := by
  set σ := do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)) with hσ
  apply no_add_cover_implies_unformatted_visible σ (1, 0) 0
  -- Antecedent: ∀ m, mark_present σ m → in_span_visible σ m (1,0) → m.markType = 0 → m.isAdd = false.
  -- With no AddMark/RemoveMark in σ, marks_of σ ≡ empty, so mark_present is always false.
  intro m h_pres _ _
  exfalso
  -- mark_present σ m = false on a no-marks state.
  simp only [hσ, mark_present, marks_of, do_, _root_.empty] at h_pres
  exact Bool.false_ne_true h_pres

/-! ## Discharge pattern for `mark_present` uniqueness

The remaining SPOTs (Ex 2, Ex 3, Ex 5-positive) all need a
universal-`∀ m', mark_present σ m' = true → ...` discharged on a
concrete state with 1–2 AddMarks. The trick that closes it cleanly:

1. Build a uniqueness lemma `∀ m', mark_present σ m' = true →
   m' = constructed_mark` (or a 2-way disjunction for two marks).
2. Discharge with `simp [hσ, ..., mark_present, marks_of, do_, add,
   _root_.singleton, union, empty] at h_pres; rcases m'; grind`.
   The `rcases` destructures `m'` into its 7 fields so `grind`
   collapses the resulting AnchorAttachment-injectivity disjunction
   into a single tuple equality.
3. Inline the constructed mark as a literal `⟨...⟩` rather than
   `let`-binding it — projections off let-bound MarkOp values
   block reduction inside `simp`.

The same pattern works on the CRDT side (`Sal/CRDTs/Peritext/Peritext_SPOT.lean`). -/

/-! ## SPOT 7 — Ex 2: concurrent same-type Adds with overlap

The paper Ex 2 scenario: **two concurrent same-type Adds from
different replicas whose spans partially overlap**, with formatting
holding at a point in the overlap.

Scenario: insert chain `'A'@(1,0) → 'B'@(2,0) → 'C'@(3,0)` (built
on a single replica for brevity). Then two AddMarks, both
`markType = 0` (bold), originating from *different* replicas:
  * `mark₁` at `(ts=4, rid=0)`: bold span `[(1,0), (2,0)]` — A and B.
  * `mark₂` at `(ts=5, rid=1)`: bold span `[(2,0), (3,0)]` — B and C.

In Sal's state-based framework, "concurrent from different replicas"
is encoded by distinct `rid`s. With `rc := Either` on Peritext,
sequential `do_; do_` on different rids converges to the same state
as a literal merge of two divergent branches — so the discharge
mechanism stays simple while the *semantics* is genuinely concurrent.

At `c = (2, 0)` (the overlap point), *both* marks cover it. The
LWW witness is `mark₂` (higher `opId` beats `mark₁` via `mark_beats`'s
`opid_max` clause when both are Adds). Applies
`partial_overlap_all_adds_formatted_visible`. -/
example :
    let σ_pre := do_ (do_ (do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)))
                          (2, 0, app_op_t.Insert 66 (1, 0)))
                     (3, 0, app_op_t.Insert 67 (2, 0))
    let σ_m1 := do_ σ_pre (4, 0, app_op_t.AddMark (1, 0) false (2, 0) true 0)
    let σ := do_ σ_m1 (5, 1, app_op_t.AddMark (2, 0) false (3, 0) true 0)
    formatted_visible σ (2, 0) 0 = true := by
  set σ_pre := do_ (do_ (do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)))
                        (2, 0, app_op_t.Insert 66 (1, 0)))
                   (3, 0, app_op_t.Insert 67 (2, 0)) with hσ_pre
  set σ_m1 := do_ σ_pre (4, 0, app_op_t.AddMark (1, 0) false (2, 0) true 0) with hσ_m1
  set σ := do_ σ_m1 (5, 1, app_op_t.AddMark (2, 0) false (3, 0) true 0) with hσ
  have h_uniq : ∀ m' : MarkOp, mark_present σ m' = true →
      m' = ⟨(4, 0), (1, 0), false, (2, 0), true, 0, true⟩ ∨
      m' = ⟨(5, 1), (2, 0), false, (3, 0), true, 0, true⟩ := by
    intro m' h_pres
    simp [hσ, hσ_m1, hσ_pre, mark_present, marks_of, do_, add,
          _root_.singleton, union, empty] at h_pres
    rcases m' with ⟨_, _, _, _, _, _, _⟩
    grind
  have h_after_2_1 : after_of σ (2, 0) (1, 0) = true := by
    simp [hσ, hσ_m1, hσ_pre, after_of, chars_of, do_]
  have h_after_3_2 : after_of σ (3, 0) (2, 0) = true := by
    simp [hσ, hσ_m1, hσ_pre, after_of, chars_of, do_]
  have h_pres_m1 :
      mark_present σ ⟨(4, 0), (1, 0), false, (2, 0), true, 0, true⟩ = true := by
    simp [hσ, hσ_m1, hσ_pre, mark_present, marks_of, do_, add]
  have h_pres_m2 :
      mark_present σ ⟨(5, 1), (2, 0), false, (3, 0), true, 0, true⟩ = true := by
    simp [hσ, hσ_m1, hσ_pre, mark_present, marks_of, do_, add]
  have h_cov_m2 :
      in_span_visible σ ⟨(5, 1), (2, 0), false, (3, 0), true, 0, true⟩ (2, 0) := by
    refine ⟨visible_le_refl _ _, ?_⟩
    show visible_le σ (2, 0) (3, 0) ∨
          bold_expand_reach σ ⟨(5, 1), (2, 0), false, (3, 0), true, 0, true⟩ (2, 0)
    exact Or.inl (Or.inr (visible_lt.parent_child h_after_3_2))
  have h_vis : visible σ (2, 0) = true := by
    simp [hσ, hσ_m1, hσ_pre, visible, do_, chars_of, removed_of, add,
          union, _root_.singleton, empty]
  -- Apply Ex 2 with mark₂ as the LWW winner.
  refine partial_overlap_all_adds_formatted_visible σ (2, 0) 0
    ⟨(5, 1), (2, 0), false, (3, 0), true, 0, true⟩
    rfl rfl h_pres_m2 h_cov_m2 h_vis ?_ ?_
  · intro m' h_pres' _ _ h_isAdd_false
    rcases h_uniq m' h_pres' with h_eq | h_eq <;> (subst h_eq; cases h_isAdd_false)
  · -- mark_beats mark₂ mark₁ = decide (opid_max (5,1) (4,0) = (5,1)) = true.
    intro m' h_pres' _ _ _ h_ne
    rcases h_uniq m' h_pres' with h_eq | h_eq
    · subst h_eq; decide
    · exact absurd h_eq h_ne

/-! ## SPOT 8 — Ex 3: different-type Adds coexist (concurrent)

Two concurrent Adds from different replicas (rid=0 bolds, rid=1
italicises). Both formattings hold independently. -/
example :
    let σ_pre := do_ (do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)))
                     (2, 0, app_op_t.Insert 66 (1, 0))
    let σ_b := do_ σ_pre (3, 0, app_op_t.AddMark (1, 0) false (2, 0) true 0)
    let σ := do_ σ_b (4, 1, app_op_t.AddMark (1, 0) false (2, 0) true 1)
    formatted_visible σ (1, 0) 0 = true ∧
    formatted_visible σ (1, 0) 1 = true := by
  set σ_pre := do_ (do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)))
                   (2, 0, app_op_t.Insert 66 (1, 0)) with hσ_pre
  set σ_b := do_ σ_pre (3, 0, app_op_t.AddMark (1, 0) false (2, 0) true 0) with hσ_b
  set σ := do_ σ_b (4, 1, app_op_t.AddMark (1, 0) false (2, 0) true 1) with hσ
  have h_uniq : ∀ m' : MarkOp, mark_present σ m' = true →
      m' = ⟨(3, 0), (1, 0), false, (2, 0), true, 0, true⟩ ∨
      m' = ⟨(4, 1), (1, 0), false, (2, 0), true, 1, true⟩ := by
    intro m' h_pres
    simp [hσ, hσ_b, hσ_pre, mark_present, marks_of, do_, add,
          _root_.singleton, union, empty] at h_pres
    rcases m' with ⟨_, _, _, _, _, _, _⟩
    grind
  have h_after : after_of σ (2, 0) (1, 0) = true := by
    simp only [hσ, hσ_b, hσ_pre, after_of, do_, chars_of, add, union, _root_.singleton,
               Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨66, Or.inr rfl⟩
  have h_pres_mB :
      mark_present σ ⟨(3, 0), (1, 0), false, (2, 0), true, 0, true⟩ = true := by
    simp [hσ, hσ_b, hσ_pre, mark_present, marks_of, do_, add]
  have h_pres_mI :
      mark_present σ ⟨(4, 1), (1, 0), false, (2, 0), true, 1, true⟩ = true := by
    simp [hσ, hσ_b, hσ_pre, mark_present, marks_of, do_, add]
  have h_cov_mB :
      in_span_visible σ ⟨(3, 0), (1, 0), false, (2, 0), true, 0, true⟩ (1, 0) := by
    refine ⟨visible_le_refl _ _, ?_⟩
    show visible_le σ (1, 0) (2, 0) ∨
          bold_expand_reach σ ⟨(3, 0), (1, 0), false, (2, 0), true, 0, true⟩ (1, 0)
    exact Or.inl (Or.inr (visible_lt.parent_child h_after))
  have h_cov_mI :
      in_span_visible σ ⟨(4, 1), (1, 0), false, (2, 0), true, 1, true⟩ (1, 0) := by
    refine ⟨visible_le_refl _ _, ?_⟩
    show visible_le σ (1, 0) (2, 0) ∨
          bold_expand_reach σ ⟨(4, 1), (1, 0), false, (2, 0), true, 1, true⟩ (1, 0)
    exact Or.inl (Or.inr (visible_lt.parent_child h_after))
  have h_vis : visible σ (1, 0) = true := by
    simp [hσ, hσ_b, hσ_pre, visible, do_, chars_of, removed_of, add,
          union, _root_.singleton, empty]
  refine different_type_adds_coexist_visible σ (1, 0)
    ⟨(3, 0), (1, 0), false, (2, 0), true, 0, true⟩
    ⟨(4, 1), (1, 0), false, (2, 0), true, 1, true⟩
    rfl rfl ?_ h_pres_mB h_pres_mI h_cov_mB h_cov_mI h_vis ?_ ?_
  · decide
  · intro m' h_pres' _ h_mt h_ne
    rcases h_uniq m' h_pres' with h_eq | h_eq
    · exact absurd h_eq h_ne
    · subst h_eq
      cases h_mt
  · intro m' h_pres' _ h_mt h_ne
    rcases h_uniq m' h_pres' with h_eq | h_eq
    · subst h_eq
      cases h_mt
    · exact absurd h_eq h_ne

/-! ## SPOT 9 — Ex 5 positive: Add wins over concurrent Remove -/
example :
    let σ_pre := do_ (do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)))
                     (2, 0, app_op_t.Insert 66 (1, 0))
    let σ_a := do_ σ_pre (3, 0, app_op_t.AddMark (1, 0) false (2, 0) true 0)
    let σ := do_ σ_a (4, 1, app_op_t.RemoveMark (1, 0) false (2, 0) true 0)
    formatted_visible σ (1, 0) 0 = true := by
  set σ_pre := do_ (do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)))
                   (2, 0, app_op_t.Insert 66 (1, 0)) with hσ_pre
  set σ_a := do_ σ_pre (3, 0, app_op_t.AddMark (1, 0) false (2, 0) true 0) with hσ_a
  set σ := do_ σ_a (4, 1, app_op_t.RemoveMark (1, 0) false (2, 0) true 0) with hσ
  have h_uniq : ∀ m' : MarkOp, mark_present σ m' = true →
      m' = ⟨(3, 0), (1, 0), false, (2, 0), true, 0, true⟩ ∨
      m' = ⟨(4, 1), (1, 0), false, (2, 0), true, 0, false⟩ := by
    intro m' h_pres
    simp [hσ, hσ_a, hσ_pre, mark_present, marks_of, do_, add,
          _root_.singleton, union, empty] at h_pres
    rcases m' with ⟨_, _, _, _, _, _, _⟩
    grind
  have h_after : after_of σ (2, 0) (1, 0) = true := by
    simp only [hσ, hσ_a, hσ_pre, after_of, do_, chars_of, add, union, _root_.singleton,
               Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨66, Or.inr rfl⟩
  have h_pres_add :
      mark_present σ ⟨(3, 0), (1, 0), false, (2, 0), true, 0, true⟩ = true := by
    simp [hσ, hσ_a, hσ_pre, mark_present, marks_of, do_, add]
  have h_pres_rem :
      mark_present σ ⟨(4, 1), (1, 0), false, (2, 0), true, 0, false⟩ = true := by
    simp [hσ, hσ_a, hσ_pre, mark_present, marks_of, do_, add]
  have h_cov_add :
      in_span_visible σ ⟨(3, 0), (1, 0), false, (2, 0), true, 0, true⟩ (1, 0) := by
    refine ⟨visible_le_refl _ _, ?_⟩
    show visible_le σ (1, 0) (2, 0) ∨
          bold_expand_reach σ ⟨(3, 0), (1, 0), false, (2, 0), true, 0, true⟩ (1, 0)
    exact Or.inl (Or.inr (visible_lt.parent_child h_after))
  have h_cov_rem :
      in_span_visible σ ⟨(4, 1), (1, 0), false, (2, 0), true, 0, false⟩ (1, 0) := by
    refine ⟨visible_le_refl _ _, ?_⟩
    show visible_le σ (1, 0) (2, 0) ∨
          bold_expand_reach σ ⟨(4, 1), (1, 0), false, (2, 0), true, 0, false⟩ (1, 0)
    exact Or.inl (Or.inr (visible_lt.parent_child h_after))
  have h_vis : visible σ (1, 0) = true := by
    simp [hσ, hσ_a, hσ_pre, visible, do_, chars_of, removed_of, add,
          union, _root_.singleton, empty]
  refine add_wins_over_concurrent_remove_visible σ (1, 0) 0
    ⟨(3, 0), (1, 0), false, (2, 0), true, 0, true⟩
    ⟨(4, 1), (1, 0), false, (2, 0), true, 0, false⟩
    rfl rfl rfl rfl h_pres_add h_pres_rem h_cov_add h_cov_rem h_vis ?_
  intro m' h_pres' _ _ h_ne_add h_ne_rem
  rcases h_uniq m' h_pres' with h_eq | h_eq
  · exact absurd h_eq h_ne_add
  · exact absurd h_eq h_ne_rem

end Peritext_SPOT
