import Sal.Interfaces.Set_Extended
import Sal.Interfaces.Map_Extended
import Sal.CRDTs.Peritext.Peritext_CRDT
import Sal.CRDTs.Peritext.Peritext_ReadSide

set_option linter.mathlibStandardSet false

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Classical

/-! # Peritext (CRDT) — SPOTs

CRDT-side mirror of `Sal/MRDTs/Peritext/Peritext_SPOT.lean`. Same
nine scenarios, same theorem-application discharge style; the
state-shape differences (`map`-backed `chars`/`afters`/`deleted`
plus a `set AnchorAttachment` for `marks`, vs the MRDT's flat
sets) only affect how the `after_of` membership facts are proved.

Discharge pattern for `after_of σ c target = true` on a concrete
state: `simp [after_of, do_]` — the existing read-side proofs use
this idiom.

For the SPOTs that need a `mark_present` uniqueness fact
(SPOTs 7-9 covering Ex 2 / Ex 3 / Ex 5-positive), the discharge
pattern is `simp [mark_present, marks_of, do_, add, _root_.singleton,
union, empty] at h_pres; rcases m'; grind`. The `rcases` destructures
`m'` into its 7 fields so `grind` collapses the AnchorAttachment-
injectivity disjunction. The constructed mark must be inlined as a
literal tuple — `let`-binding the MarkOp blocks projection reduction
inside `simp`. -/

namespace Peritext_SPOT

/-! ## SPOT 1 — Insert chain produces `afters_reach` -/
example :
    let σ₀ := do_ init_st (1, 0, app_op_t.Insert 65 (0, 0))   -- 'A' after sentinel
    let σ  := do_ σ₀     (2, 0, app_op_t.Insert 66 (1, 0))    -- 'B' after 'A'
    afters_reach σ (2, 0) (0, 0) := by
  set σ₀ := do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)) with hσ₀
  set σ  := do_ σ₀     (2, 0, app_op_t.Insert 66 (1, 0)) with hσ
  have h_step2 : after_of σ (2, 0) (1, 0) = true := by
    simp [hσ, after_of, do_]
  have h_step1 : after_of σ (1, 0) (0, 0) = true := by
    simp [hσ, hσ₀, after_of, do_, init_st]
  exact afters_reach.step (c_parent := (1, 0)) h_step2
          (afters_reach.step (c_parent := (0, 0)) h_step1 (afters_reach.refl _))

/-! ## SPOT 2 — Ex 8 partial: link-descendant has `visible_lt endId c_new` -/
example :
    let σ₀ := do_ init_st (1, 0, app_op_t.Insert 33 (0, 0))
    let σ  := do_ σ₀     (2, 0, app_op_t.Insert 63 (1, 0))
    let m  : MarkOp := ((10, 0), (0, 0), false, (1, 0), false, 0, true)
    visible_lt σ (mark_endId m) (2, 0) := by
  set σ₀ := do_ init_st (1, 0, app_op_t.Insert 33 (0, 0)) with hσ₀
  set σ  := do_ σ₀     (2, 0, app_op_t.Insert 63 (1, 0)) with hσ
  have h_after : after_of σ (2, 0) (1, 0) = true := by
    simp [hσ, after_of, do_]
  -- mark_endId of the literal mark unfolds to (1, 0).
  show visible_lt σ (1, 0) (2, 0)
  exact ex8_link_descendant_visible_lt_endId σ
    ((10, 0), (0, 0), false, (1, 0), false, 0, true) (2, 0) h_after

/-! ## SPOT 3 — Ex 7: bold-style older sibling is in span -/
example :
    let σ₀ := do_ init_st (1, 0, app_op_t.Insert 65 (0, 0))
    let σ  := do_ σ₀     (2, 0, app_op_t.Insert 66 (0, 0))
    let m  : MarkOp := ((10, 0), (0, 0), false, (1, 0), false, 0, true)
    in_span_visible σ m (2, 0) := by
  set σ₀ := do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)) with hσ₀
  set σ  := do_ σ₀     (2, 0, app_op_t.Insert 66 (0, 0)) with hσ
  have h_after_new : after_of σ (2, 0) (0, 0) = true := by
    simp [hσ, after_of, do_]
  have h_after_end : after_of σ (1, 0) (0, 0) = true := by
    simp [hσ, hσ₀, after_of, do_, init_st]
  refine ex7_bold_older_sibling_in_span σ
    ((10, 0), (0, 0), false, (1, 0), false, 0, true) (0, 0) (2, 0)
    rfl rfl ?_ h_after_new h_after_end ?_ ?_ ?_
  · exact visible_le_refl σ (0, 0)
  · decide
  · decide
  · decide

/-! ## SPOT 4 — Anchors survive tombstones -/
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
    let m  : MarkOp := ((10, 0), (1, 0), false, (2, 0), true, 0, true)
    in_span_visible σ_post m (3, 0) := by
  set σ₀ := do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)) with hσ₀
  set σ_pre := do_ σ₀ (2, 0, app_op_t.Insert 66 (1, 0)) with hσ_pre
  set σ_post := do_ σ_pre (3, 0, app_op_t.Insert 67 (1, 0)) with hσ_post
  let m : MarkOp := ((10, 0), (1, 0), false, (2, 0), true, 0, true)
  -- Freshness premise: (3, 0) is not yet a key in σ_pre's afters map.
  have h_fresh : contains (Prod.fst (Prod.snd σ_pre)) (3, 0) = false := by
    simp [hσ_pre, hσ₀, do_, init_st]
  -- Step 1: in_span_visible σ_pre m (1, 0) (i.e. at the mark's startId).
  have h_after_2_pre : after_of σ_pre (2, 0) (1, 0) = true := by
    simp [hσ_pre, after_of, do_]
  have h_span_pre : in_span_visible σ_pre m (1, 0) := by
    refine ⟨?_, ?_⟩
    · -- m.startSide = false, so visible_le σ_pre m.startId (1,0). m.startId = (1,0).
      show (if (mark_startSide m = true) then visible_lt σ_pre (mark_startId m) (1, 0)
            else visible_le σ_pre (mark_startId m) (1, 0))
      simp only [show mark_startSide m = false from rfl]
      exact visible_le_refl _ _
    · -- m.endSide = true, so visible_le σ_pre (1,0) m.endId ∨ bold_expand_reach.
      show (if (mark_endSide m = true) then
              visible_le σ_pre (1, 0) (mark_endId m) ∨ bold_expand_reach σ_pre m (1, 0)
            else visible_lt σ_pre (1, 0) (mark_endId m))
      simp only [show mark_endSide m = true from rfl, if_true]
      show visible_le σ_pre (1, 0) (2, 0) ∨ bold_expand_reach σ_pre m (1, 0)
      exact Or.inl (Or.inr (visible_lt.parent_child h_after_2_pre))
  -- Step 2: right-side bound on σ_post.
  have h_after_3_post : after_of σ_post (3, 0) (1, 0) = true := by
    simp [hσ_post, after_of, do_]
  have h_after_2_post : after_of σ_post (2, 0) (1, 0) = true := by
    simp [hσ_post, hσ_pre, after_of, do_]
  -- Sibling rule: (3, 0) and (2, 0) are siblings under (1, 0); opid_max picks (3, 0).
  have h_sib : visible_lt σ_post (3, 0) (2, 0) :=
    visible_lt.sibling h_after_3_post h_after_2_post (by decide) (by decide)
  -- Apply Ex 1.
  refine insert_within_span_in_span_visible σ_pre m 3 0 67 (1, 0) h_fresh h_span_pre ?_
  -- Right-side bound for the post-state: m.endSide = true, so visible_le σ_post (3, 0) m.endId.
  show (if (mark_endSide m = true) then visible_le σ_post (3, 0) (mark_endId m)
        else visible_lt σ_post (3, 0) (mark_endId m))
  simp only [show mark_endSide m = true from rfl, if_true]
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
  -- With no AddMark/RemoveMark in σ, marks_of σ ≡ ∅, so mark_present is always false.
  intro m h_pres _ _
  exfalso
  simp only [hσ, mark_present, marks_of, do_, init_st, _root_.empty,
             Bool.or_eq_true] at h_pres
  rcases h_pres with h | h <;> exact Bool.false_ne_true h

/-! ## SPOT 7 — Ex 2: concurrent same-type Adds with overlap

The paper Ex 2 scenario: **two concurrent same-type Adds from
different replicas whose spans partially overlap**, with formatting
holding at a point in the overlap.

Scenario: insert chain `'A'@(1,0) → 'B'@(2,0) → 'C'@(3,0)` (built
on a single replica for brevity). Then two AddMarks, both
`markType = 0` (bold), originating from *different* replicas:
  * `mark₁` at `(ts=4, rid=0)`: bold span `[(1,0), (2,0)]` — A through B.
  * `mark₂` at `(ts=5, rid=1)`: bold span `[(2,0), (3,0)]` — B through C.

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
    -- Two AddMarks from different replicas (rid=0 and rid=1) — concurrent.
    let σ_m1 := do_ σ_pre (4, 0, app_op_t.AddMark (1, 0) false (2, 0) true 0)
    let σ := do_ σ_m1 (5, 1, app_op_t.AddMark (2, 0) false (3, 0) true 0)
    formatted_visible σ (2, 0) 0 = true := by
  set σ_pre := do_ (do_ (do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)))
                        (2, 0, app_op_t.Insert 66 (1, 0)))
                   (3, 0, app_op_t.Insert 67 (2, 0)) with hσ_pre
  set σ_m1 := do_ σ_pre (4, 0, app_op_t.AddMark (1, 0) false (2, 0) true 0) with hσ_m1
  set σ := do_ σ_m1 (5, 1, app_op_t.AddMark (2, 0) false (3, 0) true 0) with hσ
  -- Uniqueness: any mark present in σ is mark₁ or mark₂.
  have h_uniq : ∀ m' : MarkOp, mark_present σ m' = true →
      m' = ((4, 0), (1, 0), false, (2, 0), true, 0, true) ∨
      m' = ((5, 1), (2, 0), false, (3, 0), true, 0, true) := by
    intro m' h_pres
    simp [hσ, hσ_m1, hσ_pre, mark_present, marks_of, do_, add,
          _root_.singleton, union, empty] at h_pres
    rcases m' with ⟨_, _, _, _, _, _, _⟩
    grind
  have h_after_2_1 : after_of σ (2, 0) (1, 0) = true := by
    simp [hσ, hσ_m1, hσ_pre, after_of, do_]
  have h_after_3_2 : after_of σ (3, 0) (2, 0) = true := by
    simp [hσ, hσ_m1, hσ_pre, after_of, do_]
  have h_pres_m1 :
      mark_present σ ((4, 0), (1, 0), false, (2, 0), true, 0, true) = true := by
    simp [hσ, hσ_m1, hσ_pre, mark_present, marks_of, do_, add]
  have h_pres_m2 :
      mark_present σ ((5, 1), (2, 0), false, (3, 0), true, 0, true) = true := by
    simp [hσ, hσ_m1, hσ_pre, mark_present, marks_of, do_, add]
  have h_cov_m1 :
      in_span_visible σ ((4, 0), (1, 0), false, (2, 0), true, 0, true) (2, 0) := by
    refine ⟨?_, ?_⟩
    · show visible_le σ (1, 0) (2, 0)
      exact Or.inr (visible_lt.parent_child h_after_2_1)
    · show visible_le σ (2, 0) (2, 0) ∨
            bold_expand_reach σ ((4, 0), (1, 0), false, (2, 0), true, 0, true) (2, 0)
      exact Or.inl (visible_le_refl _ _)
  have h_cov_m2 :
      in_span_visible σ ((5, 1), (2, 0), false, (3, 0), true, 0, true) (2, 0) := by
    refine ⟨visible_le_refl _ _, ?_⟩
    show visible_le σ (2, 0) (3, 0) ∨
          bold_expand_reach σ ((5, 1), (2, 0), false, (3, 0), true, 0, true) (2, 0)
    exact Or.inl (Or.inr (visible_lt.parent_child h_after_3_2))
  have h_vis : visible σ (2, 0) = true := by
    simp [hσ, hσ_m1, hσ_pre, visible, do_, mysel_d]
  -- Apply Ex 2 with mark₂ as the LWW winner (higher opId beats lower).
  refine partial_overlap_all_adds_formatted_visible σ (2, 0) 0
    ((5, 1), (2, 0), false, (3, 0), true, 0, true)
    rfl rfl h_pres_m2 h_cov_m2 h_vis ?_ ?_
  · -- No-Rem antecedent: every present m' is an Add (both marks have isAdd=true).
    intro m' h_pres' _ _ h_isAdd_false
    rcases h_uniq m' h_pres' with h_eq | h_eq <;> (subst h_eq; cases h_isAdd_false)
  · -- Beats-other-Adds antecedent: m' = mark₁ ∨ mark₂; m' ≠ mark₂ forces m' = mark₁.
    -- mark_beats mark₂ mark₁ = decide (opid_max (5,1) (4,0) = (5,1)) = true.
    intro m' h_pres' _ _ _ h_ne
    rcases h_uniq m' h_pres' with h_eq | h_eq
    · subst h_eq; decide
    · exact absurd h_eq h_ne

/-! ## SPOT 8 — Ex 3: different-type Adds coexist (concurrent)

Paper Ex 3: **two concurrent Adds from different replicas with
distinct `markType`s** (e.g. one user bolds, another italicises a
common region). Both formattings hold independently at the
overlap point. Applies `different_type_adds_coexist_visible`. -/
example :
    let σ_pre := do_ (do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)))
                     (2, 0, app_op_t.Insert 66 (1, 0))
    -- Concurrent AddMarks from rid=0 (bold, mt=0) and rid=1 (italic, mt=1).
    let σ_b := do_ σ_pre (3, 0, app_op_t.AddMark (1, 0) false (2, 0) true 0)
    let σ := do_ σ_b (4, 1, app_op_t.AddMark (1, 0) false (2, 0) true 1)
    formatted_visible σ (1, 0) 0 = true ∧
    formatted_visible σ (1, 0) 1 = true := by
  set σ_pre := do_ (do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)))
                   (2, 0, app_op_t.Insert 66 (1, 0)) with hσ_pre
  set σ_b := do_ σ_pre (3, 0, app_op_t.AddMark (1, 0) false (2, 0) true 0) with hσ_b
  set σ := do_ σ_b (4, 1, app_op_t.AddMark (1, 0) false (2, 0) true 1) with hσ
  have h_uniq : ∀ m' : MarkOp, mark_present σ m' = true →
      m' = ((3, 0), (1, 0), false, (2, 0), true, 0, true) ∨
      m' = ((4, 1), (1, 0), false, (2, 0), true, 1, true) := by
    intro m' h_pres
    simp [hσ, hσ_b, hσ_pre, mark_present, marks_of, do_, add,
          _root_.singleton, union, empty] at h_pres
    rcases m' with ⟨_, _, _, _, _, _, _⟩
    grind
  have h_after : after_of σ (2, 0) (1, 0) = true := by
    simp [hσ, hσ_b, hσ_pre, after_of, do_]
  have h_pres_mB :
      mark_present σ ((3, 0), (1, 0), false, (2, 0), true, 0, true) = true := by
    simp [hσ, hσ_b, hσ_pre, mark_present, marks_of, do_, add]
  have h_pres_mI :
      mark_present σ ((4, 1), (1, 0), false, (2, 0), true, 1, true) = true := by
    simp [hσ, hσ_b, hσ_pre, mark_present, marks_of, do_, add]
  have h_cov_mB :
      in_span_visible σ ((3, 0), (1, 0), false, (2, 0), true, 0, true) (1, 0) := by
    refine ⟨visible_le_refl _ _, ?_⟩
    show visible_le σ (1, 0) (2, 0) ∨
          bold_expand_reach σ ((3, 0), (1, 0), false, (2, 0), true, 0, true) (1, 0)
    exact Or.inl (Or.inr (visible_lt.parent_child h_after))
  have h_cov_mI :
      in_span_visible σ ((4, 1), (1, 0), false, (2, 0), true, 1, true) (1, 0) := by
    refine ⟨visible_le_refl _ _, ?_⟩
    show visible_le σ (1, 0) (2, 0) ∨
          bold_expand_reach σ ((4, 1), (1, 0), false, (2, 0), true, 1, true) (1, 0)
    exact Or.inl (Or.inr (visible_lt.parent_child h_after))
  have h_vis : visible σ (1, 0) = true := by
    simp [hσ, hσ_b, hσ_pre, visible, do_, mysel_d]
  refine different_type_adds_coexist_visible σ (1, 0)
    ((3, 0), (1, 0), false, (2, 0), true, 0, true)
    ((4, 1), (1, 0), false, (2, 0), true, 1, true)
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

/-! ## SPOT 9 — Ex 5 positive: Add wins over concurrent Remove

A state with one AddMark and one RemoveMark of the same markType,
both covering `c`. Under the Sal Add-biased `mark_beats` rule
(`docs/peritext-vs-paper.md`: deliberate departure from paper §4.4),
the Add always wins, so `c` is formatted. Applies
`add_wins_over_concurrent_remove_visible`. -/
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
      m' = ((3, 0), (1, 0), false, (2, 0), true, 0, true) ∨
      m' = ((4, 1), (1, 0), false, (2, 0), true, 0, false) := by
    intro m' h_pres
    simp [hσ, hσ_a, hσ_pre, mark_present, marks_of, do_, add,
          _root_.singleton, union, empty] at h_pres
    rcases m' with ⟨_, _, _, _, _, _, _⟩
    grind
  have h_after : after_of σ (2, 0) (1, 0) = true := by
    simp [hσ, hσ_a, hσ_pre, after_of, do_]
  have h_pres_add :
      mark_present σ ((3, 0), (1, 0), false, (2, 0), true, 0, true) = true := by
    simp [hσ, hσ_a, hσ_pre, mark_present, marks_of, do_, add]
  have h_pres_rem :
      mark_present σ ((4, 1), (1, 0), false, (2, 0), true, 0, false) = true := by
    simp [hσ, hσ_a, hσ_pre, mark_present, marks_of, do_, add]
  have h_cov_add :
      in_span_visible σ ((3, 0), (1, 0), false, (2, 0), true, 0, true) (1, 0) := by
    refine ⟨visible_le_refl _ _, ?_⟩
    show visible_le σ (1, 0) (2, 0) ∨
          bold_expand_reach σ ((3, 0), (1, 0), false, (2, 0), true, 0, true) (1, 0)
    exact Or.inl (Or.inr (visible_lt.parent_child h_after))
  have h_cov_rem :
      in_span_visible σ ((4, 1), (1, 0), false, (2, 0), true, 0, false) (1, 0) := by
    refine ⟨visible_le_refl _ _, ?_⟩
    show visible_le σ (1, 0) (2, 0) ∨
          bold_expand_reach σ ((4, 1), (1, 0), false, (2, 0), true, 0, false) (1, 0)
    exact Or.inl (Or.inr (visible_lt.parent_child h_after))
  have h_vis : visible σ (1, 0) = true := by
    simp [hσ, hσ_a, hσ_pre, visible, do_, mysel_d]
  refine add_wins_over_concurrent_remove_visible σ (1, 0) 0
    ((3, 0), (1, 0), false, (2, 0), true, 0, true)
    ((4, 1), (1, 0), false, (2, 0), true, 0, false)
    rfl rfl rfl rfl h_pres_add h_pres_rem h_cov_add h_cov_rem h_vis ?_
  intro m' h_pres' _ _ h_ne_add h_ne_rem
  rcases h_uniq m' h_pres' with h_eq | h_eq
  · exact absurd h_eq h_ne_add
  · exact absurd h_eq h_ne_rem

end Peritext_SPOT
