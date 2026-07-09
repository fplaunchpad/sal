import Sal.MRDTs.Peritext_with_tombstones.Peritext_DSL

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

open Classical
open Peritext_MRDT_DSL

/-! # Peritext (MRDT) — SPOTs (paper §A.2 examples)

MRDT-side mirror of `Sal/CRDTs/Peritext/Peritext_SPOT.lean`. Same
paper §A.2 examples, paper-exact text, MRDT substrate. -/

namespace Peritext_SPOT

@[simp] def the_fox_jumped : Scenario :=
  Scenario.empty.insertChars 0
    ['T', 'h', 'e', ' ', 'f', 'o', 'x', ' ', 'j', 'u', 'm', 'p', 'e', 'd']

theorem chain_vlt (s : concrete_st) (i j : Nat) (h_lt : i < j)
    (h_after : ∀ k, i ≤ k → k < j → after_of s (k + 1, 0) (k, 0) = true) :
    visible_lt s (i, 0) (j, 0) :=
  afters_reach_to_visible_lt s (j, 0) (i, 0)
    (chain_reach s i j (Nat.le_of_lt h_lt) h_after)
    (fun h => by injection h with h1 _; omega)

/-! ## Example 1 — Concurrent formatting and insertion (§3.1) -/

@[simp] def ex1_pre : Scenario :=
  the_fox_jumped.bold 0
    ['T', 'h', 'e', ' ', 'f', 'o', 'x', ' ', 'j', 'u', 'm', 'p', 'e', 'd']

@[simp] def ex1_post : Scenario := ex1_pre.insertCharAfter 1 (4, 0) 'b'

@[simp] def ex1_mark : MarkOp :=
  (Mark.bold (15, 0) (1, 0) (14, 0))

example : in_span_visible ex1_post.state ex1_mark (16, 1) := by
  have h_fresh : ∀ t ch, Prod.fst ex1_pre.state ((16, 1), t, ch) = false := by
    intro t ch; simp +decide
  have h_vlt_T_space : visible_lt ex1_pre.state (1, 0) (4, 0) :=
    chain_vlt _ 1 4 (by decide) (fun k _ _ => by interval_cases k <;> simp [after_of])
  have h_vlt_space_d : visible_lt ex1_pre.state (4, 0) (14, 0) :=
    chain_vlt _ 4 14 (by decide) (fun k _ _ => by interval_cases k <;> simp [after_of])
  have h_span_pre : in_span_visible ex1_pre.state ex1_mark (4, 0) := by
    refine ⟨Or.inr h_vlt_T_space, ?_⟩
    show visible_le ex1_pre.state (4, 0) (14, 0) ∨ _
    exact Or.inl (Or.inr h_vlt_space_d)
  have h_after_b : after_of ex1_post.state (16, 1) (4, 0) = true := by simp [after_of]
  have h_after_f : after_of ex1_post.state (5, 0) (4, 0) = true := by simp [after_of]
  have h_sib : visible_lt ex1_post.state (16, 1) (5, 0) :=
    visible_lt.sibling h_after_b h_after_f (by decide) (by decide)
  have h_vlt_f_d : visible_lt ex1_post.state (5, 0) (14, 0) :=
    chain_vlt _ 5 14 (by decide) (fun k _ _ => by interval_cases k <;> simp [after_of])
  have h_vlt_b_d : visible_lt ex1_post.state (16, 1) (14, 0) :=
    visible_lt.trans h_sib h_vlt_f_d
  refine insert_within_span_in_span_visible ex1_pre.state ex1_mark 16 1 98 (4, 0)
    h_fresh h_span_pre ?_
  show (if ex1_mark.endSide = true
        then visible_le ex1_post.state (16, 1) ex1_mark.endId
        else visible_lt ex1_post.state (16, 1) ex1_mark.endId)
  simp only [show ex1_mark.endSide = true from rfl, if_true]
  exact Or.inr h_vlt_b_d

/-! ## Example 2 — Overlapping same-type formatting (§3.2) -/

@[simp] def ex2_state : Scenario :=
  the_fox_jumped
    |>.bold 0 ['T', 'h', 'e', ' ', 'f', 'o', 'x']
    |>.bold 1 ['f', 'o', 'x', ' ', 'j', 'u', 'm', 'p', 'e', 'd']

example : ex2_state.boldAt 5 = true := by
  show formatted_visible ex2_state.state (6, 0) 0 = true
  have h_uniq : ∀ m' : MarkOp, mark_present ex2_state.state m' = true →
      m' = (Mark.bold (15, 0) (1, 0) (7, 0)) ∨
      m' = (Mark.bold (16, 1) (5, 0) (14, 0)) := by
    intro m' h_pres
    simp +decide [mark_present, marks_of, do_, add, _root_.singleton, union, empty]
      at h_pres
    simp only [Mark.bold, Mark.unbold, Mark.italic, Mark.link, Mark.mk, Anchor.toBool]
    rcases m' with ⟨_, _, _, _, _, _, _⟩
    grind
  have h_pres_M2 :
      mark_present ex2_state.state (Mark.bold (16, 1) (5, 0) (14, 0)) = true := by
    simp +decide
  have h_after_o_f : after_of ex2_state.state (6, 0) (5, 0) = true := by simp [after_of]
  have h_vlt_o_d : visible_lt ex2_state.state (6, 0) (14, 0) :=
    chain_vlt _ 6 14 (by decide) (fun k _ _ => by interval_cases k <;> simp [after_of])
  have h_cov_M2 :
      in_span_visible ex2_state.state (Mark.bold (16, 1) (5, 0) (14, 0)) (6, 0) := by
    refine ⟨Or.inr (visible_lt.parent_child h_after_o_f), ?_⟩
    show visible_le ex2_state.state (6, 0) (14, 0) ∨ _
    exact Or.inl (Or.inr h_vlt_o_d)
  have h_vis : visible ex2_state.state (6, 0) = true := by simp [visible]
  refine partial_overlap_all_adds_formatted_visible ex2_state.state (6, 0) 0
    (Mark.bold (16, 1) (5, 0) (14, 0)) rfl rfl h_pres_M2 h_cov_M2 h_vis ?_ ?_
  · intro m' h_pres' _ _ h_isAdd_false
    rcases h_uniq m' h_pres' with h_eq | h_eq <;> (subst h_eq; cases h_isAdd_false)
  · intro m' h_pres' _ _ _ h_ne
    rcases h_uniq m' h_pres' with h_eq | h_eq
    · subst h_eq; decide
    · exact absurd h_eq h_ne

/-! ## Example 3 — Different mark types coexist (§3.2) -/

@[simp] def ex3_state : Scenario :=
  the_fox_jumped
    |>.addMark 0 0 ['T', 'h', 'e', ' ', 'f', 'o', 'x']
    |>.addMark 1 1 ['f', 'o', 'x', ' ', 'j', 'u', 'm', 'p', 'e', 'd']

example : ex3_state.boldAt 5 = true ∧ ex3_state.formattedAt 5 1 = true := by
  show formatted_visible ex3_state.state (6, 0) 0 = true ∧
       formatted_visible ex3_state.state (6, 0) 1 = true
  have h_uniq : ∀ m' : MarkOp, mark_present ex3_state.state m' = true →
      m' = (Mark.bold (15, 0) (1, 0) (7, 0)) ∨
      m' = (Mark.italic (16, 1) (5, 0) (14, 0)) := by
    intro m' h_pres
    simp +decide [mark_present, marks_of, do_, add, _root_.singleton, union, empty]
      at h_pres
    simp only [Mark.bold, Mark.unbold, Mark.italic, Mark.link, Mark.mk, Anchor.toBool]
    rcases m' with ⟨_, _, _, _, _, _, _⟩
    grind
  have h_pres_mB :
      mark_present ex3_state.state (Mark.bold (15, 0) (1, 0) (7, 0)) = true := by
    simp +decide
  have h_pres_mI :
      mark_present ex3_state.state (Mark.italic (16, 1) (5, 0) (14, 0)) = true := by
    simp +decide
  have h_vlt_T_o : visible_lt ex3_state.state (1, 0) (6, 0) :=
    chain_vlt _ 1 6 (by decide) (fun k _ _ => by interval_cases k <;> simp [after_of])
  have h_vlt_o_x : visible_lt ex3_state.state (6, 0) (7, 0) :=
    chain_vlt _ 6 7 (by decide) (fun k _ _ => by interval_cases k; simp [after_of])
  have h_vlt_f_o : visible_lt ex3_state.state (5, 0) (6, 0) :=
    chain_vlt _ 5 6 (by decide) (fun k _ _ => by interval_cases k; simp [after_of])
  have h_vlt_o_d : visible_lt ex3_state.state (6, 0) (14, 0) :=
    chain_vlt _ 6 14 (by decide) (fun k _ _ => by interval_cases k <;> simp [after_of])
  have h_cov_mB :
      in_span_visible ex3_state.state (Mark.bold (15, 0) (1, 0) (7, 0)) (6, 0) := by
    refine ⟨Or.inr h_vlt_T_o, ?_⟩
    show visible_le ex3_state.state (6, 0) (7, 0) ∨ _
    exact Or.inl (Or.inr h_vlt_o_x)
  have h_cov_mI :
      in_span_visible ex3_state.state (Mark.italic (16, 1) (5, 0) (14, 0)) (6, 0) := by
    refine ⟨Or.inr h_vlt_f_o, ?_⟩
    show visible_le ex3_state.state (6, 0) (14, 0) ∨ _
    exact Or.inl (Or.inr h_vlt_o_d)
  have h_vis : visible ex3_state.state (6, 0) = true := by simp [visible]
  refine different_type_adds_coexist_visible ex3_state.state (6, 0)
    (Mark.bold (15, 0) (1, 0) (7, 0))
    (Mark.italic (16, 1) (5, 0) (14, 0))
    rfl rfl ?_ h_pres_mB h_pres_mI h_cov_mB h_cov_mI h_vis ?_ ?_
  · decide
  · intro m' h_pres' _ h_mt h_ne
    rcases h_uniq m' h_pres' with h_eq | h_eq
    · exact absurd h_eq h_ne
    · subst h_eq; cases h_mt
  · intro m' h_pres' _ h_mt h_ne
    rcases h_uniq m' h_pres' with h_eq | h_eq
    · subst h_eq; cases h_mt
    · exact absurd h_eq h_ne

/-! ## Example 5 — Conflicting bold and non-bold (§3.2.1) -/

@[simp] def ex5_state : Scenario :=
  the_fox_jumped
    |>.bold   0 ['T', 'h', 'e', ' ', 'f', 'o', 'x', ' ', 'j', 'u', 'm', 'p', 'e', 'd']
    |>.unbold 0 ['f', 'o', 'x', ' ', 'j', 'u', 'm', 'p', 'e', 'd']
    |>.bold   1 ['j', 'u', 'm', 'p', 'e', 'd']

example : ex5_state.boldAt 8 = true := by
  show formatted_visible ex5_state.state (9, 0) 0 = true
  have h_uniq : ∀ m' : MarkOp, mark_present ex5_state.state m' = true →
      m' = (Mark.bold (15, 0) (1, 0) (14, 0)) ∨
      m' = (Mark.unbold (16, 0) (5, 0) (14, 0)) ∨
      m' = (Mark.bold (17, 1) (9, 0) (14, 0)) := by
    intro m' h_pres
    simp +decide [mark_present, marks_of, do_, add, _root_.singleton, union, empty]
      at h_pres
    simp only [Mark.bold, Mark.unbold, Mark.italic, Mark.link, Mark.mk, Anchor.toBool]
    rcases m' with ⟨_, _, _, _, _, _, _⟩
    grind
  have h_pres_M2 :
      mark_present ex5_state.state (Mark.unbold (16, 0) (5, 0) (14, 0)) = true := by
    simp +decide
  have h_pres_M3 :
      mark_present ex5_state.state (Mark.bold (17, 1) (9, 0) (14, 0)) = true := by
    simp +decide
  have h_vlt_j_d : visible_lt ex5_state.state (9, 0) (14, 0) :=
    chain_vlt _ 9 14 (by decide) (fun k _ _ => by interval_cases k <;> simp [after_of])
  have h_vlt_f_j : visible_lt ex5_state.state (5, 0) (9, 0) :=
    chain_vlt _ 5 9 (by decide) (fun k _ _ => by interval_cases k <;> simp [after_of])
  have h_cov_M3 :
      in_span_visible ex5_state.state (Mark.bold (17, 1) (9, 0) (14, 0)) (9, 0) := by
    refine ⟨visible_le_refl _ _, ?_⟩
    show visible_le ex5_state.state (9, 0) (14, 0) ∨ _
    exact Or.inl (Or.inr h_vlt_j_d)
  have h_cov_M2 :
      in_span_visible ex5_state.state (Mark.unbold (16, 0) (5, 0) (14, 0)) (9, 0) := by
    refine ⟨Or.inr h_vlt_f_j, ?_⟩
    show visible_le ex5_state.state (9, 0) (14, 0) ∨ _
    exact Or.inl (Or.inr h_vlt_j_d)
  have h_vis : visible ex5_state.state (9, 0) = true := by simp [visible]
  refine add_wins_over_concurrent_remove_visible ex5_state.state (9, 0) 0
    (Mark.bold (17, 1) (9, 0) (14, 0))
    (Mark.unbold (16, 0) (5, 0) (14, 0))
    rfl rfl rfl rfl h_pres_M3 h_pres_M2 h_cov_M3 h_cov_M2 h_vis ?_
  intro m' h_pres' _ _ h_ne_M3
  rcases h_uniq m' h_pres' with h_eq | h_eq | h_eq
  · subst h_eq; decide
  · subst h_eq; decide
  · exact absurd h_eq h_ne_M3

/-! ## Example 7 — Bold-boundary insertion expands (§3.3) -/

@[simp] def ex7_pre : Scenario :=
  the_fox_jumped.bold 0 ['f', 'o', 'x', ' ', 'j', 'u', 'm', 'p', 'e', 'd']

@[simp] def ex7_mark : MarkOp :=
  (Mark.bold (15, 0) (5, 0) (14, 0))

@[simp] def ex7_post : Scenario := ex7_pre.insertCharAfter 0 (8, 0) 'X'

example : in_span_visible ex7_post.state ex7_mark (16, 0) := by
  have h_after_X : after_of ex7_post.state (16, 0) (8, 0) = true := by simp [after_of]
  have h_after_j : after_of ex7_post.state (9, 0) (8, 0) = true := by simp [after_of]
  have h_sib : visible_lt ex7_post.state (16, 0) (9, 0) :=
    visible_lt.sibling h_after_X h_after_j (by decide) (by decide)
  have h_vlt_f_space : visible_lt ex7_post.state (5, 0) (8, 0) :=
    chain_vlt _ 5 8 (by decide) (fun k _ _ => by interval_cases k <;> simp [after_of])
  have h_vlt_space_X : visible_lt ex7_post.state (8, 0) (16, 0) :=
    visible_lt.parent_child h_after_X
  have h_vlt_f_X : visible_lt ex7_post.state (5, 0) (16, 0) :=
    visible_lt.trans h_vlt_f_space h_vlt_space_X
  refine ⟨Or.inr h_vlt_f_X, ?_⟩
  show visible_le ex7_post.state (16, 0) (14, 0) ∨ bold_expand_reach ex7_post.state ex7_mark (16, 0)
  have h_vlt_j_d : visible_lt ex7_post.state (9, 0) (14, 0) :=
    chain_vlt _ 9 14 (by decide) (fun k _ _ => by interval_cases k <;> simp [after_of])
  exact Or.inl (Or.inr (visible_lt.trans h_sib h_vlt_j_d))

/-! ## Example 8 — Link-boundary insertion does not expand (§3.3) -/

@[simp] def ex8_state : Scenario := the_fox_jumped

@[simp] def ex8_mark : MarkOp :=
  (Mark.link (10, 0) (0, 0) (14, 0))

@[simp] def ex8_post : Scenario := ex8_state.insertCharAfter 0 (14, 0) 'X'

example : visible_lt ex8_post.state ex8_mark.endId (15, 0) := by
  have h_after : after_of ex8_post.state (15, 0) (14, 0) = true := by simp [after_of]
  show visible_lt ex8_post.state (14, 0) (15, 0)
  exact ex8_link_descendant_visible_lt_endId ex8_post.state ex8_mark (15, 0) h_after

end Peritext_SPOT
