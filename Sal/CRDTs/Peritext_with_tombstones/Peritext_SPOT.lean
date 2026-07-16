import Sal.CRDTs.Peritext_with_tombstones.Peritext_DSL

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Classical
open Peritext_DSL

/-! # Peritext (CRDT) — SPOTs (paper §A.2 examples)

Each SPOT mirrors a paper §A.2 example *exactly*: the same text
("The fox jumped"), the same actor names (Alice = rid 0, Bob = rid 1),
the same mark ranges, the same concurrent inserts.

OpId table after `the_fox_jumped`:
```
T=(1,0)  h=(2,0)  e=(3,0)  ' '=(4,0)  f=(5,0)  o=(6,0)  x=(7,0)
' '=(8,0) j=(9,0) u=(10,0) m=(11,0) p=(12,0) e=(13,0) d=(14,0)
```

Discharge style: DSL builders are `@[simp]`, so `simp +decide`
reduces a DSL-built state to its `do_` chain and evaluates
`after_of` / `mark_present` / `visible` on concrete inputs.
`chain_reach` builds long `afters_reach` chains in one line. -/

namespace Peritext_SPOT

/-- The base sentence "The fox jumped" typed by Alice. Used by every
example. 14 chars, OpIds (1, 0) … (14, 0). -/
@[simp] noncomputable def the_fox_jumped : Scenario :=
  Scenario.empty.insertChars 0
    ['T', 'h', 'e', ' ', 'f', 'o', 'x', ' ', 'j', 'u', 'm', 'p', 'e', 'd']

/-- Build `visible_lt s (i, 0) (j, 0)` for a chained state via
`chain_reach` + `causal_order_visible_lt`. -/
theorem chain_vlt (s : concrete_st) (i j : Nat) (h_lt : i < j)
    (h_after : ∀ k, i ≤ k → k < j → after_of s (k + 1, 0) (k, 0) = true) :
    visible_lt s (i, 0) (j, 0) :=
  afters_reach_to_visible_lt s (j, 0) (i, 0)
    (chain_reach s i j (Nat.le_of_lt h_lt) h_after)
    (fun h => by injection h with h1 _; omega)

/-! ## Example 1 — Concurrent formatting and insertion (§3.1)

> Alice makes the entire text bold while Bob inserts the word
> "brown" in the middle. Outcome: "**The brown fox jumped.**" —
> the entire text, including "brown", is bold. -/

@[simp] noncomputable def ex1_pre : Scenario :=
  the_fox_jumped.bold 0
    ['T', 'h', 'e', ' ', 'f', 'o', 'x', ' ', 'j', 'u', 'm', 'p', 'e', 'd']

/-- Bob (rid = 1) inserts the first letter of "brown" between
"The " and "fox" — afterId = the space at (4, 0). -/
@[simp] noncomputable def ex1_post : Scenario :=
  ex1_pre.insertCharAfter 1 (4, 0) 'b'

/-- Alice's bold mark over the entire sentence, opId (15, 0). -/
@[simp] noncomputable def ex1_mark : MarkOp := Mark.bold (15, 0) (1, 0) (14, 0)

/-- Bob's inserted 'b' is in Alice's bold span. -/
example : in_span_visible ex1_post.state ex1_mark (16, 1) := by
  have h_fresh : contains (Prod.fst (Prod.snd ex1_pre.state)) (16, 1) = false := by
    simp +decide
  have h_vlt_T_space : visible_lt ex1_pre.state (1, 0) (4, 0) :=
    chain_vlt _ 1 4 (by decide) (fun k _ _ => by interval_cases k <;> simp +decide)
  have h_vlt_space_d : visible_lt ex1_pre.state (4, 0) (14, 0) :=
    chain_vlt _ 4 14 (by decide) (fun k _ _ => by interval_cases k <;> simp +decide)
  have h_span_pre : in_span_visible ex1_pre.state ex1_mark (4, 0) := by
    refine ⟨Or.inr h_vlt_T_space, ?_⟩
    show visible_le ex1_pre.state (4, 0) (14, 0) ∨ _
    exact Or.inl (Or.inr h_vlt_space_d)
  have h_after_b : after_of ex1_post.state (16, 1) (4, 0) = true := by simp +decide
  have h_after_f : after_of ex1_post.state (5, 0) (4, 0) = true := by simp +decide
  have h_sib : visible_lt ex1_post.state (16, 1) (5, 0) :=
    visible_lt.sibling h_after_b h_after_f (by decide) (by decide)
  have h_vlt_f_d : visible_lt ex1_post.state (5, 0) (14, 0) :=
    chain_vlt _ 5 14 (by decide) (fun k _ _ => by interval_cases k <;> simp +decide)
  have h_vlt_b_d : visible_lt ex1_post.state (16, 1) (14, 0) :=
    visible_lt.trans h_sib h_vlt_f_d
  refine insert_within_span_in_span_visible ex1_pre.state ex1_mark 16 1 98 (4, 0)
    h_fresh h_span_pre ?_
  show (if mark_endSide ex1_mark = true
        then visible_le ex1_post.state (16, 1) (mark_endId ex1_mark)
        else visible_lt ex1_post.state (16, 1) (mark_endId ex1_mark))
  simp only [show mark_endSide ex1_mark = true from rfl, if_true]
  exact Or.inr h_vlt_b_d

/-! ## Example 2 — Overlapping same-type formatting (§3.2)

> Alice bolds the first two words ("The fox") while Bob bolds the
> last two words ("fox jumped"). Outcome: the whole text is bold;
> overlap is "fox". -/

@[simp] noncomputable def ex2_state : Scenario :=
  the_fox_jumped
    |>.bold 0 ['T', 'h', 'e', ' ', 'f', 'o', 'x']
    |>.bold 1 ['f', 'o', 'x', ' ', 'j', 'u', 'm', 'p', 'e', 'd']

/-- 'o' of "fox" (position 5, OpId (6, 0)) is bold at the overlap. -/
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
  have h_after_o_f : after_of ex2_state.state (6, 0) (5, 0) = true := by simp +decide
  have h_vlt_o_d : visible_lt ex2_state.state (6, 0) (14, 0) :=
    chain_vlt _ 6 14 (by decide) (fun k _ _ => by interval_cases k <;> simp +decide)
  have h_cov_M2 :
      in_span_visible ex2_state.state (Mark.bold (16, 1) (5, 0) (14, 0)) (6, 0) := by
    refine ⟨Or.inr (visible_lt.parent_child h_after_o_f), ?_⟩
    show visible_le ex2_state.state (6, 0) (14, 0) ∨ _
    exact Or.inl (Or.inr h_vlt_o_d)
  have h_vis : visible ex2_state.state (6, 0) = true := by simp +decide
  refine partial_overlap_all_adds_formatted_visible ex2_state.state (6, 0) 0
    (Mark.bold (16, 1) (5, 0) (14, 0)) rfl rfl h_pres_M2 h_cov_M2 h_vis ?_ ?_
  · intro m' h_pres' _ _ h_isAdd_false
    rcases h_uniq m' h_pres' with h_eq | h_eq <;> (subst h_eq; cases h_isAdd_false)
  · intro m' h_pres' _ _ _ h_ne
    rcases h_uniq m' h_pres' with h_eq | h_eq
    · subst h_eq; decide
    · exact absurd h_eq h_ne

/-! ## Example 3 — Different mark types coexist (§3.2)

> Alice bolds "The fox" while Bob makes "fox jumped" italic.
> Outcome: "The" bold, "fox" both bold and italic, "jumped" italic. -/

@[simp] noncomputable def ex3_state : Scenario :=
  the_fox_jumped
    |>.addMark 0 0 ['T', 'h', 'e', ' ', 'f', 'o', 'x']            -- alice: bold
    |>.addMark 1 1 ['f', 'o', 'x', ' ', 'j', 'u', 'm', 'p', 'e', 'd']  -- bob:   italic

/-- 'o' of "fox" is both bold (markType 0) and italic (markType 1). -/
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
    chain_vlt _ 1 6 (by decide) (fun k _ _ => by interval_cases k <;> simp +decide)
  have h_vlt_o_x : visible_lt ex3_state.state (6, 0) (7, 0) :=
    chain_vlt _ 6 7 (by decide) (fun k _ _ => by interval_cases k; simp +decide)
  have h_vlt_f_o : visible_lt ex3_state.state (5, 0) (6, 0) :=
    chain_vlt _ 5 6 (by decide) (fun k _ _ => by interval_cases k; simp +decide)
  have h_vlt_o_d : visible_lt ex3_state.state (6, 0) (14, 0) :=
    chain_vlt _ 6 14 (by decide) (fun k _ _ => by interval_cases k <;> simp +decide)
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
  have h_vis : visible ex3_state.state (6, 0) = true := by simp +decide
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

/-! ## Example 5 — Conflicting bold and non-bold (§3.2.1)

> Alice bolds the entire text "The fox jumped", then unbolds
> "fox jumped"; Bob concurrently bolds "jumped". Outcome (paper:
> "arbitrary deterministic" via opId LWW): "**The** fox **jumped**". -/

@[simp] noncomputable def ex5_state : Scenario :=
  the_fox_jumped
    |>.bold   0 ['T', 'h', 'e', ' ', 'f', 'o', 'x', ' ', 'j', 'u', 'm', 'p', 'e', 'd']
    |>.unbold 0 ['f', 'o', 'x', ' ', 'j', 'u', 'm', 'p', 'e', 'd']
    |>.bold   1 ['j', 'u', 'm', 'p', 'e', 'd']

/-- 'j' of "jumped" (position 8, OpId (9, 0)) is bold — Bob's
mark M3 has the highest opId and is an Add, so it wins by LWW. -/
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
    chain_vlt _ 9 14 (by decide) (fun k _ _ => by interval_cases k <;> simp +decide)
  have h_vlt_f_j : visible_lt ex5_state.state (5, 0) (9, 0) :=
    chain_vlt _ 5 9 (by decide) (fun k _ _ => by interval_cases k <;> simp +decide)
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
  have h_vis : visible ex5_state.state (9, 0) = true := by simp +decide
  refine add_wins_over_concurrent_remove_visible ex5_state.state (9, 0) 0
    (Mark.bold (17, 1) (9, 0) (14, 0))
    (Mark.unbold (16, 0) (5, 0) (14, 0))
    rfl rfl rfl rfl h_pres_M3 h_pres_M2 h_cov_M3 h_cov_M2 h_vis ?_
  intro m' h_pres' _ _ h_ne_M3
  rcases h_uniq m' h_pres' with h_eq | h_eq | h_eq
  · subst h_eq; decide   -- m' = M1, opid_max (17, 1) (15, 0) = (17, 1)
  · subst h_eq; decide   -- m' = M2, opid_max (17, 1) (16, 0) = (17, 1)
  · exact absurd h_eq h_ne_M3

/-! ## Example 7 — Bold-boundary insertion expands (§3.3)

> Pre: "The **fox jumped**." Alice inserts "quick " before the
> bold span and " over the dog" after. Outcome:
> "The quick **fox jumped over the dog**." — bold expands to
> include " over the dog".

This SPOT exhibits the cross-sibling case: a concurrent insert
that lands as an older sibling of `endId = d` (here, sibling of
`j` under the space at (8, 0)) is in the bold span by the
visible-order sibling rule. -/

@[simp] noncomputable def ex7_pre : Scenario :=
  the_fox_jumped.bold 0 ['f', 'o', 'x', ' ', 'j', 'u', 'm', 'p', 'e', 'd']

@[simp] noncomputable def ex7_mark : MarkOp :=
  (Mark.bold (15, 0) (5, 0) (14, 0))

@[simp] noncomputable def ex7_post : Scenario :=
  ex7_pre.insertCharAfter 0 (8, 0) 'X'

example : in_span_visible ex7_post.state ex7_mark (16, 0) := by
  have h_after_X : after_of ex7_post.state (16, 0) (8, 0) = true := by simp +decide
  have h_after_j : after_of ex7_post.state (9, 0) (8, 0) = true := by simp +decide
  have h_sib : visible_lt ex7_post.state (16, 0) (9, 0) :=
    visible_lt.sibling h_after_X h_after_j (by decide) (by decide)
  have h_vlt_f_space : visible_lt ex7_post.state (5, 0) (8, 0) :=
    chain_vlt _ 5 8 (by decide) (fun k _ _ => by interval_cases k <;> simp +decide)
  have h_vlt_space_X : visible_lt ex7_post.state (8, 0) (16, 0) :=
    visible_lt.parent_child h_after_X
  have h_vlt_f_X : visible_lt ex7_post.state (5, 0) (16, 0) :=
    visible_lt.trans h_vlt_f_space h_vlt_space_X
  refine ⟨Or.inr h_vlt_f_X, ?_⟩
  show visible_le ex7_post.state (16, 0) (14, 0) ∨ bold_expand_reach ex7_post.state ex7_mark (16, 0)
  have h_vlt_j_d : visible_lt ex7_post.state (9, 0) (14, 0) :=
    chain_vlt _ 9 14 (by decide) (fun k _ _ => by interval_cases k <;> simp +decide)
  exact Or.inl (Or.inr (visible_lt.trans h_sib h_vlt_j_d))

/-! ## Example 8 — Link-boundary insertion does not expand (§3.3)

> Same scenario as Ex 7 but with "fox jumped" as a link. Outcome:
> "The quick fox jumped over the dog." with only "fox jumped" still
> a link — the link does not expand to include " over the dog".

This SPOT exhibits the visible-order property underpinning the
exclusion: a new char inserted with `endId` as its parent comes
*after* `endId` in visible order, so the contracting (`endSide
= false`) span excludes it. -/

@[simp] noncomputable def ex8_state : Scenario := the_fox_jumped

@[simp] noncomputable def ex8_mark : MarkOp :=
  (Mark.link (10, 0) (0, 0) (14, 0))

/-- A new char inserted with `endId = d = (14, 0)` as its parent
comes after `endId` in visible order. -/
@[simp] noncomputable def ex8_post : Scenario :=
  ex8_state.insertCharAfter 0 (14, 0) 'X'

example : visible_lt ex8_post.state (mark_endId ex8_mark) (15, 0) := by
  have h_after : after_of ex8_post.state (15, 0) (14, 0) = true := by simp +decide
  show visible_lt ex8_post.state (14, 0) (15, 0)
  exact ex8_link_descendant_visible_lt_endId ex8_post.state ex8_mark (15, 0) h_after

/-! ## Negative companion (should-FAIL pin)

Mark-level negatives (`boldAt … = false`) require inversion on the
inductive `visible_lt` and belong to the ReadSide theorem layer; the
SPOT-sized pin is at the visibility read: the scenario states are
finite and the read is not constantly true on them. -/

/-- A never-inserted OpId is invisible in the paper's base state. -/
example : visible the_fox_jumped.state (99, 7) = false := by
  simp [visible, do_, init_st]

end Peritext_SPOT
