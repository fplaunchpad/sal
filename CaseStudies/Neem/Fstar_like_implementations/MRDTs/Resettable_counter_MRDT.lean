import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Linarith
import CaseStudies.Neem_interfaces.Set_extended


import Plausible

import Blaster

-- State tracks: (current_count, number_of_resets)
-- The reset counter helps merge detect which branch had more recent resets
structure concrete_st where
  count : Int
  reset_count : ℕ
deriving BEq, Repr, DecidableEq

@[simp]
def init_st: concrete_st := ⟨0, 0⟩

@[simp]
def eq (a b: concrete_st) := (a.count = b.count ∧ a.reset_count = b.reset_count)

inductive app_op_t : Type where
| Incr
| Reset
deriving BEq, DecidableEq

abbrev op_t:= ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2: op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o: op_t) :=
match o with
| (_, (rid, _)) => rid

@[simp]
def get_app_op (o: op_t) :=
match o with
| (_, (_, app_op)) => app_op

@[simp]
def get_ts (o: op_t) : ℕ :=
match o with
| (ts, _) => ts

@[simp]
def do_ (s: concrete_st) (o: op_t) : concrete_st :=
match get_app_op o with
| app_op_t.Incr => ⟨s.count + 1, s.reset_count⟩
| app_op_t.Reset => ⟨0, s.reset_count + 1⟩

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

-- Reset-first semantics: Reset operations take precedence
@[simp]
def rc (o1 o2: op_t) : rc_res :=
match get_app_op o1, get_app_op o2 with
| app_op_t.Reset, app_op_t.Reset => rc_res.Either  -- Both resets, order doesn't matter
| app_op_t.Reset, app_op_t.Incr => rc_res.Fst_then_snd  -- Reset before increment
| app_op_t.Incr, app_op_t.Reset => rc_res.Snd_then_fst  -- Reset before increment
| app_op_t.Incr, app_op_t.Incr => rc_res.Either  -- Both increments commute

@[simp]
def merge (l a b: concrete_st) : concrete_st :=
  let a_resets := a.reset_count - l.reset_count  -- resets on branch a since LCA
  let b_resets := b.reset_count - l.reset_count  -- resets on branch b since LCA
  if a_resets > 0 && b_resets = 0 then
    -- Only branch a had resets
    a
  else if b_resets > 0 && a_resets = 0 then
    -- Only branch b had resets
    b
  else if a_resets > 0 && b_resets > 0 then
    -- Both branches had resets after LCA
    if a_resets > b_resets then
      -- Branch a had more resets
      a
    else if b_resets > a_resets then
      -- Branch b had more resets
      b
    else
      -- Same number of resets on both branches - merge the increments
      ⟨a.count + b.count - l.count, a.reset_count⟩
  else
    -- No resets on either branch since LCA - standard counter merge
    ⟨a.count + b.count - l.count, a.reset_count⟩

@[simp]
def commutes_with (o1 o2: op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)


theorem rc_non_comm (o1: op_t) (o2: op_t):
distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2
→
(rc o1 o2 = rc_res.Either ↔ commutes_with o1 o2) := by
dsimp
neem





theorem no_rc_chain (o1 : op_t) (o2 : op_t) (o3 : op_t) :
(distinct_ops o1 o2 ∧ distinct_ops o2 o3)
→ (¬(rc o1 o2 = rc_res.Fst_then_snd ∧ rc o2 o3 = rc_res.Fst_then_snd))
:= by
dsimp
blaster

theorem cond_comm_base (s: concrete_st) (o1: op_t) (o2: op_t) (o3: op_t) :
(distinct_ops o1 o2 ∧ distinct_ops o2 o3 ∧ distinct_ops o1 o3
    ∧ rc o1 o2 = rc_res.Fst_then_snd ∧ ¬(rc o2 o3 = rc_res.Either))
→
eq (do_ (do_ (do_ s o1) o2) o3) (do_ (do_ (do_ s o2) o1) o3) := by
dsimp
neem

theorem  merge_comm (l: concrete_st) (a: concrete_st) (b: concrete_st) :
eq (merge l a b) (merge l b a) := by
dsimp
neem

theorem merge_idem (s: concrete_st):
eq (merge s s s) s := by
dsimp
neem

theorem base_2op (o1: op_t) (o2: op_t):
(rc o2 o1 = rc_res.Fst_then_snd ∨ rc o2 o1 = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ distinct_ops o1 o2
→
eq (merge init_st (do_ init_st o1) (do_ init_st o2)) (do_ (merge init_st init_st (do_ init_st o2)) o1) := by
dsimp
neem



theorem ind_lca_2op (l: concrete_st) (o1: op_t) (o2: op_t) (ol: op_t) :
(rc o2 o1 = rc_res.Fst_then_snd ∨ rc o2 o1 = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ distinct_ops o1 o2 ∧ distinct_ops o1 ol ∧ distinct_ops o2 ol ∧ eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ l ol)) (do_ (merge (do_ l ol) (do_ l ol) (do_ l ol)) o1) ∧ eq (merge l (do_ l o1) (do_ l o2)) (do_ (merge l l (do_ l o2)) o1)
→
eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ (do_ l ol) o2)) (do_ (merge (do_ l ol) (do_ l ol) (do_ (do_ l ol) o2)) o1) := by
dsimp
neem


theorem inter_right_base_2op  (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) :
(rc o2 o1 = rc_res.Fst_then_snd ∨ rc o2 o1 = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ rc ob o1 = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧ distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o2 ob ∧ distinct_ops o2 ol ∧ distinct_ops ob ol ∧
                    eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1) ∧
                    eq (merge l (do_ a o1) (do_ (do_ b ob) o2)) (do_ (merge l a (do_ (do_ b ob) o2)) o1) ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ol) o2)) o1)
                    →
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b ob) ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b ob) ol) o2)) o1)
                    := by
dsimp
neem
theorem inter_left_base_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) :
 (rc o2 o1) = rc_res.Fst_then_snd ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid o2 != get_rid o1 ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o2 ob ∧ distinct_ops o2 ol ∧ distinct_ops ob ol ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ol) o2)) o1)
                    →
                  eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ (do_ b ol) o2)) o1)
:= by
dsimp
neem



theorem inter_right_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) :
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops o2 ob ∧
                    distinct_ops o2 ol ∧ distinct_ops o2 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b ob) ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b ob) ol) o2)) o1)
                    →
 eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ (do_ b o) ob) ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ (do_ b o) ob) ol) o2)) o1)
:= by
dsimp
neem



theorem inter_left_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) :
 (rc o2 o1) = rc_res.Fst_then_snd ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid o2 != get_rid o1 ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops o2 ob ∧
                    distinct_ops o2 ol ∧ distinct_ops o2 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ (do_ b ol) o2)) o1)
                    →
   eq (merge (do_ l ol) (do_ (do_ (do_ (do_ a o) ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ (do_ a o) ob) ol) (do_ (do_ b ol) o2)) o1)
   := by
dsimp
neem

theorem inter_lca_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ol: op_t) :
((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ol ∧ distinct_ops o2 ol ∧
                    (exists o, (rc o ol) = rc_res.Fst_then_snd) ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1) ∧
                    eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1)
  →
  eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ol) o2)) o1) := by
dsimp
neem

theorem ind_right_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (o2': op_t) :
(rc o2 o1) = rc_res.Fst_then_snd ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 o2' ∧ distinct_ops o2 o2' ∧
                    eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1)
                    →  eq (merge l (do_ a o1) (do_ (do_ b o2') o2)) (do_ (merge l a (do_ (do_ b o2') o2)) o1) := by
dsimp
neem
theorem ind_left_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (o1': op_t) :
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 o1' ∧ distinct_ops o2 o1' ∧
                    eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1)
                    →

 eq (merge l (do_ (do_ a o1') o1) (do_ b o2)) (do_ (merge l (do_ a o1') (do_ b o2)) o1)
 := by

dsimp
neem

theorem base_1op (o1: op_t) :
eq (merge init_st (do_ init_st o1) init_st) (do_ (merge init_st init_st init_st) o1) := by
dsimp
neem
theorem  ind_lca_1op (l: concrete_st) (o1: op_t) (ol: op_t) :
 distinct_ops o1 ol ∧
                    (get_rid o1 != get_rid ol ∨ Prod.fst ol < Prod.fst o1) ∧
                    eq (merge l (do_ l o1) l) (do_ (merge l l l) o1)
  → eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ l ol)) (do_ (merge (do_ l ol) (do_ l ol) (do_ l ol)) o1) := by
dsimp
neem
theorem inter_right_base_1op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t)  :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops ob ol ∧
                    ((rc ob o1) = rc_res.Fst_then_snd → eq (merge l (do_ a o1) (do_ b ob)) (do_ (merge l a (do_ b ob)) o1)) ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1)
                    →
  eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ob) ol)) o1)
  := by
dsimp
blaster (dump-smt-lib:1)


theorem inter_left_base_1op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops ob ol ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1)
                    →
  eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ b ol)) o1)
  := by
dsimp
neem

theorem inter_right_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) (o: op_t) :
rc ob ol =  rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧ (¬(rc o ob = rc_res.Either) ∨ (rc o ol = rc_res.Fst_then_snd)) ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧ get_rid o != get_rid ol ∧ eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ob) ol)) o1)
→
eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b o) ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b o) ob) ol)) o1)
:= by
dsimp
neem
theorem inter_left_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) (o: op_t) :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ b ol)) o1)
                    →
                     eq (merge (do_ l ol) (do_ (do_ (do_ (do_ a o) ob) ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ (do_ (do_ a o) ob) ol) (do_ b ol)) o1)
        := by

dsimp
neem
theorem inter_lca_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ol: op_t) (oi: op_t) :
distinct_ops o1 ol ∧ distinct_ops o1 oi ∧ distinct_ops ol oi ∧
                    (exists o, (rc o ol) = rc_res.Fst_then_snd) ∧
                    (exists o, (rc o oi) = rc_res.Fst_then_snd) ∧
                    eq (merge (do_ l oi) (do_ (do_ a oi) o1) (do_ b oi)) (do_ (merge (do_ l oi) (do_ a oi) (do_ b oi)) o1) ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1)
                    →
                  eq (merge (do_ (do_ l oi) ol) (do_ (do_ (do_ a oi) ol) o1) (do_ (do_ b oi) ol))
                      (do_ (merge (do_ (do_ l oi) ol) (do_ (do_ a oi) ol) (do_ (do_ b oi) ol)) o1)
:= by
dsimp
neem

theorem ind_left_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o1': op_t) (ol: op_t) :
distinct_ops o1 o1' ∧ distinct_ops o1 ol ∧ distinct_ops o1' ol ∧
                    eq (merge (do_ l ol) (do_ a o1) (do_ b ol)) (do_ (merge (do_ l ol) a (do_ b ol)) o1)
→
eq (merge (do_ l ol) (do_ (do_ a o1') o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a o1') (do_ b ol)) o1)
:= by
dsimp
neem

theorem ind_right_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o2: op_t) (o2': op_t) (ol: op_t)  :
distinct_ops o2 o2' ∧ distinct_ops o2 ol ∧ distinct_ops o2' ol ∧
                    eq (merge (do_ l ol) (do_ a ol) (do_ b o2)) (do_ (merge (do_ l ol) (do_ a ol) b) o2)
→
eq (merge (do_ l ol) (do_ a ol) (do_ (do_ b o2') o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b o2')) o2)
:= by
dsimp
neem
theorem  lem_0op (l: concrete_st) (a: concrete_st) (b: concrete_st) (ol: op_t) :
eq (merge (do_ l ol) (do_ a ol) (do_ b ol)) (do_ (merge l a b) ol)
:= by
dsimp
blaster (dump-smt-lib:1)
