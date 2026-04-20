import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Linarith

import Blaster
import CaseStudies.Tactics.Sal

abbrev concrete_st := Int × Bool

@[simp]
def init_st : concrete_st := (0, false)

@[simp]
def eq (a b : concrete_st) := (a = b)

inductive app_op_t : Type where
| Enable
| Disable

abbrev op_t:= ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o : op_t) :=
match o with
| (_, (rid, _)) => rid

@[simp]
def do_ (s : concrete_st) (o : op_t) : concrete_st
:= match o with
| (_, (rid, .Enable)) => (Prod.fst s + 1, true)
| (_, (rid, .Disable)) => (Prod.fst s, false)


inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

@[simp]
def rc (o1 o2 : op_t) :=
match (Prod.snd (Prod.snd o1), Prod.snd (Prod.snd o2)) with
| (.Enable, .Disable) => rc_res.Snd_then_fst
| (.Disable, .Enable) => rc_res.Fst_then_snd
| _ => rc_res.Either

@[simp]
def merge_flag (l a b : concrete_st) :=
  if Prod.snd a && Prod.snd b then true
  else if not (Prod.snd a) && not (Prod.snd b) then false
  else if Prod.snd a then Prod.fst a > Prod.fst l
  else Prod.fst b > Prod.fst l

@[simp]
def merge (l a b : concrete_st) : concrete_st
:= (Prod.fst a + Prod.fst b - Prod.fst l , merge_flag l a b)

@[simp]
def commutes_with (o1 o2 : op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)

syntax tactic " and_then " tactic : tactic

macro_rules
| `(tactic| $a:tactic and_then $b:tactic) =>
    `(tactic| $a:tactic; $b:tactic)

macro "neem_solve" : tactic =>
    `(tactic |
    dsimp and_then
    solve
      | all_goals try aesop and_then all_goals try first
        | (ext ; grind)
      | all_goals try first
        | (ext; grind)
        | blaster
)

theorem no_rc_chain (o1 : op_t) (o2 : op_t) (o3 : op_t) :
(distinct_ops o1 o2 ∧ distinct_ops o2 o3)
→ (¬(rc o1 o2 = rc_res.Fst_then_snd ∧ rc o2 o3 = rc_res.Fst_then_snd))
:= by
    neem_solve

theorem lem_0op (l : concrete_st) (a : concrete_st) (b : concrete_st) (ol : op_t):
eq (merge (do_ l ol) (do_ a ol) (do_ b ol)) (do_ (merge l a b) ol) := by sal
grind

theorem ind_left_2op (l : concrete_st) (a : concrete_st) (b : concrete_st)
(o1 : op_t) (o2 : op_t) (o1' : op_t):
(((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 o1' ∧ distinct_ops o2 o1' ∧
                    eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1))
→
(eq (merge l (do_ (do_ a o1') o1) (do_ b o2)) (do_ (merge l (do_ a o1') (do_ b o2)) o1))
:= by sal

#print lem_0op
