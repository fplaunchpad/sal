import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import ProofWidgets


import Std.Tactic.BVDecide
import CaseStudies.Interfaces.Set_Extended
import Std

import CaseStudies.Fstar_like_implementations.Counterexample_Visualization.WriterMonad_Set


open Classical Std


abbrev concrete_st := set ℕ

@[simp]
def init_st: concrete_st := empty


@[simp]
def eq (a: concrete_st) (b: concrete_st) := a = b

abbrev app_op_t := ℕ

abbrev op_t:= ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2: op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o: op_t) :=
match o with
| (_, (rid, _)) => rid



@[simp]
def do_ (s: concrete_st) (o: op_t) : concrete_st :=
add (Prod.snd (Prod.snd o)) s


inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

@[simp, grind]
def rc (o1: op_t) (o2: op_t) := rc_res.Either


@[simp, grind]
def merge (l: concrete_st) (a: concrete_st) (b: concrete_st) : concrete_st :=
union l (union a b)

def univ_add (o : op_t) := Prod.snd (Prod.snd o)

def op_string (o : op_t) := s! "Added {toString (Prod.snd (Prod.snd o))}"


#eval do_viz (do_) (ok (init_st_viz init_st)) (1,1,3) univ_add op_string

def ans := do_viz do_ (do_viz (do_) (ok (init_st_viz init_st)) (1,1,3) univ_add op_string) (4,5,6) univ_add op_string

#eval ans

def merge_ans := merge_viz merge (ok (init_st_viz init_st))
( do_viz (do_) (ok (init_st_viz init_st)) (1,1,7) univ_add op_string)
(do_viz (do_) (ok (init_st_viz init_st)) (1,2,8) univ_add op_string)

#eval merge_ans

#html  renderBranchingTreeFromList merge_ans.log
