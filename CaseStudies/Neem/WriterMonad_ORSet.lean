import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import ProofWidgets


import Std.Tactic.BVDecide
import CaseStudies.Neem_interfaces.Set_extended
import Std

import CaseStudies.Neem.WriterMonad_Set


open Classical Std


abbrev concrete_st := set (ℕ × ℕ)

@[simp]
def init_st: concrete_st := empty

@[simp]
def mem_id_s (id:ℕ) (s: concrete_st) : Prop :=
exists e, mem e s ∧ Prod.fst e = id

@[simp]
def mem_ele_s (ele: ℕ) (s: concrete_st) : Prop :=
exists e, mem e s ∧ Prod.snd e = ele


@[simp]
def eq (a: concrete_st) (b: concrete_st) := a = b

inductive app_op_t : Type where
| Add: ℕ → app_op_t
| Rem: ℕ → app_op_t

abbrev op_t:= ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2: op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o: op_t) :=
match o with
| (_, (rid, _)) => rid

@[simp]
def get_ele (o: op_t) : ℕ :=
  match (Prod.snd (Prod.snd o)) with
  | app_op_t.Add e => e
  | app_op_t.Rem e => e

@[simp]
def do_ (s: concrete_st) (o: op_t) : concrete_st :=
match o with
| (ts, (rid, app_op_t.Add e)) => add (ts,e) s
| (_, (rid, app_op_t.Rem e)) => filter s (fun ele => Prod.snd ele != e)


inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

@[simp, grind]
def rc (o1: op_t) (o2: op_t) :=
match (Prod.snd (Prod.snd o1)), (Prod.snd (Prod.snd o2)) with
| app_op_t.Add e1, app_op_t.Rem e2 => if e1 = e2 then rc_res.Snd_then_fst else rc_res.Either
| app_op_t.Rem e1, app_op_t.Add e2 => if e1 = e2 then rc_res.Fst_then_snd else rc_res.Either
| _,_ => rc_res.Either


@[simp, grind]
def merge (l: concrete_st) (a: concrete_st) (b: concrete_st) : concrete_st :=
  let da := difference a l
  let db := difference b l
  let i_ab := intersection a b
  let i_lab := intersection l i_ab
  union i_lab (union da db)

def univ_add (o : op_t) :=
match o with
| (ts, (rid, .Add x)) => (ts,x)
| (ts, (rid, .Rem x)) => (ts,x)


def op_string (o : op_t) :=
match o with
| (ts, (rid, .Add x)) => s! "Added {toString (x)} at timestamp {ts}"
| (ts, (rid, .Rem x)) => s! "Removed {toString (x)} at timestamp {ts}"




#eval do_viz (do_) (ok (init_st_viz init_st)) (1,1,app_op_t.Rem 3) univ_add op_string

def ans := do_viz do_ (do_viz (do_) (ok (init_st_viz init_st)) (1,1,app_op_t.Rem 3) univ_add op_string) (4,5,app_op_t.Add 3) univ_add op_string

#eval ans

def merge_ans := merge_viz merge (ok (init_st_viz init_st))
( do_viz (do_) (ok (init_st_viz init_st)) (1,1,app_op_t.Rem 3) univ_add op_string)
(do_viz (do_) (ok (init_st_viz init_st)) (1,2,app_op_t.Add 3) univ_add op_string)

#eval merge_ans

#html  renderBranchingTreeFromList merge_ans.log
