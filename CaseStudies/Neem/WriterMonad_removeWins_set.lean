import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import ProofWidgets

import Std.Tactic.BVDecide
import CaseStudies.Neem_interfaces.Set_extended
import Std

import CaseStudies.Neem.WriterMonad_Set


open Classical Std ProofWidgets Jsx

@[simp] abbrev concrete_st := set (ℕ × ℕ)

@[simp]
def init_st : concrete_st:= filter (fun (ts, _) => if ts = 0 then true else false) (complement empty)

@[simp]
def eq (a b: concrete_st) :=
forall e, mem e a ↔ mem e b


inductive app_op_t : Type where
| Add : ℕ → app_op_t
| Rem : ℕ → app_op_t

abbrev op_t:= ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2 : op_t) := (Prod.fst op1 != Prod.fst op2 ∧ Prod.fst op1 != 0 ∧ Prod.fst op2 !=0)
--the initial state already has ts 0, so further ops should have ts > 0

@[simp]
def get_rid (o : op_t) :=
match o with
| (_, (rid, _)) => rid

@[simp]
def do_ (s: concrete_st) (o: op_t) : concrete_st :=
match o with
| (_, (rid, .Add x)) => filter s (fun e => Prod.snd e != x)
| (ts, (rid, .Rem x)) => add (ts,x) s



inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

@[simp]
def rc (o1 o2 : op_t) := match Prod.snd (Prod.snd o1), Prod.snd (Prod.snd o2) with
| .Add x1, .Rem x2 => if x1 = x2 then rc_res.Fst_then_snd else rc_res.Either
| .Rem x1, .Add x2 => if x1 = x2 then rc_res.Snd_then_fst else rc_res.Either
| _, _ => rc_res.Either

def merge (l a b: concrete_st) : concrete_st :=
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
