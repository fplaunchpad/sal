import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Std.Tactic.BVDecide
import Blaster

import CaseStudies.Neem_interfaces.Map_extended


@[simp] abbrev concrete_st := map ℕ (set ℕ)



@[simp]
def init_st : concrete_st:= const_on (add 0 empty) (complement empty)

@[simp]
def eq (a b: concrete_st) :=
a = b


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
| (_, (rid, .Add x)) => filter s (fun e => Prod.snd e != 1)
| (ts, (rid, .Rem x)) => add (ts,1) s



inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

@[simp]
def rc (o1 o2 : op_t) := match Prod.snd (Prod.snd o1), Prod.snd (Prod.snd o2) with
| .Add1, .Rem1 | .Add2, .Rem2 => rc_res.Fst_then_snd
| .Rem1, .Add1 | .Rem2, .Add2 => rc_res.Snd_then_fst
| _, _ => rc_res.Either

@[simp]
def commutes_with (o1 o2 : op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)

@[simp]
def merge (l a b: concrete_st) : concrete_st :=
  let da := difference a l
  let db := difference b l
  let i_ab := intersection a b
  let i_lab := intersection l i_ab
  union i_lab (union da db)
