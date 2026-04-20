import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Std.Tactic.BVDecide
import Std.Data.ExtTreeMap.Basic

import CaseStudies.Interfaces.Map_extended
import CaseStudies.Tactics.Sal

import Blaster


@[simp] abbrev concrete_st := Std.ExtTreeMap ℕ (set ℕ)
/- keys: replicas IDs, values: int -/

@[simp]
def mysel (s: concrete_st) (k: ℕ) : (set ℕ) :=
match (Std.ExtTreeMap.get? s k ) with
| some val => val
| none => empty

@[simp]
def init_st : concrete_st := Std.ExtTreeMap.empty

@[simp]
def eq (a b: concrete_st) := a = b

abbrev app_op_t := ℕ × ℕ

abbrev op_t:= ℕ × ℕ × app_op_t

@[simp]
def key (op:op_t) := Prod.fst (Prod.snd op)

@[simp]
def value (op:op_t) := Prod.snd (Prod.snd op)

@[simp]
def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o : op_t) :=
match o with
| (_, (rid, _)) => rid

@[simp]
def do_ (s: concrete_st) (o: op_t) : concrete_st :=
match o with
| (ts, (_, (k,v))) => Std.ExtTreeMap.insert  s k (add v (mysel s k))


inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

@[simp]
def rc (o1 o2 : op_t) := rc_res.Either

@[simp]
def commutes_with (o1 o2 : op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)

@[simp]
def merge (l a b: concrete_st) : concrete_st :=
let la_merge := Std.ExtTreeMap.mergeWith (fun k s1 s2 => union s1 s2) l a
let lab_merge := Std.ExtTreeMap.mergeWith (fun k s1 s2 => union s1 s2) la_merge b
lab_merge
