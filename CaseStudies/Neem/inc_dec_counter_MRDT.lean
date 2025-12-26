import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Linarith

import CaseStudies.Velvet.Std

import Blaster

open Lean.Elab.Term.DoNames

abbrev concrete_st := Int

@[simp]
def init_st: concrete_st := 0

@[simp]
def eq (a b: concrete_st) := (a = b)

inductive app_op_t : Type where
| Inc
| Dec

abbrev op_t:= ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2: op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o: op_t) :=
match o with
| (_, (rid, _)) => rid

@[simp]
def do_ (s:concrete_st) (o: op_t) : concrete_st
:= match Prod.snd (Prod.snd o) with
| app_op_t.Inc => s+1
| app_op_t.Dec => s-1

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

@[simp]
def rc (o1 o2: op_t) := rc_res.Either

@[simp]
def merge (l a b: concrete_st) : concrete_st
:= a + b - l

@[simp]
def commutes_with (o1 o2: op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)

method rc_non_comm (o1: op_t) (o2: op_t) return (u: Unit)
require distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2
ensures (rc o1 o2 = rc_res.Either ↔ commutes_with o1 o2)
do
    return ()


prove_correct rc_non_comm by
    dsimp [rc_non_comm]
    loom_solve

method no_rc_chain (o1: op_t) (o2: op_t) (o3: op_t) return (u: Unit)
require distinct_ops o1 o2 ∧ distinct_ops o2 o3
ensures ¬(rc o1 o2 = rc_res.Fst_then_snd ∧ rc o2 o3 = rc_res.Fst_then_snd)
do
    return ()

prove_correct no_rc_chain by
    dsimp [no_rc_chain]
    loom_solve


method cond_comm_base (s: concrete_st) (o1: op_t) (o2: op_t) (o3: op_t) return (u: Unit)
require (distinct_ops o1 o2 ∧ distinct_ops o2 o3 ∧ distinct_ops o1 o3
    ∧ rc o1 o2 = rc_res.Fst_then_snd ∧ ¬(rc o2 o3 = rc_res.Either))
ensures eq (do_ (do_ (do_ s o1) o2) o3) (do_ (do_ (do_ s o2) o1) o3)
do
    return ()

prove_correct cond_comm_base by
    dsimp [cond_comm_base]
    loom_solve

-- method cond_comm_ind (s:concrete_st) (o1:op_t) (o2:op_t) (o3:op_t) (o:op_t) (l:seq op_t) return (u: Unit)
-- require


/- do_ cond_comm_ind after figuring log out -/

method merge_comm (l: concrete_st) (a: concrete_st) (b: concrete_st) return (u: Unit)
ensures eq (merge l a b) (merge l b a)
do
    return ()

prove_correct merge_comm by
    dsimp [merge_comm]
    loom_solve


method merge_idem (s: concrete_st)return (u: Unit)
ensures eq (merge s s s) s
do
    return ()

prove_correct merge_idem by
    dsimp[merge_idem]
    loom_solve


method base_2op (o1: op_t) (o2: op_t) return (u: Unit)
require (rc o2 o1 = rc_res.Fst_then_snd ∨ rc o2 o1 = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ distinct_ops o1 o2
ensures eq (merge init_st (do_ init_st o1) (do_ init_st o2)) (do_ (merge init_st init_st (do_ init_st o2)) o1)
do
    return ()

prove_correct base_2op by
    dsimp [base_2op]
    loom_solve

method ind_lca_2op (l: concrete_st) (o1: op_t) (o2: op_t) (ol: op_t) return (u: Unit)
require (rc o2 o1 = rc_res.Fst_then_snd ∨ rc o2 o1 = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ distinct_ops o1 o2 ∧ distinct_ops o1 ol ∧ distinct_ops o2 ol ∧ eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ l ol)) (do_ (merge (do_ l ol) (do_ l ol) (do_ l ol)) o1) ∧ eq (merge l (do_ l o1) (do_ l o2)) (do_ (merge l l (do_ l o2)) o1)
ensures eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ (do_ l ol) o2)) (do_ (merge (do_ l ol) (do_ l ol) (do_ (do_ l ol) o2)) o1)
do
    return ()


prove_correct ind_lca_2op by
    dsimp [ind_lca_2op]
    loom_solve


method inter_right_base_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) return (u: Unit)
require (rc o2 o1 = rc_res.Fst_then_snd ∨ rc o2 o1 = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ rc ob o1 = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧ distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o2 ob ∧ distinct_ops o2 ol ∧ distinct_ops ob ol ∧
                    eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1) ∧
                    eq (merge l (do_ a o1) (do_ (do_ b ob) o2)) (do_ (merge l a (do_ (do_ b ob) o2)) o1) ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ol) o2)) o1)
ensures eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b ob) ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b ob) ol) o2)) o1)
do
    return ()

prove_correct inter_right_base_2op by
    dsimp [inter_right_base_2op]
    loom_solve

method inter_left_base_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) return (u: Unit)
require (rc o2 o1) = rc_res.Fst_then_snd ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid o2 != get_rid o1 ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o2 ob ∧ distinct_ops o2 ol ∧ distinct_ops ob ol ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ol) o2)) o1)
ensures eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ (do_ b ol) o2)) o1)
do
    return ()

prove_correct inter_left_base_2op by
    dsimp [inter_left_base_2op]
    loom_solve


method inter_right_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) return (u: Unit)
require ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops o2 ob ∧
                    distinct_ops o2 ol ∧ distinct_ops o2 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b ob) ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b ob) ol) o2)) o1)
ensures eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ (do_ b o) ob) ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ (do_ b o) ob) ol) o2)) o1)
do
    return ()

prove_correct inter_right_2op by
    dsimp[inter_right_2op]
    loom_solve


method inter_left_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) return (u: Unit)
require (rc o2 o1) = rc_res.Fst_then_snd ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid o2 != get_rid o1 ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops o2 ob ∧
                    distinct_ops o2 ol ∧ distinct_ops o2 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ (do_ b ol) o2)) o1)
ensures  eq (merge (do_ l ol) (do_ (do_ (do_ (do_ a o) ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ (do_ a o) ob) ol) (do_ (do_ b ol) o2)) o1)
do
    return ()

prove_correct inter_left_2op by
    dsimp [inter_left_2op]
    loom_solve

method inter_lca_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ol: op_t) return (u: Unit)
require ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ol ∧ distinct_ops o2 ol ∧
                    (exists o, (rc o ol) = rc_res.Fst_then_snd) ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1) ∧
                    eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1)
ensures   eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ol) o2)) o1)
do
    return ()

prove_correct inter_lca_2op by
    dsimp [inter_lca_2op]
    loom_solve

method ind_right_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (o2': op_t) return (u: Unit)
require (rc o2 o1) = rc_res.Fst_then_snd ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 o2' ∧ distinct_ops o2 o2' ∧
                    eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1)
ensures eq (merge l (do_ a o1) (do_ (do_ b o2') o2)) (do_ (merge l a (do_ (do_ b o2') o2)) o1)
do
    return ()

prove_correct ind_right_2op by
    dsimp [ind_right_2op]
    loom_solve


method ind_left_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (o1': op_t) return (u: Unit)
require  ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 o1' ∧ distinct_ops o2 o1' ∧
                    eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1)

ensures  eq (merge l (do_ (do_ a o1') o1) (do_ b o2)) (do_ (merge l (do_ a o1') (do_ b o2)) o1)
do
    return ()

prove_correct ind_left_2op by
    dsimp [ind_left_2op]
    loom_solve


method base_1op (o1: op_t) return (u: Unit)
ensures eq (merge init_st (do_ init_st o1) init_st) (do_ (merge init_st init_st init_st) o1)
do
    return ()

prove_correct base_1op by
    dsimp [base_1op]
    loom_solve

method ind_lca_1op (l: concrete_st) (o1: op_t) (ol: op_t) return (u: Unit)
require  distinct_ops o1 ol ∧
                    (get_rid o1 != get_rid ol ∨ Prod.fst ol < Prod.fst o1) ∧
                    eq (merge l (do_ l o1) l) (do_ (merge l l l) o1)
ensures  eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ l ol)) (do_ (merge (do_ l ol) (do_ l ol) (do_ l ol)) o1)
do
    return ()

prove_correct ind_lca_1op by
    dsimp [ind_lca_1op]
    loom_solve



method inter_right_base_1op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) return (u: Unit)
require (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops ob ol ∧
                    ((rc ob o1) = rc_res.Fst_then_snd → eq (merge l (do_ a o1) (do_ b ob)) (do_ (merge l a (do_ b ob)) o1)) ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1)
ensures  eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ob) ol)) o1)
do
    return ()


prove_correct inter_right_base_1op by
    dsimp [inter_right_base_1op]
    loom_solve


method inter_left_base_1op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) return (u: Unit)
require (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops ob ol ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1)
ensures  eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ b ol)) o1)
do
    return ()

prove_correct inter_left_base_1op by
    dsimp [inter_left_base_1op]
    loom_solve


method inter_right_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) (o: op_t) return (u: Unit)
require rc ob ol =  rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧ (¬(rc o ob = rc_res.Either) ∨ (rc o ol = rc_res.Fst_then_snd)) ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧ get_rid o != get_rid ol ∧ eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ob) ol)) o1)
ensures eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b o) ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b o) ob) ol)) o1)
do
    return ()


prove_correct inter_right_1op by
    dsimp [inter_right_1op]
    loom_solve


method inter_left_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) (o: op_t) return (u: Unit)
require (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ b ol)) o1)
ensures  eq (merge (do_ l ol) (do_ (do_ (do_ (do_ a o) ob) ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ (do_ (do_ a o) ob) ol) (do_ b ol)) o1)
do
    return ()

prove_correct inter_left_1op by
    dsimp [inter_left_1op]
    loom_solve

method inter_lca_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ol: op_t) (oi: op_t) return (u: Unit)
require  distinct_ops o1 ol ∧ distinct_ops o1 oi ∧ distinct_ops ol oi ∧
                    (exists o, (rc o ol) = rc_res.Fst_then_snd) ∧
                    (exists o, (rc o oi) = rc_res.Fst_then_snd) ∧
                    eq (merge (do_ l oi) (do_ (do_ a oi) o1) (do_ b oi)) (do_ (merge (do_ l oi) (do_ a oi) (do_ b oi)) o1) ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1)
ensures  eq (merge (do_ (do_ l oi) ol) (do_ (do_ (do_ a oi) ol) o1) (do_ (do_ b oi) ol))
                      (do_ (merge (do_ (do_ l oi) ol) (do_ (do_ a oi) ol) (do_ (do_ b oi) ol)) o1)
do
    return ()

prove_correct inter_lca_1op by
    dsimp [inter_lca_1op]
    loom_solve


method ind_left_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o1': op_t) (ol: op_t) return (u: Unit)
require  distinct_ops o1 o1' ∧ distinct_ops o1 ol ∧ distinct_ops o1' ol ∧
                    eq (merge (do_ l ol) (do_ a o1) (do_ b ol)) (do_ (merge (do_ l ol) a (do_ b ol)) o1)
ensures  eq (merge (do_ l ol) (do_ (do_ a o1') o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a o1') (do_ b ol)) o1)
do
    return ()

prove_correct ind_left_1op by
    dsimp [ind_left_1op]
    loom_solve

method ind_right_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o2: op_t) (o2': op_t) (ol: op_t)  return (u: Unit)
require distinct_ops o2 o2' ∧ distinct_ops o2 ol ∧ distinct_ops o2' ol ∧
                    eq (merge (do_ l ol) (do_ a ol) (do_ b o2)) (do_ (merge (do_ l ol) (do_ a ol) b) o2)
ensures  eq (merge (do_ l ol) (do_ a ol) (do_ (do_ b o2') o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b o2')) o2)
do
    return ()

prove_correct ind_right_1op by
    dsimp [ind_right_1op]
    loom_solve

method lem_0op (l: concrete_st) (a: concrete_st) (b: concrete_st) (ol: op_t) return (u: Unit)
ensures  eq (merge (do_ l ol) (do_ a ol) (do_ b ol)) (do_ (merge l a b) ol)
do
    return ()

prove_correct lem_0op by
    dsimp [lem_0op]
    loom_solve
