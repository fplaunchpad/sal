import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Linarith

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

import Plausible

import Blaster

open Lean.Elab.Term.DoNames

abbrev concrete_st := Int

@[simp]
def init_st: concrete_st := 0

@[simp]
def eq (a b: concrete_st) := (a = b)

inductive app_op_t : Type where
| Incr

abbrev op_t:= ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2: op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o: op_t) :=
match o with
| (_, (rid, _)) => rid


structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

def andThen (result : WithLog α β) (next : β → WithLog α γ)
: WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}

def ok (x : β) : WithLog (concrete_st × String × concrete_st) β := {log := [], val := x}

def save (data : α) : WithLog α Unit :=
  {log := [data], val := ()}

infixl:55 " ~~> " => andThen

def do_ (ls:  WithLog (concrete_st × String × concrete_st) concrete_st) (o: op_t)
: WithLog (concrete_st × String × concrete_st) concrete_st
:=
let s := ls.val
{log := ls.log, val:=()} ~~> fun () =>save (s,"Incr", s+1) ~~> fun () => ok (s+1)

def ans := do_ (do_ (ok init_st) (1,1,app_op_t.Incr)) (1,1,app_op_t.Incr)
#eval ans


inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

@[simp]
def rc (o1 o2: op_t) := rc_res.Either


def merge (l a b: WithLog (concrete_st × String × concrete_st) concrete_st) :
WithLog (concrete_st × String × concrete_st) concrete_st
:=
let lval := l.val
let aval := a.val
let bval := b.val
let result := aval + bval - lval
{log := l.log ++ [(lval, "MergeL", result)] ++
 a.log ++ [(aval, "MergeA", result)] ++
 b.log ++ [(bval, "MergeB", result)]
 val := ()} ~~> fun () => ok (result)

/- Sample Evaluation-/

#eval merge (ok (init_st)) (do_ (ok (init_st)) (1,1,app_op_t.Incr))
(do_ (ok (init_st)) (1,1,app_op_t.Incr))

/- evaluate LHS of failing VC -/

#eval merge (ok (4)) (ok (4)) (ok (4))

/- evaluate RHS of failing VC -/
#eval ok (4)
