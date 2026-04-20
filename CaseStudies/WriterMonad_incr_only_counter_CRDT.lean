import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Std.Tactic.BVDecide

import CaseStudies.Interfaces.Map_extended

import Blaster


@[simp] abbrev concrete_st := map ℕ Int
/- keys: replicas IDs, values: int -/

@[simp]
def mysel (s: concrete_st) (k: ℕ) : Int :=
if (contains s k) then (sel s k) else 0

@[simp]
def init_st : concrete_st := const_on empty 0

@[simp]
def eq (a b: concrete_st) := (forall id:ℕ, (contains a id = contains b id) ∧ (mysel a id = mysel b id))

inductive app_op_t : Type where
| Incr

abbrev op_t:= ℕ × ℕ × app_op_t

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

def andThen {α β γ} (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}

def ok {β} (x : β) : WithLog (concrete_st × String × concrete_st) β := {log := [], val := x}

def save {α} (data : α) : WithLog α Unit :=
  {log := [data], val := ()}

infixl:55 " ~~> " => andThen


structure map_with_universe

@[simp]
def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o : op_t) :=
match o with
| (_, (rid, _)) => rid

@[simp]
def do_ (s: concrete_st) (o: op_t) : concrete_st :=
match o with
| (_, (r, _)) => upd s r (mysel s r + 1)

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
def merge (a b: concrete_st) : concrete_st :=
let keys := union (domain a) (domain b)
let u := const_on keys 0
iter_upd (fun k v => max (mysel a k) (mysel b k)) u
