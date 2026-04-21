import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Linarith
import Std


set_option linter.style.commandStart false

def mycmp (a: ℕ × ℕ) (b: ℕ × ℕ) :=
let af := Prod.fst a
let bf := Prod.fst b
let as := Prod.snd a
let bs := Prod.snd b
if af < bf then Ordering.lt
else if af = bf then if as < bs then Ordering.lt else if as > bs then Ordering.gt else Ordering.eq
else Ordering.gt


abbrev concrete_st := Std.ExtTreeSet (ℕ × ℕ) mycmp


@[simp]
def init_st: concrete_st := {}

@[simp]
def mem_id_s (id:pos) (s: concrete_st) : Prop :=
exists e, Std.ExtTreeSet.contains s e ∧ Prod.fst e = id

@[simp]
def mem_ele_s (ele: ℕ) (s: concrete_st) : Prop :=
exists e, e ∈ s ∧ Prod.snd e = ele

@[simp]
def eq (a: concrete_st) (b: concrete_st) := a=b

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
| (ts, (rid, app_op_t.Add e)) => {(ts,e)} ∪ s
| (_, (rid, app_op_t.Rem e)) => {x | x ∈ s ∧ Prod.snd x != e}


inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

@[simp]
def rc (o1: op_t) (o2: op_t) :=
match (Prod.snd (Prod.snd o1)), (Prod.snd (Prod.snd o2)) with
| app_op_t.Add e1, app_op_t.Rem e2 => if e1 = e2 then rc_res.Snd_then_fst else rc_res.Either
| app_op_t.Rem e1, app_op_t.Add e2 => if e1 = e2 then rc_res.Fst_then_snd else rc_res.Either
| _,_ => rc_res.Either


@[simp]
def merge (l: concrete_st) (a: concrete_st) (b: concrete_st) : concrete_st :=
  (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

@[simp]
def commutes_with (o1 o2: op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)
