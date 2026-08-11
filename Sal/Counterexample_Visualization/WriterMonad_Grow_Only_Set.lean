import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import ProofWidgets


import Std.Tactic.BVDecide
import Sal.Interfaces.Set_Extended
import Std

import Sal.Counterexample_Visualization.WriterMonad_Set


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


/-! ## The same execution as a `Trace`, then extended past one merge

The writer monad above records the execution as a flat log, which `#eval` prints.
Drawing it needs the branching structure kept rather than recovered, which is what
a `Trace` does — and unlike the flat log, traces compose: `round2` below merges two
branches that each descend from the *result* of `round1`.

Grow-only is the degenerate case — every merge is a union and every branch
survives — so this is the shape without the drama. The add-wins set is where a
multi-merge execution actually says something: see
`Sal/Counterexample_Visualization/WriterMonad_Add_Wins_Set.lean`. -/

def tInit : Trace (concrete_st_viz ℕ) := .leaf (init_st_viz init_st)

/-- Replica 1 adds 7, replica 2 adds 8, and they merge: `#[7,8]#`. -/
def round1 : Trace (concrete_st_viz ℕ) :=
  merge_trace merge tInit
    (do_trace do_ tInit (1,1,7) univ_add op_string)
    (do_trace do_ tInit (2,2,8) univ_add op_string)

/-- Both replicas carry on from the merged version and merge again: `#[7,8,9,10]#`.
The branches are `reroot`ed so `round1`'s result is drawn once, at the apex. -/
def round2 : Trace (concrete_st_viz ℕ) :=
  merge_trace merge round1
    (do_trace do_ round1.reroot (3,1,9) univ_add op_string)
    (do_trace do_ round1.reroot (4,2,10) univ_add op_string)

#eval round1.result
#eval round2.result

#html renderTrace round1
#html renderTrace round2
