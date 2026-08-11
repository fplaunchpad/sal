import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import ProofWidgets

import Std.Tactic.BVDecide
import Sal.Interfaces.Set_Extended
import Std

import Sal.Counterexample_Visualization.WriterMonad_Set


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


/-! ## The remove-wins race as a `Trace`, run twice

The mirror image of the OR-set, and the representation is inverted with it: the
state holds *removal markers* `(ts, elem)`, `Rem x` stakes a marker, and `Add x`
retracts every marker for `x`. Element 3 is present exactly when **no** marker for
it is in the set, so the displayed set reads as "what is gone", not "what is here".

That inversion is what makes the race come out the other way. An `Add` can only
retract the markers it has seen, so a marker staked concurrently survives the
merge and keeps the element absent: remove wins. The diagrams below run it twice,
the second round from the first's result.

`init_st` holds a marker `(0, x)` for *every* `x`, so it is infinite — it prints
as `#[]#` only because the display universe starts empty and grows as ops touch
elements. Every node before the first op is under-reported for that reason. -/

def tInit : Trace (concrete_st_viz (ℕ × ℕ)) := .leaf (init_st_viz init_st)

/-- The LCA of the first race: `Add 3` retracts the initial `(0,3)` marker, so
element 3 is present and no marker for it remains. -/
def seeded : Trace (concrete_st_viz (ℕ × ℕ)) :=
  do_trace do_ tInit (1,0,app_op_t.Add 3) univ_add op_string

/-- **Round 1.** Left stakes a removal marker `(2,3)`; right adds 3, retracting
only the markers it has seen — of which there are none for 3. The merge keeps
`(2,3)`: `#[(2, 3)]#`, so element 3 is **absent**. Remove wins. -/
def round1 : Trace (concrete_st_viz (ℕ × ℕ)) :=
  merge_trace merge seeded
    (do_trace do_ seeded.reroot (2,1,app_op_t.Rem 3) univ_add op_string)
    (do_trace do_ seeded.reroot (3,2,app_op_t.Add 3) univ_add op_string)

/-- **Round 2.** Again from round 1's result, sides swapped: left adds 3,
retracting `(2,3)`; right stakes a fresh marker `(5,3)`. The merge keeps `(5,3)`:
`#[(5, 3)]#`, element 3 absent again. The concurrent `Add` loses from either side. -/
def round2 : Trace (concrete_st_viz (ℕ × ℕ)) :=
  merge_trace merge round1
    (do_trace do_ round1.reroot (4,1,app_op_t.Add 3) univ_add op_string)
    (do_trace do_ round1.reroot (5,2,app_op_t.Rem 3) univ_add op_string)

-- Expect `#[(2, 3)]#` then `#[(5, 3)]#` — a marker survives both rounds, under a
-- fresh tag the second time. Contrast the OR-set file, where the same race shape
-- leaves the element present.
#eval round1.result
#eval round2.result

#html renderTrace round1
#html renderTrace round2
