import Lean
import ProofWidgets
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Linarith



import Plausible

import Sal.Counterexample_Visualization.Trace




abbrev concrete_st := Int × Bool

@[simp]
def init_st: concrete_st := (0, false)

@[simp]
def eq (a b: concrete_st) := (a = b)

inductive app_op_t : Type where
| Enable
| Disable

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

def andThen {α β γ} (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}

def ok {β} (x : β) : WithLog (concrete_st × String × concrete_st) β := {log := [], val := x}

def save {α} (data : α) : WithLog α Unit :=
  {log := [data], val := ()}

infixl:55 " ~~> " => andThen




def do_ (ls:  WithLog (concrete_st × String × concrete_st) concrete_st) (o: op_t)
: WithLog (concrete_st × String × concrete_st) concrete_st
:=
let s := ls.val
{log := ls.log, val := ()} ~~> fun () =>
 (match o with
| (ts, (rid, .Enable)) => save (s, s!"({ts},r{rid},enable)", (Prod.fst s + 1, true)) ~~> fun () => ok ((Prod.fst s + 1, true))
| (ts, (rid, .Disable)) => save (s, s!"({ts},r{rid},disable)", (Prod.fst s, false)) ~~> fun () => ok ((Prod.fst s, false))
 )

def ans := do_ (do_ (ok init_st) (1,2,app_op_t.Enable)) (1,1,app_op_t.Disable)
#eval ans





@[simp]
def merge_flag (l a b: concrete_st) :=
  if Prod.snd a && Prod.snd b then true
  else if not (Prod.snd a) && not (Prod.snd b) then false
  else if Prod.snd a then Prod.fst a > Prod.fst l
  else Prod.fst b > Prod.fst l


def merge (l a b: WithLog (concrete_st × String × concrete_st) concrete_st) :
WithLog (concrete_st × String × concrete_st) concrete_st
:=
let lval := l.val
let aval := a.val
let bval := b.val
let result := ((Prod.fst aval + Prod.fst bval - Prod.fst lval , merge_flag lval aval bval))
{log := l.log ++ [(lval, "LMerge", result)] ++
 a.log ++ [(aval, "AMerge", result)] ++
 b.log ++ [(bval, "BMerge", result)]
 val := ()} ~~> fun () => ok (result)


#eval merge (ok (init_st)) (do_ (ok (init_st)) (1,1,app_op_t.Enable)) (do_ (ok (init_st)) (1,1,app_op_t.Enable))


/-! ## The same `do_` and `merge`, without the logging

`Sal/Counterexample_Visualization/Trace.lean` builds diagrams from a *pure* state
transition and a labelling function, so the writer-monad plumbing above is split
back apart here: `do_pure` and `merge_pure` are the state halves of `do_` and
`merge`, and `op_string` is the label half of `do_`. They are transcriptions, not
a second implementation — compare them line by line with the two definitions
above, and see the `#eval`s in each namespace below, which check that a trace and
its `WithLog` counterpart land on the same state. -/

@[simp]
def do_pure (s : concrete_st) (o : op_t) : concrete_st :=
match o with
| (_, (_, .Enable)) => (Prod.fst s + 1, true)
| (_, (_, .Disable)) => (Prod.fst s, false)

def op_string (o : op_t) : String :=
match o with
| (ts, (rid, .Enable)) => s!"({ts},r{rid},enable)"
| (ts, (rid, .Disable)) => s!"({ts},r{rid},disable)"

@[simp]
def merge_pure (l a b : concrete_st) : concrete_st :=
  (Prod.fst a + Prod.fst b - Prod.fst l, merge_flag l a b)


/-! ## The failing VC, `inter_right_1op`, as two traces

    lhs = merge (do l ol) (do (do a ol) o1) (do (do (do b o) ob) ol)
    rhs = do (merge (do l ol) (do a ol) (do (do (do b o) ob) ol)) o1

The bug is that these two disagree. Each namespace below instantiates them at a
counterexample and draws both, so the divergence can be read off the diagrams.

`l`, `a` and `b` are three independent starting states, not one shared root, so
each is a `ref` — it gets its own captioned node at the top of its own path.
(The flat renderer assumed a shared prefix and dropped `l`'s length off each
branch, which silently ate the first edge of the longer `b` path.) -/

def vc_lhs (l a b : concrete_st) (ol o1 o ob : op_t) : Trace concrete_st :=
  mergeWith merge_pure
    (stepWith do_pure op_string (.ref "l" l) ol)
    (stepWith do_pure op_string (stepWith do_pure op_string (.ref "a" a) ol) o1)
    (stepWith do_pure op_string
      (stepWith do_pure op_string (stepWith do_pure op_string (.ref "b" b) o) ob) ol)

def vc_rhs (l a b : concrete_st) (ol o1 o ob : op_t) : Trace concrete_st :=
  stepWith do_pure op_string
    (mergeWith merge_pure
      (stepWith do_pure op_string (.ref "l" l) ol)
      (stepWith do_pure op_string (.ref "a" a) ol)
      (stepWith do_pure op_string
        (stepWith do_pure op_string (stepWith do_pure op_string (.ref "b" b) o) ob) ol))
    o1


namespace counter1
/- Plausible Generation -/
/- encode the counterexamples generated -/
def l: WithLog (concrete_st × String × concrete_st) concrete_st := ok (2, true)
def a: WithLog (concrete_st × String × concrete_st) concrete_st := ok (2, true)
def b: WithLog (concrete_st × String × concrete_st) concrete_st := ok (2, true)
def ob := (0,1,app_op_t.Disable)
def ol :=  (2,3,app_op_t.Enable)
def o := (4,5, app_op_t.Enable)
def o1 := (6,7,app_op_t.Disable)

/- evaluate the counterexamples generated -/

def lhs := merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b o) ob) ol)
#eval lhs

def rhs := do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b o) ob) ol)) o1
#eval rhs

/- draw the same two sides -/

def lhs_trace : Trace concrete_st := vc_lhs l.val a.val b.val ol o1 o ob
def rhs_trace : Trace concrete_st := vc_rhs l.val a.val b.val ol o1 o ob

-- Each must agree with the `.val` of the `WithLog` version directly above it, and
-- the two must differ from each other — that difference is the bug.
#eval lhs_trace.result
#eval rhs_trace.result

#html renderTrace lhs_trace
#html renderTrace rhs_trace

end counter1

namespace counter2

/- Vimala's counterexample -/
/- encode the counterexamples generated -/
def l: WithLog (concrete_st × String × concrete_st) concrete_st := ok (0, false)
def a: WithLog (concrete_st × String × concrete_st) concrete_st := ok (0, false)
def b: WithLog (concrete_st × String × concrete_st) concrete_st := ok (0, false)
def ob := (4,2,app_op_t.Disable)
def ol :=  (1,1,app_op_t.Enable)
def o := (3,2, app_op_t.Enable)
def o1 := (3,1,app_op_t.Disable)

/- evaluate the counterexamples generated -/

def lhs := merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b o) ob) ol)
#eval lhs

def rhs := do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b o) ob) ol)) o1
#eval rhs

/- draw the same two sides -/

def lhs_trace : Trace concrete_st := vc_lhs l.val a.val b.val ol o1 o ob
def rhs_trace : Trace concrete_st := vc_rhs l.val a.val b.val ol o1 o ob

-- Each must agree with the `.val` of the `WithLog` version directly above it, and
-- the two must differ from each other — that difference is the bug.
#eval lhs_trace.result
#eval rhs_trace.result

#html renderTrace lhs_trace
#html renderTrace rhs_trace

end counter2
