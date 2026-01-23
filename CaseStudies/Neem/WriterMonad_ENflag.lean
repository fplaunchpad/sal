import Lean
import ProofWidgets
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Linarith



import Plausible

import Blaster



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
| (_, (rid, .Enable)) => save (s, "Enable", (Prod.fst s + 1, true)) ~~> fun () => ok ((Prod.fst s + 1, true))
| (_, (rid, .Disable)) => save (s, "Disable", (Prod.fst s, false)) ~~> fun () => ok ((Prod.fst s, false))
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

end counter1

namespace counter2

/- Vimala's counterexample -/
/- encode the counterexamples generated -/
def l: WithLog (concrete_st × String × concrete_st) concrete_st := ok (0, false)
def a: WithLog (concrete_st × String × concrete_st) concrete_st := ok (0, false)
def b: WithLog (concrete_st × String × concrete_st) concrete_st := ok (0, false)
def ob := (0,1,app_op_t.Disable)
def ol :=  (2,3,app_op_t.Enable)
def o := (4,5, app_op_t.Enable)
def o1 := (6,7,app_op_t.Disable)

/- evaluate the counterexamples generated -/

def lhs := merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b o) ob) ol)
#eval lhs

def rhs := do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b o) ob) ol)) o1
#eval rhs


open ProofWidgets Jsx in
def renderNode (state : concrete_st) : Html :=
  <div style={json% {
    border: "2px solid #3b82f6",
    borderRadius: "8px",
    padding: "12px 16px",
    backgroundColor: "#eff6ff",
    fontWeight: "bold",
    fontFamily: "arial",
    textAlign: "center",
    minWidth: "100px",
    margin: "0 auto",
    color: "#000000",
    fontSize: "20px"
  }}>
    {Html.text s!"({state.1}, {state.2})"}
  </div>

open ProofWidgets Jsx in
def renderEdge (label : String) : Html :=
  <div style={json% {
    display: "flex",
    flexDirection: "column",
    alignItems: "center",
    margin: "5px 0"
  }}>
    <div style={json% {
      width: "2px",
      height: "20px",
      backgroundColor: "#6b7280"
    }}/>
    <div style={json% {
      padding: "4px 12px",
      backgroundColor: "#fef3c7",
      border: "1px solid #f59e0b",
      borderRadius: "4px",
      fontSize: "20px",
      fontWeight: "1000",
      margin: "5px 0",
      color: "#000000"
    }}>
      {Html.text label}
    </div>
    <div style={json% {
      width: "2px",
      height: "20px",
      backgroundColor: "#6b7280"
    }}/>
  </div>


def splitAtMerge (lst : List ((concrete_st) × String × concrete_st)) (mergeLabel : String) :
    List ((concrete_st) × String × concrete_st) × List ((concrete_st) × String × concrete_st) :=
  let rec go (acc : List ((concrete_st) × String × concrete_st)) (rest : List ((concrete_st) × String × concrete_st)) :
      List ((concrete_st) × String × concrete_st) × List ((concrete_st) × String × concrete_st) :=
    match rest with
    | [] => (acc.reverse, [])
    | h :: t =>
      if h.2.1 == mergeLabel then
        (acc.reverse, t)
      else
        go (h :: acc) t
  go [] lst

open ProofWidgets Jsx in
def renderBranchingTreeFromList (lst : List ((concrete_st) × String × concrete_st)) : Html :=
  let (rootPath, afterLMerge) := splitAtMerge lst "LMerge"
  let (leftBranch, afterAMerge) := splitAtMerge afterLMerge "AMerge"
  let (rightBranch, afterBMerge) := splitAtMerge afterAMerge "BMerge"

  let finalNode := match rightBranch.getLast? with
    | some ((_, _), _, n1, n2) => (n1, n2)
    | none => match leftBranch.getLast? with
      | some ((_, _), _, n1, n2) => (n1, n2)
      | none => (0, false)

  let rootStart := match rootPath.head? with
    | some ((s1, s2), _, _, _) => (s1, s2)
    | none => (0, false);

  <div style={json% {
    padding: "20px",
    backgroundColor: "#f9fafb",
    borderRadius: "8px",
    border: "2px solid #e5e7eb",
    display: "flex",
    flexDirection: "column",
    alignItems: "center"
  }}>
    {renderNode rootStart}
    {rootPath.foldl (fun html ((_, _), label, n1, n2) =>
      Html.element "div" #[] #[html, renderEdge label, renderNode (n1, n2)]
    ) (Html.element "div" #[] #[])}

    <div style={json% {
      display: "flex",
      justifyContent: "center",
      gap: "100px",
      width: "100%",
      marginTop: "20px",
      marginBottom: "20px"
    }}>
      <div style={json% {
        display: "flex",
        flexDirection: "column",
        alignItems: "center"
      }}>
        <div style={json% {
          fontSize: "20px",
          fontWeight: "bold",
          color: "#6b7280",
          marginBottom: "10px"
        }}>
          {Html.text "Left Branch"}
        </div>
        {leftBranch.foldl (fun html ((_, _), label, n1, n2) =>
          Html.element "div" #[] #[html, renderEdge label, renderNode (n1, n2)]
        ) (Html.element "div" #[] #[])}
      </div>

      <div style={json% {
        display: "flex",
        flexDirection: "column",
        alignItems: "center"
      }}>
        <div style={json% {
          fontSize: "20px",
          fontWeight: "bold",
          color: "#6b7280",
          marginBottom: "10px"
        }}>
          {Html.text "Right Branch"}
        </div>
        {rightBranch.foldl (fun html ((_, _), label, n1, n2) =>
          Html.element "div" #[] #[html, renderEdge label, renderNode (n1, n2)]
        ) (Html.element "div" #[] #[])}
      </div>
    </div>

    <div style={json% {
      fontSize: "20px",
      fontWeight: "bold",
      color: "#6b7280",
      marginBottom: "10px"
    }}>
      {Html.text "↓ All paths converge ↓"}
    </div>

    {renderNode finalNode}

    {afterBMerge.foldl (fun html ((_, _), label, n1, n2) =>
      Html.element "div" #[] #[html, renderEdge label, renderNode (n1, n2)]
    ) (Html.element "div" #[] #[])}
  </div>

#html renderBranchingTreeFromList lhs.log
#html renderBranchingTreeFromList rhs.log

end counter2
