import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

import Std.Tactic.BVDecide
import CaseStudies.Interfaces.Set_extended
import Std

import Blaster


open Classical Std


structure set_with_universe (α: Type) [ToString α] [DecidableEq α] [Hashable α] where
_set : set α
_universe : HashSet α

instance {α} [ToString α] [DecidableEq α] [Hashable α] : ToString (set_with_universe α) where
  toString a := let s := a._set
  let univ := a._universe
  let members := univ.fold (fun acc elem => if mem elem s then (toString elem)::acc else acc) []
  let rec str_process_fun (l : List String) :=  (match l with
  | [] => ""
  | [x] => x
  | x::xs => x ++ "," ++ (str_process_fun xs))
  s! "#[{str_process_fun members}]#"


abbrev concrete_st_viz (α : Type) [ToString α] [DecidableEq α] [Hashable α] := set_with_universe α


@[simp]
def init_st_viz {α: Type} [ToString α] [DecidableEq α] [Hashable α] (init_st : set α): concrete_st_viz α := {_set := init_st, _universe:={}}




structure WithLog (logged : Type) (α : Type) [ToString α] [ToString logged] where
  log : List logged
  val : α

instance {α logged} [ToString α] [ToString logged] : ToString (WithLog logged α) where
  toString x := "{" ++ s!"log := {toString x.log}, val := {toString x.val}" ++ "}"


def andThen {α β γ} [ToString α] [ToString β] [ToString γ] (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}


def ok {α}  [ToString α] [DecidableEq α] [Hashable α]  (x : concrete_st_viz α) : WithLog (concrete_st_viz α × String × concrete_st_viz α) (concrete_st_viz α) := {log := [], val := x}

def save {α} [ToString α] (data : α) : WithLog α Unit :=
  {log := [data], val := ()}

infixl:55 " ~~> " => andThen

def do_viz {β : Type} {α: Type} [ToString α] [DecidableEq α] [Hashable α] (do_: set α → (ℕ × ℕ × β) → set α)
(ls:  WithLog (concrete_st_viz α × String × concrete_st_viz α)
(concrete_st_viz α)) (o: ℕ × ℕ ×  β) (univ_add : (ℕ × ℕ × β) → α) (op_string : (ℕ × ℕ × β) → String)
: WithLog (concrete_st_viz α × String × concrete_st_viz α) (concrete_st_viz α)
:=
let s := ls.val
let _set := s._set
let _universe := s._universe
let final_set := do_ _set o
let final_universe := _universe.insert (univ_add o)
let structure_toret : concrete_st_viz α := {_set := final_set, _universe := final_universe}
{log := ls.log, val := ()} ~~> fun () =>
  save (s, s!"{op_string o}", structure_toret) ~~> fun () =>
  ok (structure_toret)



def merge_viz {α : Type} [ToString α] [DecidableEq α] [Hashable α] (merge : set α → set α → set α → set α) (l a b: WithLog (concrete_st_viz α × String × concrete_st_viz α) (concrete_st_viz α)) :
WithLog (concrete_st_viz α × String × concrete_st_viz α) (concrete_st_viz α) :=
let lval := l.val
let aval := a.val
let bval := b.val
let lset := lval._set
let aset := aval._set
let bset := bval._set
let l_univ := lval._universe
let a_univ := aval._universe
let b_univ := bval._universe
let set_result := merge lset aset bset
let universe_result := l_univ.union (a_univ.union b_univ)
let result : concrete_st_viz α := {_set:=set_result, _universe:= universe_result}
{log := l.log ++ [(lval, "LMerge", result)] ++
 a.log ++ [(aval, "AMerge", result)] ++
 b.log ++ [(bval, "BMerge", result)]
 val := ()} ~~> fun () => ok (result)


open ProofWidgets Jsx in
def renderNode  {α : Type} [ToString α] [DecidableEq α] [Hashable α]  (state : concrete_st_viz α) : Html :=
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
    {Html.text (toString state)}
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


def splitAtMerge {α : Type} [ToString α] [DecidableEq α] [Hashable α]  (lst : List ((concrete_st_viz α) × String × concrete_st_viz α)) (mergeLabel : String) :
    List ((concrete_st_viz α) × String × concrete_st_viz α) × List ((concrete_st_viz α) × String × concrete_st_viz α) :=
  let rec go (acc : List ((concrete_st_viz α) × String × concrete_st_viz α)) (rest : List ((concrete_st_viz α) × String × concrete_st_viz α)) :
      List ((concrete_st_viz α) × String × concrete_st_viz α) × List ((concrete_st_viz α) × String × concrete_st_viz α) :=
    match rest with
    | [] => (acc.reverse, [])
    | h :: t =>
      if h.2.1 == mergeLabel then
        (acc.reverse, t)
      else
        go (h :: acc) t
  go [] lst

def splitAtMerge' {α : Type} [ToString α] [DecidableEq α] [Hashable α]  (lst : List ((concrete_st_viz α) × String × concrete_st_viz α)) (mergeLabel : String) :
    List ((concrete_st_viz α) × String × concrete_st_viz α) × List ((concrete_st_viz α) × String × concrete_st_viz α) :=
  let rec go (acc : List ((concrete_st_viz α) × String × concrete_st_viz α)) (rest : List ((concrete_st_viz α) × String × concrete_st_viz α)) :
      List ((concrete_st_viz α) × String × concrete_st_viz α) × List ((concrete_st_viz α) × String × concrete_st_viz α) :=
    match rest with
    | [] => (acc.reverse, [])
    | h :: t =>
      if h.2.1 == mergeLabel then
        ((h::acc).reverse, t)
      else
        go (h :: acc) t
  go [] lst

open ProofWidgets Jsx in
def renderBranchingTreeFromList {α : Type} [ToString α] [DecidableEq α] [Hashable α]  (lst : List ((concrete_st_viz α) × String × concrete_st_viz α)) : Html :=
  let (rootPath, afterLMerge) := splitAtMerge lst "LMerge"
  let (leftBranchFull, afterAMerge) := splitAtMerge afterLMerge "AMerge"
  let (rightBranchFull, afterBMerge) := splitAtMerge afterAMerge "BMerge"
  let (mergePath,_) := splitAtMerge' lst "LMerge"

  let leftBranch := leftBranchFull.drop rootPath.length
  let rightBranch := rightBranchFull.drop rootPath.length


  let finalNode := match mergePath.getLast? with
    | some (_, _, y) => y
    | none => {_set := empty, _universe:={}}

  let rootStart := match rootPath.head? with
    | some (y, _, _) => y
    | none => {_set := empty, _universe:={}};

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
    {rootPath.foldl (fun html (_, label, y) =>
      Html.element "div" #[] #[html, renderEdge label, renderNode y]
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
        {leftBranch.foldl (fun html (_, label, y) =>
          Html.element "div" #[] #[html, renderEdge label, renderNode y]
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
        {rightBranch.foldl (fun html (_, label, y) =>
          Html.element "div" #[] #[html, renderEdge label, renderNode y]
        ) (Html.element "div" #[] #[])}
      </div>
    </div>

    <div style={json% {
      fontSize: "20px",
      color: "#6b7280",
      marginBottom: "10px"
    }}>
      {Html.text "↓ All paths converge ↓"}
    </div>

    {renderNode finalNode}

    {afterBMerge.foldl (fun html (_, label, y) =>
      Html.element "div" #[] #[html, renderEdge label, renderNode y]
    ) (Html.element "div" #[] #[])}
  </div>
