import Sal.MRDTs.Paper1.ConcreteVCExecution
import Sal.MRDTs.Paper1.CertifiedClosedExecution
import Sal.MRDTs.Instances.EnableWinsFlag
import Mathlib.Data.Finset.Max
import Mathlib.Data.Prod.Lex

/-! Neem Optional_register/App_mrdt.fst, with its finite partial-map domain.
The source has no read operation. We explicitly choose the active payload
with greatest timestamp (replica ID breaks unreachable timestamp ties).
The arithmetic, reset, flag, and equal-timestamp averaging branches below
are copied from the source rather than replaced by an event log. -/
namespace Sal.MRDTs.Instances.OptionalRegister
open Foundation

inductive Action where
  | set (value : Nat)
  | unset
  deriving DecidableEq, Repr

def Action.isSet : Action → Bool
  | .set _ => true
  | .unset => false

def valueOf (e : Op Action) : Nat := match e.op with
  | .set v => v
  | .unset => 0

abbrev Payload := Nat × Nat
abbrev Cell := (Int × Bool) × Payload

def zero : Cell := ((0,false),(0,0))

/-- A finite partial map, with normalized default lookup outside its domain.
The zero-outside condition is representational, not a reachability invariant. -/
structure State where
  domain : Finset Nat
  cells : Nat → Cell
  outside : ∀ r, r ∉ domain → cells r = zero

@[ext] theorem State.ext {s t : State} (domain : s.domain = t.domain)
    (cells : ∀ r, s.cells r = t.cells r) : s = t := by
  cases s; cases t
  simp_all only
  congr
  funext r; exact cells r

def initial : State := ⟨∅,fun _ => zero,by simp⟩

def update (s : State) (e : Op Action) : State := match e.op with
  | .set v => ⟨insert e.rep s.domain,
      fun r => if r = e.rep then (((s.cells r).1.1 + 1,true),(e.time,v)) else s.cells r,
      by intro r h
         have absent : r ≠ e.rep ∧ r ∉ s.domain := by simpa using h
         simp [absent.1,s.outside r absent.2]⟩
  | .unset => ⟨s.domain,fun r => (((s.cells r).1.1,false),(0,0)),
      by intro r h; simp [s.outside r h,zero]⟩

def mergePayload (_l a b : Payload) : Payload :=
  if a.1 = b.1 then (a.1,(a.2+b.2)/2)
  else if a.1 > b.1 then a else b

def mergeCell (l a b : Cell) : Cell :=
  let flag := NeemFlag.mergeFlag l.1 a.1 b.1
  let payload := if !flag then (0,0)
    else if !a.1.2 then b.2
    else if !b.1.2 then a.2
    else mergePayload l.2 a.2 b.2
  ((a.1.1+b.1.1-l.1.1,flag),payload)

@[simp] theorem mergeCell_zero : mergeCell zero zero zero = zero := rfl

def merge (l a b : State) : State :=
  ⟨l.domain ∪ (a.domain ∪ b.domain),fun r => mergeCell (l.cells r) (a.cells r) (b.cells r),
    by intro r h
       have absent : r ∉ l.domain ∧ r ∉ a.domain ∧ r ∉ b.domain := by simpa using h
       change mergeCell (l.cells r) (a.cells r) (b.cells r) = zero
       rw [l.outside r absent.1,a.outside r absent.2.1,b.outside r absent.2.2,mergeCell_zero]⟩

/-- Active candidates retain replica IDs solely for a deterministic read on raw
states with a timestamp tie; actual events have globally unique timestamps. -/
abbrev Write := Lex (Nat × Lex (Nat × Nat))

def candidates (s : State) : Finset Write :=
  (s.domain.filter (fun r => (s.cells r).1.2)).image
    (fun r => toLex ((s.cells r).2.1,toLex (r,(s.cells r).2.2)))

/-- Lexicographic winner: timestamp, then replica, then value. -/
def winner (s : State) : Option Write :=
  if h : (candidates s).Nonempty then some ((candidates s).max' h) else none

def query (s : State) : Option Nat := (winner s).map (fun c => (ofLex (ofLex c).2).2)

noncomputable def D : MRDTSig where
  State := State
  dec_state := fun _ _ => Classical.propDecidable _
  init := initial
  AppOp := Action
  dec_op := inferInstance
  Query := Unit
  Value := Option Nat
  update := update
  merge := merge
  query := fun s _ => query s

def generation : Issuance D where
  CanIssue := fun e _ => 0 < e.time

/-- The source state refinement; it is stronger than map normalization and
needs positive issued timestamps to be preserved by a Set of value zero. -/
def SourceWellFormed (s : State) : Prop :=
  ∀ r ∈ s.domain, (s.cells r).1.2 = false ↔ (s.cells r).2 = (0,0)

end Sal.MRDTs.Instances.OptionalRegister
