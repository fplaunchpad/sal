import Artifact.MRDTs.Paper1.CertifiedClosedExecution
import Artifact.MRDTs.Paper1.ConcreteVCExecution
import Mathlib.Data.Finset.Max
import Mathlib.Data.Prod.Lex

/-!
# The optional register: its implementation tuple

The Optional register row of Table 1, Appendix `app:dt-optional-register`.
A register whose payload may be absent, over the flag core beside it. The
active payload is the one with the greatest `(timestamp, replica)` key.

The flag's namespaces sit beside this row rather than inside it: nested,
the register's own `Cell` and `State` would shadow the flag's.
-/

namespace LeanProofs.Implementations.OptionalRegisterFlag
open Artifact.MRDTs
open Artifact.MRDTs.Paper1
open Artifact.MRDTs.Foundation

inductive Action where
  | winning
  | reset
  deriving DecidableEq

abbrev Cell := Int × Bool
abbrev State := Nat → Cell

def initial (initialFlag : Bool) : State := fun _ => (0,initialFlag)
def update (s : State) (e : Op Action) : State := match e.op with
  | .winning => fun r => if r = e.2.1 then ((s r).1 + 1,true) else s r
  | .reset => fun r => ((s r).1,false)

def mergeFlag (l a b : Cell) : Bool :=
  if a.2 && b.2 then true
  else if !a.2 && !b.2 then false
  else if a.2 then decide (a.1 > l.1)
  else decide (b.1 > l.1)
def mergeCell (l a b : Cell) : Cell := (a.1 + b.1 - l.1,mergeFlag l a b)
def merge (l a b : State) : State := fun r => mergeCell (l r) (a r) (b r)
noncomputable def active (s : State) : Bool := by
  classical
  exact decide (∃ r, (s r).2 = true)
noncomputable def D (initialFlag : Bool) (invert : Bool := false) : MRDTSig where
  State := State
  dec_state := fun _ _ => Classical.propDecidable _
  init := initial initialFlag
  AppOp := Action
  dec_op := inferInstance
  Query := Unit
  Value := Bool
  update := update
  merge := merge
  query := fun s _ => if invert then !active s else active s

def generation (initialFlag : Bool) (invert : Bool := false) : Issuance (D initialFlag invert) where
  CanIssue := fun _ _ => True

theorem active_true_iff (s : State) : active s = true ↔ ∃ r, (s r).2 = true := by
  classical
  simp [active]

theorem active_initial (initialFlag : Bool) : active (initial initialFlag) = initialFlag := by
  cases initialFlag <;> simp [active,initial]

theorem active_winning (s : State) (ts r : Nat) :
    active (update s (ts,r,.winning)) = true := by
  rw [active_true_iff]
  exact ⟨r,by simp [update,Op.op]⟩
theorem active_reset (s : State) (ts r : Nat) :
    active (update s (ts,r,.reset)) = false := by
  simp [active,update,Op.op]

end LeanProofs.Implementations.OptionalRegisterFlag

namespace LeanProofs.Implementations.OptionalRegisterFlagInstance
abbrev Action := OptionalRegisterFlag.Action
abbrev State := OptionalRegisterFlag.State
def enable : Action := .winning
def disable : Action := .reset
abbrev initial := OptionalRegisterFlag.initial false
abbrev update := OptionalRegisterFlag.update
abbrev merge := OptionalRegisterFlag.merge
noncomputable abbrev D := OptionalRegisterFlag.D false
abbrev generation := OptionalRegisterFlag.generation false
noncomputable abbrev query := OptionalRegisterFlag.active
end LeanProofs.Implementations.OptionalRegisterFlagInstance

namespace LeanProofs.Implementations.OptionalRegister
open Artifact.MRDTs
open Artifact.MRDTs.Paper1
open Artifact.MRDTs.Foundation

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
  let flag := OptionalRegisterFlag.mergeFlag l.1 a.1 b.1
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

end LeanProofs.Implementations.OptionalRegister
