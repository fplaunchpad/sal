import LeanProofs_no_spec_non_comm.Interface.Implementation
import LeanProofs_no_spec_non_comm.Soundness.SequentialSpec
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Prod.Lex
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# The add-wins priority queue: the implementation tuple

The Priority queue row of Table 1, following Appendix
`app:dt-add-wins-priority-queue`. Each addition creates an insertion record.
An increment attaches to the insertions visible at its issuer, and a removal
disables those observed insertions, so an unseen concurrent addition
survives.

The state is three finite sets, all grow-only:

```
  B : births      ((x, u), v)      element x, add timestamp u, innate value v
  I : increments  ((x, u), t, n)   increment t of amount n, attached to (x, u)
  R : removed     (x, u)           disabled insertion tags
  merge(l, a, b) = (B_a ∪ B_b, I_a ∪ I_b, R_a ∪ R_b)        ancestor ignored
```

All three effects are additions to immutable stores, so **every pair of
events commutes** and `rc` is empty. Repeated receipt of one increment does
not count twice, because attachments form a set.

The returned priority takes both the innate value and the increments from
the **same** latest surviving insertion, which is the appendix's repair of
the published query.

No proof appears in this file.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.PriorityQueue

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

/-- An insertion tag: the element and the timestamp of its addition. -/
abbrev Tag := Nat × Nat
/-- A birth: a tag and the innate value it carries. -/
abbrev Birth := Tag × Int
/-- An attachment: a tag, the increment's identity, and its amount. -/
abbrev Attachment := Tag × Nat × Int

/-- `O_type`. The observed sets are the insertion timestamps the issuer saw. -/
inductive AppOp where
  | add (element : Nat) (innate : Int)
  | inc (element : Nat) (amount : Int) (observed : Finset Nat)
  | remove (element : Nat) (observed : Finset Nat)
  deriving DecidableEq

/-- The queries of the row. -/
inductive Query where
  | empty
  | lookup (element : Nat)
  | getPri (element : Nat)
  | getMax
  deriving DecidableEq

/-- The tagged answers. -/
inductive Answer where
  | boolean (b : Bool)
  | priority (p : Option Int)
  | maximum (m : Option (Nat × Int))
  deriving DecidableEq

/-- `Sigma`: births, attachments and disabled tags. -/
structure St where
  births : Finset Birth := ∅
  increments : Finset Attachment := ∅
  removed : Finset Tag := ∅
  deriving DecidableEq

@[ext] theorem St.ext {a b : St} (hb : a.births = b.births)
    (hi : a.increments = b.increments) (hr : a.removed = b.removed) : a = b := by
  cases a; cases b; simp_all

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type : MRDTType where
  OType := AppOp
  decOType := inferInstance
  QType := Query
  ValType := Answer

/-- `do`: each effect adds to one immutable store. -/
def step (s : St) (e : Op AppOp) : St :=
  match e.op with
  | .add x v => { s with births := insert ((x, e.time), v) s.births }
  | .inc x n W =>
      { s with increments := s.increments ∪ W.image (fun u => ((x, u), e.time, n)) }
  | .remove x W => { s with removed := s.removed ∪ W.image (fun u => (x, u)) }

/-- `merge`: componentwise union. The ancestor is ignored. -/
def mergeState (_l a b : St) : St :=
  ⟨a.births ∪ b.births, a.increments ∪ b.increments, a.removed ∪ b.removed⟩

/-! ## The query -/

/-- `A_sigma(x,u)`: the increments attached to one insertion. -/
def acquired (s : St) (tag : Tag) : Int :=
  ∑ a ∈ s.increments.filter (fun a => a.1 = tag), a.2.2

/-- The live births of `x`, keyed by timestamp then innate value. -/
noncomputable def candidates (s : St) (x : Nat) : Finset (Lex (Nat × Int)) :=
  (s.births.filter (fun b => b.1.1 = x ∧ b.1 ∉ s.removed)).image
    (fun b => toLex (b.1.2, b.2))

/-- `p_sigma(x)`: the innate value of the latest surviving insertion, plus
that same insertion's increments. -/
noncomputable def priority (s : St) (x : Nat) : Option Int :=
  (candidates s x).max.map (fun b => (ofLex b).2 + acquired s (x, (ofLex b).1))

/-- `E_sigma`: the elements with a surviving insertion. -/
def elements (s : St) : Finset Nat :=
  (s.births.filter (fun b => b.1 ∉ s.removed)).image (fun b => b.1.1)

/-- `maximum(E, p)`, with ties on the priority broken by the greatest
element identity. Shared between the implementation's query and the
specification's, so that the two agree as soon as `(E, p)` does. -/
noncomputable def maximumOf (E : Finset Nat) (p : Nat → Option Int) :
    Option (Nat × Int) :=
  ((E.filter (fun x => (p x).isSome)).image
      (fun x => toLex ((p x).getD 0, x))).max.map
    (fun m => ((ofLex m).2, (ofLex m).1))

/-- The implementation's `getMax`. -/
noncomputable def getMax (s : St) : Option (Nat × Int) :=
  maximumOf (elements s) (priority s)

/-- `query`. -/
noncomputable def read (s : St) : Query → Answer
  | .empty => .boolean (decide (elements s = ∅))
  | .lookup x => .boolean (decide (x ∈ elements s))
  | .getPri x => .priority (priority s x)
  | .getMax => .maximum (getMax s)

/-- `rc` is empty: the immutable concrete effects commute. -/
def rcOf : AppOp → AppOp → OrderResult := fun _ _ => OrderResult.Either

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`. -/
noncomputable def D : Impl type where
  Sigma := St
  decSigma := inferInstance
  sigma0 := {}
  do_ := step
  merge := mergeState
  query := read
  rc := rcOf


/-! ## `Spec`

A finite partial priority map, with all updates total. Every finite run from
the empty map is admitted, so the only thing a history has to get right is
the answer it reports.

The specification has no insertion identities, no attachment store and no
timestamp order. That is why it cannot explain an arbitrary replay: the
implementation resolves two additions of one element by the greater
timestamp, while the specification takes the later one in the history.
`VCs.lean` chooses the history that reconciles them. -/

/-- The specification's state: the domain, and the cell of each element. -/
abbrev SpecState := Finset Nat × (Nat → Option Int)

/-- The specification as a deterministic machine. -/
noncomputable def specMachine : DeterministicSpec type.OType type.QType type.ValType where
  State := SpecState
  initial := (∅, fun _ => none)
  update m o := match o with
    | .add x v => (insert x m.1, fun y => if y = x then some v else m.2 y)
    | .inc x n _ =>
        match m.2 x with
        | some v => (m.1, fun y => if y = x then some (v + n) else m.2 y)
        | none => m
    | .remove x _ => (m.1.erase x, fun y => if y = x then none else m.2 y)
  query m q := match q with
    | .empty => .boolean (decide (m.1 = ∅))
    | .lookup x => .boolean (decide (x ∈ m.1))
    | .getPri x => .priority (m.2 x)
    | .getMax => .maximum (maximumOf m.1 m.2)

/-- `Spec` as a language of histories. -/
noncomputable def historySpec : Soundness.Spec type := specMachine.toSpec

/-! ## Issuance -/

/-- `T_sigma`: every tag the state knows, whether from a birth or from an
attachment. -/
def recordTags (s : St) : Finset Tag :=
  s.births.image Prod.fst ∪ s.increments.image Prod.fst

/-- `L_sigma`: the tags that are not disabled. -/
def liveTags (s : St) : Finset Tag := recordTags s \ s.removed

/-- `W_sigma(x)`: the surviving insertion timestamps of `x`. -/
def observed (s : St) (x : Nat) : Finset Nat :=
  ((liveTags s).filter (fun t => t.1 = x)).image Prod.snd

/-- Issuance: `add` only when the element is absent, `inc` and `remove`
only when present and carrying exactly the observed insertion identities. -/
def issuance : Issuance D.toMRDTSig where
  CanIssue := fun e s =>
    match e.op with
    | .add x _ => observed s x = ∅
    | .inc x _ W => observed s x ≠ ∅ ∧ W = observed s x
    | .remove x W => observed s x ≠ ∅ ∧ W = observed s x

end LeanProofs.NoSpecNonComm.Implementations.PriorityQueue
