import LeanProofs1.Interface.Implementation
import LeanProofs1.Soundness.SequentialSpec

/-!
# Embedded Peritext: the implementation tuple

The Embedded Peritext row of Table 1, following Appendix
`app:dt-peritext-embed-rga`. Characters and formatting boundaries share one
embedded sequence. A mark uses two independent boundary insertions, and the
rendering scan collects all open marks with no last-writer-wins resolution.

The concrete state, initial state, update, merge and payload-list query are
those of Embedded RGA (`app:dt-embed-rga`) with this payload type:

```
  Sigma = List (id, payload, coordinate)        coordinate : List Bool
  o = Ins v p a    insert v, anchored at a, carrying the anchor coordinate p
  o = Del x        remove the record with identity x
```

An insertion takes the event's **timestamp** as its identity and builds the
coordinate `p ++ enc (t - a)`. Records are kept in descending key order, the
key of a coordinate being its bits read as `2`/`1` with a `3` appended, so
an ancestor precedes its descendants and newer siblings come first.

`rc` is empty, as the appendix states, with the qualification that the
update and merge laws hold "for the states and event prefixes arising in
guarded executions". `Negative.lean` shows what that qualification costs.

No proof appears in this file.
-/

namespace LeanProofs1.Implementations.Peritext

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- The formatting marks of the source. -/
inductive Mark where
  | bold
  | italic
  | underline
  | strike
  | link (url : Nat)
  | comment (author text : Nat)
  | colour (value : Nat)
  | heading (level : Nat)
  deriving DecidableEq, Repr

/-- A payload: a character, or one boundary of a mark. `b` says whether the
boundary starts or ends the mark, and `j` is the mark identity, which is
independent of the insertion identities of its two boundaries. -/
inductive Payload where
  | char (glyph : Nat)
  | bound (j : Nat) (m : Mark) (isStart : Bool)
  deriving DecidableEq, Repr

/-- A coordinate: the insertion ancestry, in bits. -/
abbrev Coord := List Bool

/-- A record: identity, payload, coordinate. -/
abbrev Record := Nat × Payload × Coord

/-- `O_type`. -/
inductive AppOp where
  | ins (value : Payload) (anchorCoord : Coord) (anchor : Nat)
  | del (target : Nat)
  deriving DecidableEq, Repr

/-- `enc`: the unary code, `d` trues followed by a false. It is monotone and
prefix-free on positive arguments, which is all the appendix asks of it. -/
def enc (d : Nat) : Coord := List.replicate d true ++ [false]

/-- `K(c)`: the comparison key. The trailing `3` puts an ancestor before its
descendants in descending order. -/
def key (c : Coord) : List Nat := c.map (fun b => if b then 2 else 1) ++ [3]

/-- Strict lexicographic order on keys, a proper prefix being smaller. -/
def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x < y then true else if y < x then false else lexLt xs ys

/-- The key of a record. -/
def recKey (z : Record) : List Nat := key z.2.2

/-- `Sigma`. -/
abbrev St := List Record

/-- `I(S)`: the live identities. -/
def ids (S : St) : List Nat := S.map (fun z => z.1)

/-- `J`: descending-key insertion. -/
def insertDown (z : Record) : St → St
  | [] => [z]
  | y :: Y => if lexLt (recKey y) (recKey z) then z :: y :: Y else y :: insertDown z Y

/-- `M`: the descending merge of two lists. -/
def mergeDown : St → St → St
  | [], Y => Y
  | X, [] => X
  | x :: X, y :: Y =>
      if lexLt (recKey y) (recKey x) then x :: mergeDown X (y :: Y)
      else y :: mergeDown (x :: X) Y

/-- `type = < O_type, Q_type, Val_type >`. The registered query is the
payload list. -/
@[reducible] def type : MRDTType where
  OType := AppOp
  decOType := inferInstance
  QType := Unit
  ValType := List Payload

/-- `do`. An insertion whose identity is already live is a no-op. -/
def step (S : St) (e : Op AppOp) : St :=
  match e.op with
  | .ins v p a =>
      if e.time ∈ ids S then S
      else insertDown (e.time, v, p ++ enc (e.time - a)) S
  | .del x => S.filter (fun z => z.1 ≠ x)

/-- `merge`: surviving records of each branch, merged in descending order. -/
def mergeState (l a b : St) : St :=
  mergeDown (a.filter (fun z => z.1 ∈ ids b || !(z.1 ∈ ids l)))
    (b.filter (fun z => !(z.1 ∈ ids l) && !(z.1 ∈ ids a)))

/-- `q(S)`: the payload list. -/
def payloads (S : St) : List Payload := S.map (fun z => z.2.1)

/-- The rendering scan, the appendix's additional observation: a start
boundary opens a mark, an end boundary closes it, and a character emits
itself with the marks open at that point. -/
def renderAux : List (Nat × Mark) → St → List (Nat × List (Nat × Mark))
  | _, [] => []
  | open_, z :: Z =>
      match z.2.1 with
      | .char g => (g, open_) :: renderAux open_ Z
      | .bound j m true => renderAux ((j, m) :: open_) Z
      | .bound j _ false => renderAux (open_.filter (fun p => p.1 ≠ j)) Z

/-- The rendered document. -/
def render (S : St) : List (Nat × List (Nat × Mark)) := renderAux [] S

/-- `rc` is empty, as the appendix states. -/
def rcOf : AppOp → AppOp → OrderResult := fun _ _ => OrderResult.Either

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`, at an arbitrary
`rc`, because `Negative.lean` speaks about more than one choice. -/
def D (rc : AppOp → AppOp → OrderResult) : Impl type where
  Sigma := St
  decSigma := inferInstance
  sigma0 := []
  do_ := step
  merge := mergeState
  query S _ := payloads S
  rc := rc

/-- The row's own tuple, with the appendix's empty `rc`. -/
abbrev Dp : Impl type := D rcOf

/-! ## Issuance -/

/-- Issuance: an insertion anchors at the root or at a live record whose
coordinate it carries, with a clock above the anchor; a deletion names a
live identity. -/
def issuance (rc : AppOp → AppOp → OrderResult) : Issuance (D rc).toMRDTSig where
  CanIssue := fun e S =>
    let s : St := S
    match e.op with
    | .ins _ p a =>
        a < e.time ∧ ((a = 0 ∧ p = []) ∨ ∃ v, ((a, v, p) : Record) ∈ s)
    | .del x => x ∈ ids s

end LeanProofs1.Implementations.Peritext
