import LeanProofs1.Interface.Implementation
import LeanProofs1.Soundness.SequentialSpec

/-!
# Embedded RGA: the implementation tuple

The Embedded RGA row of Table 1, following Appendix `app:dt-embed-rga`. An
insertion stores its ancestry as a **coordinate** rather than as tree edges.
Descending coordinate order gives depth-first, newest-sibling-first RGA
order; merge combines surviving records and deletion removes the named
identity.

```
  Sigma = List (id, value, coordinate)      coordinate : List Bool
  o = Ins v p a    insert v, anchored at a, carrying the anchor's coordinate
  o = Del x        remove the record with identity x
  c_e = p ++ enc (t - a)      K(c) = b_{1,2}(c) ++ [3]
```

The terminator `3` puts an ancestor before its descendants in descending
order, while monotone codewords put newer siblings first.

An insertion takes the event's **timestamp** as its identity, and `rc` is
empty, with the appendix's qualification that the laws hold "for the states
and event prefixes arising in guarded executions". `Negative.lean` shows
what that qualification costs.

This is the row the anchored FIFO queue and Embedded Peritext are built
from: the queue changes only the query, Peritext only the payload type.

No proof appears in this file.
-/

namespace LeanProofs1.Implementations.EmbeddedRGA

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- A coordinate: the insertion ancestry, in bits. -/
abbrev Coord := List Bool

/-- A record: identity, value, coordinate. -/
abbrev Record := Nat × Nat × Coord

/-- `O_type`. -/
inductive AppOp where
  | ins (value : Nat) (anchorCoord : Coord) (anchor : Nat)
  | del (target : Nat)
  deriving DecidableEq, Repr

/-- `enc`: the unary code, `d` trues then a false. It is monotone and
prefix-free on positive arguments, which is all the appendix asks. -/
def enc (d : Nat) : Coord := List.replicate d true ++ [false]

/-- `K(c)`: the bits as `2`/`1`, with the terminator `3`. -/
def key (c : Coord) : List Nat := c.map (fun b => if b then 2 else 1) ++ [3]

/-- Strict lexicographic order, a proper prefix being smaller. -/
def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x < y then true else if y < x then false else lexLt xs ys

def recKey (z : Record) : List Nat := key z.2.2

/-- `Sigma`. -/
abbrev St := List Record

/-- `I(S)`. -/
def ids (S : St) : List Nat := S.map (fun z => z.1)

/-- `J`: descending-key insertion. -/
def insertDown (z : Record) : St → St
  | [] => [z]
  | y :: Y => if lexLt (recKey y) (recKey z) then z :: y :: Y else y :: insertDown z Y

/-- `M`: the descending merge. -/
def mergeDown : St → St → St
  | [], Y => Y
  | X, [] => X
  | x :: X, y :: Y =>
      if lexLt (recKey y) (recKey x) then x :: mergeDown X (y :: Y)
      else y :: mergeDown (x :: X) Y

/-- `type = < O_type, Q_type, Val_type >`. The query is the payload list. -/
@[reducible] def type : MRDTType where
  OType := AppOp
  decOType := inferInstance
  QType := Unit
  ValType := List Nat

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
def payloads (S : St) : List Nat := S.map (fun z => z.2.1)

/-- `rc` is empty, as the appendix states. -/
def rcOf : AppOp → AppOp → OrderResult := fun _ _ => OrderResult.Either

/-- `D_type`, at an arbitrary `rc`. -/
def D (rc : AppOp → AppOp → OrderResult) : Impl type where
  Sigma := St
  decSigma := inferInstance
  sigma0 := []
  do_ := step
  merge := mergeState
  query S _ := payloads S
  rc := rc

/-- The row's own tuple, with the appendix's empty `rc`. -/
abbrev De : Impl type := D rcOf

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

end LeanProofs1.Implementations.EmbeddedRGA
