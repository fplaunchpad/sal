import LeanProofs1.Interface.Implementation
import LeanProofs1.Soundness.SequentialSpec

/-!
# The anchored FIFO queue: the implementation tuple

The Anchored FIFO queue row of Table 1, following Appendix
`app:dt-anchored-queue-paper-variant`. Enqueue inserts after the live tail
and dequeue removes the observed head. Coordinates retain the insertion
ancestry across merge, and descending coordinate order gives the FIFO order.

```
  Sigma = List (id, value, coordinate)      coordinate : List Bool
  sigma0 = []
  o = ins v p a        enqueue v, anchored at a with the anchor's coordinate p
  o = del x            dequeue the element with identity x
```

An insertion takes the event's **timestamp** as its identity and builds the
coordinate `p ++ Gamma (t - a)`, where `Gamma d` is `d` trues then a false.
Records are kept in descending key order, the key of a coordinate being its
bits read as `2`/`1` with a `3` appended, compared lexicographically.

`rc` is empty, as the appendix states.

No proof appears in this file. `Negative.lean` shows that no `rc` at all,
empty or otherwise, satisfies `Laws(D_type)` for this row.
-/

namespace LeanProofs1.Implementations.AnchoredQueue

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- A coordinate: the insertion ancestry, in bits. -/
abbrev Coord := List Bool

/-- A record: identity, value, coordinate. -/
abbrev Record := Nat × Nat × Coord

/-- `O_type`. An insertion carries its value, the anchor's coordinate, and
the anchor's identity. -/
inductive AppOp where
  | ins (value : Nat) (anchorCoord : Coord) (anchor : Nat)
  | del (target : Nat)
  deriving DecidableEq, Repr

/-- `Gamma d`: the unary code, `d` trues followed by a false. -/
def gamma (d : Nat) : Coord := List.replicate d true ++ [false]

/-- The comparison key of a coordinate. The trailing `3` makes a proper
prefix smaller than its extension. -/
def key (c : Coord) : List Nat := c.map (fun b => if b then 2 else 1) ++ [3]

/-- Strict lexicographic order on keys. -/
def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x < y then true else if y < x then false else lexLt xs ys

/-- The key of a record. -/
def recKey (z : Record) : List Nat := key z.2.2

/-- `Sigma`: the live records, in descending key order. -/
abbrev St := List Record

/-- The live identities. -/
def ids (S : St) : List Nat := S.map (fun z => z.1)

/-- Descending-key insertion: place `z` before the first strictly smaller
key, so equal keys retain delivery order. -/
def insertDown (z : Record) : St → St
  | [] => [z]
  | y :: Y => if lexLt (recKey y) (recKey z) then z :: y :: Y else y :: insertDown z Y

/-- Descending merge of two sorted lists: emit the larger head key, and on a
tie take the right head. -/
def mergeDown : St → St → St
  | [], Y => Y
  | X, [] => X
  | x :: X, y :: Y =>
      if lexLt (recKey y) (recKey x) then x :: mergeDown X (y :: Y)
      else y :: mergeDown (x :: X) Y

/-- `type = < O_type, Q_type, Val_type >`. The public query returns the head
as an optional identity and value. -/
@[reducible] def type : MRDTType where
  OType := AppOp
  decOType := inferInstance
  QType := Unit
  ValType := Option (Nat × Nat)

/-- `do`. An insertion whose identity is already live is a no-op; a deletion
drops the named identity. -/
def step (S : St) (e : Op AppOp) : St :=
  match e.op with
  | .ins v p a =>
      if e.time ∈ ids S then S
      else insertDown (e.time, v, p ++ gamma (e.time - a)) S
  | .del x => S.filter (fun z => z.1 ≠ x)

/-- `merge`. The ancestor distinguishes deletion of existing elements from
new insertions; values and coordinates are immutable. -/
def mergeState (l a b : St) : St :=
  mergeDown (a.filter (fun z => z.1 ∈ ids b || !(z.1 ∈ ids l)))
    (b.filter (fun z => !(z.1 ∈ ids l) && !(z.1 ∈ ids a)))

/-- `query`: the head's identity and value, if any. -/
def readHead (S : St) : Option (Nat × Nat) :=
  match S with
  | [] => none
  | z :: _ => some (z.1, z.2.1)

/-- `rc` is empty, as the appendix states. -/
def rcOf : AppOp → AppOp → OrderResult := fun _ _ => OrderResult.Either

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`, at an arbitrary
`rc`, because `Negative.lean` quantifies over every choice. -/
def D (rc : AppOp → AppOp → OrderResult) : Impl type where
  Sigma := St
  decSigma := inferInstance
  sigma0 := []
  do_ := step
  merge := mergeState
  query S _ := readHead S
  rc := rc

/-- The row's own `rc`, which is the empty one. -/
abbrev Dq : Impl type := D rcOf

/-! ## Issuance -/

/-- The live tail, as an identity and coordinate. -/
def tail? (S : St) : Option (Nat × Coord) :=
  (S.getLast?).map (fun z => (z.1, z.2.2))

/-- Issuance: an enqueue must anchor on the live tail, with a clock above
the tail identity; a dequeue must name the observed head. -/
def issuance (rc : AppOp → AppOp → OrderResult) : Issuance (D rc).toMRDTSig where
  CanIssue := fun e S =>
    match e.op with
    | .ins _ p a =>
        a < e.time ∧ ((S = [] ∧ a = 0 ∧ p = []) ∨ tail? S = some (a, p))
    | .del x => (readHead S).map Prod.fst = some x

end LeanProofs1.Implementations.AnchoredQueue
