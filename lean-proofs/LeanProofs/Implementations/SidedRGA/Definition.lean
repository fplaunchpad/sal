import LeanProofs1.Interface.Implementation
import LeanProofs1.Soundness.SequentialSpec

/-!
# Sided Embedded RGA: the implementation tuple

The Sided Embedded RGA row of Table 1, following Appendix
`app:dt-sided-embed-rga`. Each coordinate encodes a root path of left/right
steps and timestamp differences, so an insertion may lie on **either** side
of its anchor.

```
  h_R d = b_{1,2}(enc d)              right-side band
  h_L d = b_{4,5}(complement (enc d)) left-side band
  c_e   = p ++ h_s (t - a)            K(c) = c ++ [3]
```

The symbol bands satisfy `R{1,2} < 3 < L{4,5}`, so descending keys give the
in-order reading: left descendants, then the anchor, then right
descendants. Complementing the bits in `h_L` is what makes a newer sibling
lie closer to its anchor on both sides, where the plain embedded row only
manages it on one.

Everything else — the insertion `J`, the three-way merge `M`, the
payload-list query — is the embedded row's, and so is `rc = ∅` with the
appendix's qualification that the laws hold "for the states and event
prefixes arising in guarded executions".

No proof appears in this file.
-/

namespace LeanProofs1.Implementations.SidedRGA

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- Which side of its anchor an insertion lies on. -/
inductive Side where
  | left
  | right
  deriving DecidableEq, Repr

/-- A coordinate: a root path over the symbol bands. -/
abbrev Coord := List Nat

/-- A record: identity, value, coordinate. -/
abbrev Record := Nat × Nat × Coord

/-- `O_type`. -/
inductive AppOp where
  | ins (value : Nat) (anchorCoord : Coord) (anchor : Nat) (side : Side)
  | del (target : Nat)
  deriving DecidableEq, Repr

/-- `enc`: the unary code, `d` trues then a false. -/
def enc (d : Nat) : List Bool := List.replicate d true ++ [false]

/-- `h_R`: the right band, `0 -> 1`, `1 -> 2`. -/
def hR (d : Nat) : Coord := (enc d).map (fun b => if b then 2 else 1)

/-- `h_L`: the left band on the complemented code, `0 -> 4`, `1 -> 5`, so a
complemented bit `b` lands on `4` when `b` is set. -/
def hL (d : Nat) : Coord := (enc d).map (fun b => if b then 4 else 5)

/-- The step a side contributes. -/
def hSide : Side → Nat → Coord
  | .right => hR
  | .left => hL

/-- `K(c)`: the path with the terminator `3`, which separates the bands. -/
def key (c : Coord) : List Nat := c ++ [3]

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

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type : MRDTType where
  OType := AppOp
  decOType := inferInstance
  QType := Unit
  ValType := List Nat

/-- `do`. An insertion whose identity is already live is a no-op. -/
def step (S : St) (e : Op AppOp) : St :=
  match e.op with
  | .ins v p a s =>
      if e.time ∈ ids S then S
      else insertDown (e.time, v, p ++ hSide s (e.time - a)) S
  | .del x => S.filter (fun z => z.1 ≠ x)

/-- `merge`. -/
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
abbrev Ds : Impl type := D rcOf

/-! ## Issuance -/

/-- Issuance: an insertion anchors at the root or at a live record whose
coordinate it carries, with a clock above the anchor; a deletion names a
live identity. -/
def issuance (rc : AppOp → AppOp → OrderResult) : Issuance (D rc).toMRDTSig where
  CanIssue := fun e S =>
    let s : St := S
    match e.op with
    | .ins _ p a _ =>
        a < e.time ∧ ((a = 0 ∧ p = []) ∨ ∃ v, ((a, v, p) : Record) ∈ s)
    | .del x => x ∈ ids s

end LeanProofs1.Implementations.SidedRGA
