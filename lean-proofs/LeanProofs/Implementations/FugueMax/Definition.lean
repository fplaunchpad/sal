import LeanProofs1.Interface.Implementation
import LeanProofs1.Soundness.SequentialSpec
import Mathlib.Data.Finset.Basic

/-!
# FugueMax with immutable birth records: the implementation and the specification

The FugueMax row of Table 1, following Appendix `app:dt-fugue-max`. An
insertion normally makes a right child of its visible predecessor; if that
predecessor already has a right child, it becomes a left child of the right
origin instead. **Immutable births** let the issuer find these origins even
after deletion, so the state carries a grow-only birth store beside the live
list.

```
  Sigma = List (id, value, coordinate) × Finset Birth,   sigma0 = ([], empty)
  o = ins p s      structural parent p, child side s
  o = del x        remove the live record x
```

The coordinate is the encoded ancestry chain `C(h)`, with the left and right
bands `u_L` and `u_R`, the chain-tag encoding `W`, and the terminator `3` in
`K(c) = c ++ [3]`. Unlike Sided Embedded RGA, the **right**-side delta code
is the complemented one.

Deleted births persist; each inserted identity is also its displayed value,
and the query returns the live identity list.

`rc` is empty, with the appendix's qualification that the laws hold "on
states arising in guarded executions". `Negative.lean` shows what that
qualification costs.

No proof appears in this file. The row has no obligations to bundle,
because `Negative.lean` refutes `Laws(D_type)` at the appendix's `rc`, so it
has a `Negative.lean` where a positive row has `VCs.lean` and
`Certificate.lean`.

## Where the identity lives

The appendix's sequential action is `insertAfter(t, l)`, which names the
event's timestamp. Definition 4 hands the specification the operation, not
the event, so `AppOp` carries `ts` and `issuance` pins it to the issuing
event's own timestamp. On every certified execution this is the appendix's
tuple. It is the same deviation RGA makes for the identity an insertion
allocates.
-/

namespace LeanProofs1.Implementations.FugueMax

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- Which child of its parent an insertion is. -/
inductive Side where
  | left
  | right
  deriving DecidableEq, Repr

/-- One entry of the ancestry chain. -/
inductive Chain where
  | L (d : Nat)
  | R (tau : List Nat) (d : Nat)
  deriving DecidableEq, Repr

/-- The structural part of an operation. -/
inductive Core where
  | ins (parent : Nat) (side : Side)
  | del (target : Nat)
  deriving DecidableEq, Repr

/-- `O_type`: the issuing event's timestamp, the structural operation, the
visible left origin, the optional right origin, and the encoded ancestry
chain. -/
structure AppOp where
  ts : Nat
  core : Core
  leftOrigin : Nat
  rightOrigin : Option Nat
  chain : List Chain
  deriving DecidableEq, Repr

/-- An event: an operation with its timestamp and replica. -/
abbrev Event := Op AppOp

/-- An immutable birth record. -/
structure Birth where
  time : Nat
  rep : Nat
  op : AppOp
  deriving DecidableEq, Repr

/-- `Gamma`: the unary code, monotone and prefix-free on positive
arguments. -/
def gamma (d : Nat) : List Bool := List.replicate d true ++ [false]

/-- The right band, on complemented bits. -/
def uR (b : Bool) : Nat := if b then 2 else 1
/-- The left band, on complemented bits. -/
def uL (b : Bool) : Nat := if b then 5 else 4

/-- `W(k)`, the chain-tag encoding. -/
def W (k : Nat) : List Nat := [(8 - k) / 3, (8 - k) % 3]

/-- `W*`, over a tag list. -/
def Wstar (tau : List Nat) : List Nat := tau.flatMap W

/-- `D_s(d)`: the delta code in the band of side `s`, on complemented
bits. -/
def Dside : Side → Nat → List Nat
  | .left, d => (gamma d).map (fun b => uL (!b))
  | .right, d => (gamma d).map (fun b => uR (!b))

/-- `F`, one chain entry. -/
def F : Chain → List Nat
  | .L d => Dside .left d
  | .R tau d => Wstar tau ++ Dside .right d

/-- `C(h)`, the whole chain. -/
def chainCoord (h : List Chain) : List Nat := h.flatMap F

/-- `K(c)`, with the terminator. -/
def key (c : List Nat) : List Nat := c ++ [3]

/-- Strict lexicographic order, a proper prefix being smaller. -/
def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x < y then true else if y < x then false else lexLt xs ys

/-- A live record: identity, value, coordinate. -/
abbrev Record := Nat × Nat × List Nat

def recKey (z : Record) : List Nat := key z.2.2

/-- `Sigma`: the live records, and the immutable births. -/
abbrev St := List Record × Finset Birth

/-- The identities the client sees. -/
def view (S : St) : List Nat := S.1.map (fun z => z.1)

/-- `ids(S)`. -/
def ids (S : List Record) : List Nat := S.map (fun z => z.1)

/-- `J`: descending-key insertion. -/
def insertDown (z : Record) : List Record → List Record
  | [] => [z]
  | y :: Y => if lexLt (recKey y) (recKey z) then z :: y :: Y else y :: insertDown z Y

/-- `M`: the two-list descending merge. -/
def mergeDown : List Record → List Record → List Record
  | [], Y => Y
  | X, [] => X
  | x :: X, y :: Y =>
      if lexLt (recKey y) (recKey x) then x :: mergeDown X (y :: Y)
      else y :: mergeDown (x :: X) Y

/-- `type = < O_type, Q_type, Val_type >`. The query returns identities. -/
@[reducible] def type : MRDTType where
  OType := AppOp
  decOType := inferInstance
  QType := Unit
  ValType := List Nat

/-- The birth record an event carries. -/
def birthOf (e : Event) : Birth := ⟨e.time, e.rep, e.op⟩

/-- `do`. An insertion records its birth whatever happens, and joins the
live list only when its identity is not already there. -/
def step (S : St) (e : Event) : St :=
  match e.op.core with
  | .ins _ _ =>
      if e.time ∈ ids S.1 then (S.1, insert (birthOf e) S.2)
      else (insertDown (e.time, e.time, chainCoord e.op.chain) S.1,
            insert (birthOf e) S.2)
  | .del x => (S.1.filter (fun z => z.1 ≠ x), S.2)

/-- `merge`: surviving records in descending order, births unioned. -/
def mergeState (l a b : St) : St :=
  (mergeDown (a.1.filter (fun z => z.1 ∈ ids b.1 || !(z.1 ∈ ids l.1)))
      (b.1.filter (fun z => !(z.1 ∈ ids l.1) && !(z.1 ∈ ids a.1))),
   a.2 ∪ b.2)

/-- `rc` is empty, as the appendix states. -/
def rcOf : AppOp → AppOp → OrderResult := fun _ _ => OrderResult.Either

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`, at an arbitrary
`rc`. Everything but `rc` is the row's own; `Negative.lean` needs the
parameter because it refutes the laws at the appendix's choice. -/
@[reducible] def D (rc : AppOp → AppOp → OrderResult) : Impl type where
  Sigma := St
  decSigma := inferInstance
  sigma0 := ([], ∅)
  do_ := step
  merge := mergeState
  query S _ := view S
  rc := rc

/-- The row's own tuple, with the appendix's empty `rc`. -/
@[reducible] def Df : Impl type := D rcOf

/-! ## `Spec`

The independent state is `(B, T)`: a permanent identity list and a set of
deleted identities. Structural parent, side, right origin and coordinate
chain are absent from the sequential action; they stay in the concrete
payload. Deleted identities remain usable as origins, and deleting the root
is a no-op.
-/

/-- `Phi = (B, T)`, initially `([0], empty)`. -/
abbrev SpecState := List Nat × Finset Nat

/-- `P(B, l, t)`: insert immediately after the first occurrence of the
origin. -/
def insertPos : List Nat → Nat → Nat → List Nat
  | [], _, _ => []
  | x :: X, l, t => if x = l then x :: t :: X else x :: insertPos X l t

/-- `q(B, T)`: the live identities, root excluded. -/
def specQuery (s : SpecState) : List Nat :=
  s.1.filter (fun x => decide (x ≠ 0 ∧ x ∉ s.2))

/-- `Spec`. `args` maps the concrete payload to the sequential action:
an insertion becomes `insertAfter(t, l)` and a deletion `deleteID(x)`. -/
def specMachine : HistoryMachine type.OType type.QType type.ValType where
  State := SpecState
  initial := ([0], ∅)
  transition s label t' :=
    match label with
    | .update o =>
        match o.core with
        | .ins _ _ =>
            o.ts ≠ 0 ∧ o.ts ∉ s.1 ∧ o.leftOrigin ∈ s.1
              ∧ t' = (insertPos s.1 o.leftOrigin o.ts, s.2)
        | .del x => x ∈ s.1 ∧ t' = (s.1, s.2 ∪ ({x} \ {0}))
    | .query _ answer => t' = s ∧ answer = specQuery s

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec type := specMachine.toSpec

/-! ## Issuance -/

/-- Issuance: the operation's copy of the identity is the issuing event's
own timestamp, an insertion's clock is above its parent, and a deletion
names a live identity. -/
def issuance (rc : AppOp → AppOp → OrderResult) : Issuance (D rc).toMRDTSig where
  CanIssue := fun e S =>
    let s : St := S
    e.op.ts = e.time ∧
    match e.op.core with
    | .ins p _ => p < e.time ∧ e.time ∉ ids s.1
    | .del x => x ∈ ids s.1

end LeanProofs1.Implementations.FugueMax
