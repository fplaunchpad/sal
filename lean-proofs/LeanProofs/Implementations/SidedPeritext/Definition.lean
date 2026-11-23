import LeanProofs1.Implementations.SidedRGA.Definition
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Sided Peritext: the implementation and the specification

The Sided Peritext row of Table 1, following Appendix
`app:dt-sided-peritext-rich-core`. A retained insertion shadow orders text,
while separate grow-only stores record logical deletions and formatting
marks. Rendering resolves deleted anchors to nearby survivors and selects
the greatest mark timestamp per character and mark type.

```
  Sigma = (S, D, F),  sigma0 = ([], empty, empty)
  do((S,D,F), t, r, Text o)            = (do(S,t,r,o), D, F)
  do((S,D,F), t, r, RecordDeletion x)  = (S, D u {x}, F)
  do((S,D,F), t, r, RecordMark m)      = (S, D, F u {m})
  merge(l,a,b) = (merge(S_l,S_a,S_b), D_a u D_b, F_a u F_b)
```

The insertion shadow uses the carrier, coordinates, update and merge of
Sided Embedded RGA, so this file imports that row rather than repeating
them. The evidence-store merge ignores the ancestor.

Table 1 combines the **core** and the **rendered** interface over this one
carrier, so `Q_type` selects between them: the core interface returns the
shadow value list or one of the two stores, and the rendered interface takes
a mark type and returns the document-order rich query.

`rc` is empty, with the appendix's qualification that the laws hold "for the
states and event prefixes arising in guarded executions". `Negative.lean`
shows what that qualification costs, and shows that for this row it costs
more than deletion: two **insertions** already fail.

## Where the identity lives

The sided editor specification reads the event's timestamp, both as the
identity `V_e` inserts and in `Admit`'s clock test. Definition 4 hands the
specification the operation, not the event, so `TextOp.ins` carries `ts` and
`issuance` pins it to the issuing event's own timestamp. `do` still reads
`e.time`, so on every certified execution this is the appendix's tuple. It
is the same deviation RGA makes for the identity an insertion allocates.

No proof appears in this file.
-/

namespace LeanProofs1.Implementations.SidedPeritext

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-! ## Marks -/

/-- The mark types the row renders. -/
inductive MarkType where
  | bold | italic | underline | strike | link | comment | colour | heading
  deriving DecidableEq, Repr

/-- A mark either applies or retracts its type. -/
inductive MarkOp where
  | add | remove
  deriving DecidableEq, Repr

/-- Which side of its anchor an endpoint sits on. -/
inductive EndSide where
  | before | after
  deriving DecidableEq, Repr

/-- A mark record. The document-order renderer ignores the paths and the
mark value. -/
structure Mark where
  mid : Nat
  ty : MarkType
  op : MarkOp
  value : Nat
  startID : Nat
  endID : Nat
  startSide : EndSide
  endSide : EndSide
  startPath : List Nat := []
  endPath : List Nat := []
  deriving DecidableEq, Repr

/-! ## Operations and the carrier -/

/-- The text operation, over the sided row's coordinates and sides. `ts` is
the issuing event's timestamp, carried so that the specification can read
the identity an insertion allocates. -/
inductive TextOp where
  | ins (ts value : Nat) (anchorCoord : SidedRGA.Coord) (anchor : Nat)
      (side : SidedRGA.Side)
  | del (target : Nat)
  deriving DecidableEq, Repr

/-- `O_type`. -/
inductive AppOp where
  | text (o : TextOp)
  | recordDeletion (x : Nat)
  | recordMark (m : Mark)
  deriving DecidableEq, Repr

/-- An event: an operation with its timestamp and replica. -/
abbrev Event := Op AppOp

/-- The identity an insertion allocates, and the coordinate it lands on. -/
def TextOp.ts : TextOp → Nat
  | .ins t _ _ _ _ => t
  | .del _ => 0

/-- `c_p`: the coordinate an insertion lands on. -/
def TextOp.coord : TextOp → SidedRGA.Coord
  | .ins t _ p a s => p ++ SidedRGA.hSide s (t - a)
  | .del _ => []

/-- `Sigma = (S, D, F)`: the insertion shadow, the deletion store and the
mark store. -/
abbrev St := SidedRGA.St × Finset Nat × Finset Mark

/-- The sided row's update, on the shadow component. -/
def textStep (S : SidedRGA.St) (t : Nat) : TextOp → SidedRGA.St
  | .ins _ v p a s =>
      if t ∈ SidedRGA.ids S then S
      else SidedRGA.insertDown (t, v, p ++ SidedRGA.hSide s (t - a)) S
  | .del x => S.filter (fun z => z.1 ≠ x)

/-- `do`. Text delegates to the sided row; the two stores only grow. -/
def step (s : St) (e : Event) : St :=
  match e.op with
  | .text o => (textStep s.1 e.time o, s.2.1, s.2.2)
  | .recordDeletion x => (s.1, insert x s.2.1, s.2.2)
  | .recordMark m => (s.1, s.2.1, insert m s.2.2)

/-- `merge`. The sided merge on the shadow, union on the stores. The
evidence-store merge ignores the ancestor. -/
def mergeState (l a b : St) : St :=
  (SidedRGA.mergeState l.1 a.1 b.1, a.2.1 ∪ b.2.1, a.2.2 ∪ b.2.2)

/-! ## The document-order rich query

Every definition below reads only the retained ID/value list `Z`, the
deletion store and the mark store, which is why the specification can use
the same ones on its abstract buffer.
-/

/-- `idx(X, a)`: the first index of `a`, or `|X|` if absent. -/
def idx (X : List Nat) (a : Nat) : Nat :=
  match X.findIdx? (fun i => decide (i = a)) with
  | some i => i
  | none => X.length

/-- `b`: the retained identities, in document order. -/
def bList (Z : List (Nat × Nat)) : List Nat := Z.map Prod.fst

/-- `l`: the live identities. -/
def liveList (Z : List (Nat × Nat)) (Dl : Finset Nat) : List Nat :=
  (bList Z).filter (fun i => decide (i ∉ Dl))

/-- `cp(a)`: the value of the first pair with that identity, or `0`. -/
def cp (Z : List (Nat × Nat)) (a : Nat) : Nat :=
  match Z.find? (fun p => decide (p.1 = a)) with
  | some p => p.2
  | none => 0

/-- `R(a)`: the first live identity strictly after `a`'s position. -/
def nextLive (Z : List (Nat × Nat)) (Dl : Finset Nat) (a : Nat) : Option Nat :=
  ((bList Z).drop (idx (bList Z) a + 1)).find? (fun i => decide (i ∉ Dl))

/-- `L(a)`: the first live identity strictly before `a`'s position, scanning
the reversed prefix. An absent identity therefore scans all of `b`. -/
def prevLive (Z : List (Nat × Nat)) (Dl : Finset Nat) (a : Nat) : Option Nat :=
  ((bList Z).take (idx (bList Z) a)).reverse.find? (fun i => decide (i ∉ Dl))

/-- `T(a, s)`: resolve an endpoint anchor to a survivor. -/
def resolve (Z : List (Nat × Nat)) (Dl : Finset Nat) (a : Nat) :
    EndSide → Option Nat
  | .before => if a ∈ liveList Z Dl then some a else nextLive Z Dl a
  | .after => if a ∈ liveList Z Dl then some a else prevLive Z Dl a

/-- The initial contiguous run of identities greater than `u`. -/
def runLen (u : Nat) : List Nat → Nat
  | [] => 0
  | i :: rest => if u < i then 1 + runLen u rest else 0

/-- `r_u(j)`: that run inside `l`, starting at `j`. -/
def rRun (L : List Nat) (u j : Nat) : Nat := runLen u (L.drop j)

/-- `l_u(j)`: that run in the reverse of the prefix of length `j`. -/
def lRun (L : List Nat) (u j : Nat) : Nat := runLen u (L.take j).reverse

/-- `g_u(i) = i + 1 + r_u(i+1)`: include the anchor and grow right over the
contiguous newer-than-mark run. -/
def gFun (L : List Nat) (u i : Nat) : Nat := i + 1 + rRun L u (i + 1)

/-- `h_u(i) = i - l_u(i)`: exclude the anchor and the run to its left. -/
def hFun (L : List Nat) (u i : Nat) : Nat := i - lRun L u i

/-- `alpha_m`: the resolved start, or `none` for a missing boundary. -/
def alphaOf (L : List Nat) (m : Mark) : Option Nat → Option Nat
  | none => match m.startSide with
      | .before => none
      | .after => some 0
  | some a => match m.startSide with
      | .before => some (idx L a)
      | .after => some (gFun L m.mid (idx L a))

/-- `beta_m`: the resolved end, or `none` for a missing boundary. -/
def betaOf (L : List Nat) (m : Mark) : Option Nat → Option Nat
  | none => match m.endSide with
      | .after => none
      | .before => some L.length
  | some z => match m.endSide with
      | .after => some (gFun L m.mid (idx L z))
      | .before => some (hFun L m.mid (idx L z))

/-- A mark covers a position exactly when both boundaries exist and the
position lies between them. -/
def covers (Z : List (Nat × Nat)) (Dl : Finset Nat) (m : Mark) (j : Nat) : Bool :=
  let L := liveList Z Dl
  match alphaOf L m (resolve Z Dl m.startID m.startSide),
        betaOf L m (resolve Z Dl m.endID m.endSide) with
  | some al, some be => decide (al ≤ j ∧ j < be)
  | _, _ => false

open Classical in
/-- Among covering marks of the requested type, the one with the greatest
mid, retaining the earlier enumerated record on ties. -/
noncomputable def bestCover (Z : List (Nat × Nat)) (Dl : Finset Nat)
    (F : Finset Mark) (k : MarkType) (j : Nat) : Option Mark :=
  (F.toList.filter (fun m => decide (m.ty = k) && covers Z Dl m j)).foldl
    (fun best m =>
      match best with
      | none => some m
      | some bm => if bm.mid < m.mid then some m else some bm) none

/-- `f_k(j)`: true exactly when the selected mark has op `add`. -/
noncomputable def flagAt (Z : List (Nat × Nat)) (Dl : Finset Nat)
    (F : Finset Mark) (k : MarkType) (j : Nat) : Bool :=
  match bestCover Z Dl F k j with
  | none => false
  | some m => decide (m.op = MarkOp.add)

/-- `q_k(Z, D, F)`: the document-order rich query. -/
noncomputable def renderZ (Z : List (Nat × Nat)) (Dl : Finset Nat)
    (F : Finset Mark) (k : MarkType) : List (Nat × Bool) :=
  let L := liveList Z Dl
  (List.range L.length).map (fun j => (cp Z (L.getD j 0), flagAt Z Dl F k j))

/-! ## The tuple -/

/-- `Q_type`: the core interface asks for the shadow values or a store; the
rendered interface asks for a mark type. -/
inductive Query where
  | text
  | deletions
  | marks
  | rendered (k : MarkType)
  deriving DecidableEq, Repr

/-- `Val_type`. -/
inductive Value where
  | text (vs : List Nat)
  | ids (xs : Finset Nat)
  | marks (ms : Finset Mark)
  | rendered (out : List (Nat × Bool))
  deriving DecidableEq

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type : MRDTType where
  OType := AppOp
  decOType := inferInstance
  QType := Query
  ValType := Value

/-- `Z`: the retained ID/value list of the shadow. -/
def zOf (S : SidedRGA.St) : List (Nat × Nat) := S.map (fun z => (z.1, z.2.1))

/-- The query, over both interfaces. -/
noncomputable def view (s : St) : Query → Value
  | .text => .text (s.1.map (fun z => z.2.1))
  | .deletions => .ids s.2.1
  | .marks => .marks s.2.2
  | .rendered k => .rendered (renderZ (zOf s.1) s.2.1 s.2.2 k)

/-- `rc` is empty, as the appendix states. -/
def rcOf : AppOp → AppOp → OrderResult := fun _ _ => OrderResult.Either

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`, at an arbitrary
`rc`. `Negative.lean` needs the parameter because it refutes the laws at the
appendix's choice. -/
@[reducible] noncomputable def D (rc : AppOp → AppOp → OrderResult) : Impl type where
  Sigma := St
  decSigma := inferInstance
  sigma0 := ([], ∅, ∅)
  do_ := step
  merge := mergeState
  query := view
  rc := rc

/-- The row's own tuple, with the appendix's empty `rc`. -/
@[reducible] noncomputable def Dsp : Impl type := D rcOf

/-! ## `Spec`

The editor product. Its state is the sided editor buffer beside the same two
stores, and the rendered query is **the same** `renderZ`, applied to the
abstract buffer with the root removed. It uses no coordinates, no concrete
update and no merge.
-/

/-- `P_s(B, a, z)`: insert at the first matching anchor, on the given side.
An absent anchor leaves the list unchanged. -/
def Pside : SidedRGA.Side → List (Nat × Nat) → Nat → Nat × Nat →
    List (Nat × Nat)
  | _, [], _, _ => []
  | s, y :: Y, a, z =>
      if y.1 = a then
        match s with
        | .left => z :: y :: Y
        | .right => y :: z :: Y
      else y :: Pside s Y a z

/-- `B_0 = [(0,0)]`: identity `0` is the root sentinel. -/
def B0 : List (Nat × Nat) := [(0, 0)]

/-- `V_e(B)`: the total editor helper. -/
def editorStep (B : List (Nat × Nat)) : TextOp → List (Nat × Nat)
  | .ins t v _ a s => Pside s B a (t, v)
  | .del x => B.filter (fun p => decide (p.1 ≠ x))

/-- `q(B)`: the values, root excluded. -/
def bufferValues (B : List (Nat × Nat)) : List Nat :=
  (B.filter (fun p => decide (p.1 ≠ 0))).map Prod.snd

/-- `Z` on the abstract buffer: the root removed. -/
def bufferZ (B : List (Nat × Nat)) : List (Nat × Nat) :=
  B.filter (fun p => decide (p.1 ≠ 0))

/-- `Phi = (h, B, D, F)`. The prefix is carried solely to check `Admit`. -/
abbrev SpecState := List AppOp × List (Nat × Nat) × Finset Nat × Finset Mark

/-- `InsEvents(h)`: the insertions of the prefix. -/
def insEvents (h : List AppOp) : List TextOp :=
  h.filterMap (fun o =>
    match o with
    | .text (.ins t v p a s) => some (TextOp.ins t v p a s)
    | _ => none)

/-- `Admit`: earlier allocation, a clock above every earlier insertion, and
an anchor that is the root or an insertion already in the prefix carrying
exactly this coordinate prefix. -/
def Admit (h : List AppOp) : TextOp → Prop
  | .ins t _ p a _ =>
      (∀ q ∈ insEvents h, q.ts < t)
        ∧ ((a = 0 ∧ p = []) ∨ ∃ q ∈ insEvents h, q.ts = a ∧ q.coord = p)
  | .del x => ∃ q ∈ insEvents h, q.ts = x

/-- The specification's own query, over both interfaces. -/
noncomputable def specView (s : SpecState) : Query → Value
  | .text => .text (bufferValues s.2.1)
  | .deletions => .ids s.2.2.1
  | .marks => .marks s.2.2.2
  | .rendered k => .rendered (renderZ (bufferZ s.2.1) s.2.2.1 s.2.2.2 k)

/-- `Spec`. Queries are state-preserving transitions returning this value. -/
noncomputable def specMachine :
    HistoryMachine type.OType type.QType type.ValType where
  State := SpecState
  initial := ([], B0, ∅, ∅)
  transition s label t :=
    match label with
    | .update o =>
        match o with
        | .text o' =>
            Admit s.1 o' ∧ t = (s.1 ++ [o], editorStep s.2.1 o', s.2.2.1, s.2.2.2)
        | .recordDeletion x =>
            t = (s.1 ++ [o], s.2.1, insert x s.2.2.1, s.2.2.2)
        | .recordMark m =>
            t = (s.1 ++ [o], s.2.1, s.2.2.1, insert m s.2.2.2)
    | .query q answer => t = s ∧ answer = specView s q

/-- `Spec` as a history language. -/
noncomputable def historySpec : Soundness.Spec type := specMachine.toSpec

/-! ## Issuance -/

/-- Issuance. Logical deletion retains the insertion shadow; native text
deletion exists as a total raw effect but cannot be issued. The first
conjunct of the insertion clause is the deviation this file's header
documents. -/
noncomputable def issuance (rc : AppOp → AppOp → OrderResult) :
    Issuance (D rc).toMRDTSig where
  CanIssue := fun e s =>
    let sigma : St := s
    match e.op with
    | .text (.ins t _ p a _) =>
        t = e.time ∧ a < e.time
          ∧ ((a = 0 ∧ p = []) ∨ ∃ v', ((a, v', p) : SidedRGA.Record) ∈ sigma.1)
    | .text (.del _) => False
    | .recordDeletion x => x ∈ SidedRGA.ids sigma.1 ∧ x ∉ sigma.2.1
    | .recordMark m =>
        m.mid = e.time
          ∧ m.startID ∈ SidedRGA.ids sigma.1 ∧ m.startID ∉ sigma.2.1
          ∧ m.endID ∈ SidedRGA.ids sigma.1 ∧ m.endID ∉ sigma.2.1
          ∧ ∀ n ∈ sigma.2.2, n.mid ≠ m.mid

end LeanProofs1.Implementations.SidedPeritext
