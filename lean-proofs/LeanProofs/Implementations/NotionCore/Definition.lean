import LeanProofs1.Interface.Implementation
import LeanProofs1.Soundness.SequentialSpec
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.List.Sort

/-!
# Notion core: the implementation and the specification

The Notion core row of Table 1, following Appendix `app:dt-notion-core`.
A text instance is an RGA-like parent graph; a displayed block presents
slices of text instances. Splitting a block inserts a hidden marker and
gives the new block the following interval of the same source instance.

```
  Sigma = Finset Fact,   F0 = empty
  do(F, t, r, (k, p)) = F union Delta(k, p)
  merge(l, a, b)      = a union b
```

The carrier is a grow-only set of **immutable facts**: births, erasures,
block creations and cut assignments. All facts of one transaction enter
atomically, receipt is idempotent, and the ancestor argument of `merge` is
ignored. That is why `rc` is empty here without qualification, exactly as
for AegisSheet, even though the independent document commands do not
commute.

The query reconstructs the displayed document from the facts alone: it
rebuilds each instance's physical list by a fuel-bounded traversal of the
parent graph, cuts that list at the recorded boundaries, orders the blocks
by their creation links, and reads off the live text.

No proof appears in this file. Every obligation is in `VCs.lean`.
-/

namespace LeanProofs1.Implementations.NotionCore

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-! ## Identities, rows and facts -/

/-- A source ID `k = (c, u)`: a counter and a UTF-16 session unit list.
Distinct from the event timestamp and replica. -/
abbrev Id := Nat × List Nat

/-- Lexicographic order on session unit lists. -/
def lexLeList : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x < y then true else if y < x then false else lexLeList xs ys

/-- Source IDs are ordered by counter, then lexicographically. -/
def idLe (a b : Id) : Bool :=
  if a.1 < b.1 then true else if b.1 < a.1 then false else lexLeList a.2 b.2

/-- `K = {initial} + {issued(k)}`: block and instance keys. -/
inductive Key where
  | initial
  | issued (k : Id)
  deriving DecidableEq

/-- `Origin = {start} + {item(k)}`. -/
inductive Origin where
  | start
  | item (k : Id)
  deriving DecidableEq

/-- An item kind: a character with its deletion bit, or a hidden split
marker. -/
inductive ItemKind where
  | text (v : Nat) (d : Bool)
  | split
  deriving DecidableEq

/-- A row records an item ID, its kind and its origin. -/
abbrev Row := Id × ItemKind × Origin

/-- The four fact constructors, as a tagged union. -/
inductive Fact where
  | birth (i : Key) (rho : Row)
  | erased (i : Key) (k : Id)
  | created (b : Key) (a : Option Key)
  | cut (i : Key) (k : Id) (b : Key)
  deriving DecidableEq

/-- `Sigma = Finset(Fact)`. -/
abbrev St := Finset Fact

/-! ## Transactions and the exact atomic decode -/

/-- A transaction payload. -/
inductive Payload where
  | bootstrap (x : List Nat)
  | create (a : Option Key)
  | insert (b i : Key) (o : Origin) (x : List Nat)
  | erase (b i : Key) (X : List Id)
  | split (b i : Key) (o : Origin)
  deriving DecidableEq

/-- `O_type`: the transaction `tau = (k, p)`. -/
structure AppOp where
  id : Id
  payload : Payload
  deriving DecidableEq

/-- An event: a transaction with its timestamp and replica. -/
abbrev Event := Op AppOp

/-- `B(i, k, o, x)`: the text-run births. The `j`-th character takes ID
`(c+j, u)` and origin `item(k_{j-1})`, with the supplied origin for
`j = 0`. -/
def textBirths (i : Key) (k : Id) (o : Origin) (x : List Nat) : Finset Fact :=
  ((List.range x.length).map (fun j =>
      Fact.birth i ((k.1 + j, k.2), .text (x.getD j 0) false,
        if j = 0 then o else .item (k.1 + j - 1, k.2)))).toFinset

/-- `Delta(k, p)`: the decoded fact set. All facts of one transaction enter
together. -/
def delta (k : Id) : Payload → Finset Fact
  | .bootstrap x =>
      textBirths .initial k .start x ∪ {Fact.created .initial none}
  | .create a => {Fact.created (.issued k) a}
  | .insert _ i o x => textBirths i k o x
  | .erase _ i X => (X.map (fun j => Fact.erased i j)).toFinset
  | .split b i o =>
      {Fact.birth i (k, .split, o), Fact.created (.issued k) (some b),
       Fact.cut i k (.issued k)}

/-! ## Names and addresses

The appendix fixes injective names `beta` on keys with `beta(initial) = 0`
and `nu` on session lists, together with partial inverses that fail outside
their images. They are parameters of the tuple, not derived from it, and
they need not preserve source-ID order.
-/

/-- The naming maps and their partial inverses. -/
structure Names where
  beta : Key → Nat
  betaInv : Nat → Option Key
  nu : List Nat → Nat

/-- The tail of a semantic address. -/
inductive AddrTail where
  | start
  | event (s c : Nat)
  deriving DecidableEq

/-- A semantic address: an instance name and a tail. -/
abbrev Addr := Nat × AddrTail

variable (nm : Names)

/-- `a(i, (c,u)) = (beta(i), event(nu(u), c))`. -/
def addrItem (i : Key) (k : Id) : Addr := (nm.beta i, .event (nm.nu k.2) k.1)

/-- `a(i, start) = (beta(i), start)` and `a(i, item(k))` as above. -/
def addrOrigin (i : Key) : Origin → Addr
  | .start => (nm.beta i, .start)
  | .item k => addrItem nm i k

/-! ## Rows, the physical list, and cuts -/

/-- `T_i`: the birth rows of instance `i`, with a text row's deletion bit
raised to `d or [erased(i,k) in F]`. A split row is unchanged. -/
noncomputable def instanceRows (F : St) (i : Key) : List Row :=
  F.toList.filterMap (fun f =>
    match f with
    | .birth i' rho =>
        if i' = i then
          some (match rho with
            | (k, .text v d, o) => (k, .text v (d || (Fact.erased i k ∈ F)), o)
            | (k, .split, o) => (k, .split, o))
        else none
    | _ => none)

/-- `row_i(k)`: the first row with identity `k`, or absent. -/
noncomputable def rowAt (F : St) (i : Key) (k : Id) : Option Row :=
  (instanceRows F i).find? (fun rho => rho.1 = k)

/-- `children_i(o)`: the row identities whose origin is `o`, sorted in
descending source-ID order. -/
noncomputable def children (F : St) (i : Key) (o : Origin) : List Id :=
  (((instanceRows F i).filter (fun rho => rho.2.2 = o)).map (fun rho => rho.1)).mergeSort
    (le := fun a b => idLe b a)

/-- `V_i(n, o)`: the fuel-bounded traversal. Each visited item carries its
address. The fuel is sufficient on honest closed rows; it also defines the
raw query on malformed cycles. -/
noncomputable def trav (F : St) (i : Key) : Nat → Origin → List (Addr × ItemKind)
  | 0, _ => []
  | n + 1, o =>
      (children F i o).flatMap (fun k =>
        match rowAt F i k with
        | some rho => (addrItem nm i k, rho.2.1) :: trav F i n (.item k)
        | none => [])

/-- `P_i(F)`: a virtual split atom at `(beta(i), start)`, then the
traversal. -/
noncomputable def physical (F : St) (i : Key) : List (Addr × ItemKind) :=
  ((nm.beta i, AddrTail.start), ItemKind.split)
    :: trav nm F i (instanceRows F i).length .start

/-- `C(F)`: the owner/start records, from creations and from cuts. -/
noncomputable def records (F : St) : List (Nat × Addr) :=
  F.toList.filterMap (fun f =>
    match f with
    | .created b _ => some (nm.beta b, (nm.beta b, AddrTail.start))
    | .cut i k b => some (nm.beta b, addrItem nm i k)
    | _ => none)

/-- The boundary records of one instance, in physical order: at each atom,
the first record whose start equals that atom's address and whose start
instance is `beta(i)`. -/
noncomputable def boundaries (F : St) (i : Key) : List (Nat × Addr) :=
  (physical nm F i).filterMap (fun at_ =>
    (records nm F).find? (fun r => r.2 = at_.1 ∧ r.2.1 = nm.beta i))

/-- The atoms strictly after the first occurrence of an address. A missing
start gives an empty list. -/
def afterFirst (P : List (Addr × ItemKind)) (a : Addr) : List (Addr × ItemKind) :=
  match P with
  | [] => []
  | p :: rest => if p.1 = a then rest else afterFirst rest a

/-- The atoms up to the first occurrence of an address. A missing endpoint
retains the remainder. -/
def upToFirst (P : List (Addr × ItemKind)) (a : Addr) : List (Addr × ItemKind) :=
  match P with
  | [] => []
  | p :: rest => if p.1 = a then [] else p :: upToFirst rest a

/-- The interval of the boundary at index `j`: strictly after its own start,
up to the next boundary's start, or to the end of the physical list. The
interval contains every intervening atom, including tombstones. -/
noncomputable def intervalAt (F : St) (i : Key) (j : Nat) : List (Addr × ItemKind) :=
  let bs := boundaries nm F i
  let tail := afterFirst (physical nm F i) ((bs.getD j (0, (0, .start))).2)
  match bs[j + 1]? with
  | some nxt => upToFirst tail (Prod.snd nxt)
  | none => tail

/-- The live text values of an interval. -/
def liveText (L : List (Addr × ItemKind)) : List Nat :=
  L.filterMap (fun at_ =>
    match at_.2 with
    | .text v false => some v
    | _ => none)

/-- `blockText(F, b)`: select the first record owned by `b` whose start
instance differs from `b`, else the first record owned by `b`; decode its
start instance to a block key; find its interval by the selected start
address. Any failure is `none`. -/
noncomputable def blockText (F : St) (b : Nat) : Option (List Nat) :=
  let owned := (records nm F).filter (fun r => r.1 = b)
  match (owned.find? (fun r => r.2.1 ≠ b)).orElse (fun _ => owned.head?) with
  | none => none
  | some r =>
      match nm.betaInv r.2.1 with
      | none => none
      | some i =>
          match (boundaries nm F i).findIdx? (fun c => c.2 = r.2) with
          | none => none
          | some j => some (liveText (intervalAt nm F i j))

/-! ## Block order -/

/-- The creator key: `(1, [65])` for `initial`, and `k` for `issued(k)`. -/
def creatorKey : Key → Id
  | .initial => (1, [65])
  | .issued k => k

/-- `Lambda(F)`, stably sorted by increasing creator key. -/
noncomputable def creations (F : St) : List (Key × Option Key) :=
  (F.toList.filterMap (fun f =>
    match f with
    | .created b a => some (b, a)
    | _ => none)).mergeSort (le := fun p q => idLe (creatorKey p.1) (creatorKey q.1))

/-- Insert `v` immediately after the first occurrence of `w`. -/
def insertAfterFirst (w v : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => if x = w then x :: v :: xs else x :: insertAfterFirst w v xs

/-- `Ord(F)`: fold the sorted creation links. A block already present is
left alone; otherwise it goes after its present predecessor, and at the
front when there is none or it is absent. This fold reads creation links
rather than replaying transactions. -/
noncomputable def blockOrder (F : St) : List Nat :=
  (creations F).foldl (fun ord p =>
    if nm.beta p.1 ∈ ord then ord
    else match p.2 with
      | none => nm.beta p.1 :: ord
      | some a =>
          if nm.beta a ∈ ord then insertAfterFirst (nm.beta a) (nm.beta p.1) ord
          else nm.beta p.1 :: ord) []

/-- `query(F)`: the document, or `none` if any block read fails. -/
noncomputable def view (F : St) : Option (List (Nat × List Nat)) :=
  (blockOrder nm F).mapM (fun b => (blockText nm F b).map (fun x => (b, x)))

/-! ## The tuple -/

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type : MRDTType where
  OType := AppOp
  decOType := inferInstance
  QType := Unit
  ValType := Option (List (Nat × List Nat))

/-- `rc` is empty. Receipt is a set union, so every pair of events commutes
at every state. -/
def rcOf : AppOp → AppOp → OrderResult := fun _ _ => OrderResult.Either

/-- `do(F, t, r, (k, p))`: the decoded facts enter atomically. -/
noncomputable def step (F : St) (e : Event) : St := F ∪ delta e.op.id e.op.payload

/-- `merge(l, a, b)`: the ancestor argument is ignored. -/
def mergeState (_l a b : St) : St := a ∪ b

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`.

Reducible so that `(D nm).Sigma` unfolds to `St` during instance search. -/
@[reducible] noncomputable def D : Impl type where
  Sigma := St
  decSigma := inferInstance
  sigma0 := ∅
  do_ := step
  merge := mergeState
  query F _ := view nm F
  rc := rcOf

/-! ## `Spec`

The ordered block list of the appendix. Its state is a list of blocks, each
a list of retained slots, and its commands are the ordinary document edits:
create a block, insert slots after an address, hide named characters, and
split a block at an address.

Every rule is **deterministic on every ordered block list**, including lists
with repeated IDs or addresses, so each is given here as a partial function
rather than a relation. A command that admits no transition returns `none`.

One update of the machine is an **atomic group** of commands, prepared at
issuance by `commands` and admitted only when every command in the group
succeeds. Histories start at `D0` and may query only between complete
groups. This machine has no transaction archive and no sorting rule.
-/

/-- A retained slot: an address, a text atom, and a visibility bit. -/
abbrev Slot := Addr × Nat × Bool

/-- `Phi`: an ordered block list. -/
abbrev Doc := List (Nat × List Slot)

/-- `root(j)`. -/
def root (j : Nat) : Slot := ((j, AddrTail.start), 0, false)

/-- `text(L)`: the visible values, in list order. -/
def slotText (L : List Slot) : List Nat :=
  L.filterMap (fun z => if z.2.2 then some z.2.1 else none)

/-- `view(D)`. -/
def docView (Dd : Doc) : List (Nat × List Nat) :=
  Dd.map (fun C => (C.1, slotText C.2))

/-- `blocks(D)`. -/
def blocks (Dd : Doc) : List Nat := Dd.map Prod.fst

/-- `owns((b,L), a)`. -/
def owns (C : Nat × List Slot) (a : Addr) : Bool :=
  C.2.any (fun z => z.1 = a)

/-- `owner(D, a)`: the first owning block. -/
def owner (Dd : Doc) (a : Addr) : Option (Nat × List Slot) :=
  Dd.find? (fun C => owns C a)

/-- `cut(L, a)`: cut immediately after the first occurrence of `a`, or
`(L, [])` when it is absent. -/
def cutAfter (L : List Slot) (a : Addr) : List Slot × List Slot :=
  match L.findIdx? (fun z => z.1 = a) with
  | some i => (L.take (i + 1), L.drop (i + 1))
  | none => (L, [])

/-- `hide_X`. -/
def hideSlot (X : List Addr) (z : Slot) : Slot :=
  if z.1 ∈ X then (z.1, z.2.1, false) else z

/-- The four commands. -/
inductive Cmd where
  | create (b j : Nat) (a : Option Nat)
  | insert (a : Addr) (F : List Slot)
  | delete (X : List Addr)
  | split (a : Addr) (m : Slot) (d : Nat)

/-- One command, as a partial function. `none` is "admits no transition". -/
def cmdStep (Dd : Doc) : Cmd → Option Doc
  | .create b j none =>
      if b ∈ blocks Dd then none else some ((b, [root j]) :: Dd)
  | .create b j (some a) =>
      if b ∈ blocks Dd ∨ a ∉ blocks Dd then none
      else some (Dd.flatMap (fun C => if C.1 = a then [C, (b, [root j])] else [C]))
  | .insert a F =>
      match owner Dd a with
      | none => none
      | some _ =>
          some (Dd.map (fun C =>
            if owns C a then
              let r := cutAfter C.2 a
              (C.1, r.1 ++ F ++ r.2)
            else C))
  | .delete X => some (Dd.map (fun C => (C.1, C.2.map (hideSlot X))))
  | .split a m d =>
      match owner Dd a with
      | none => none
      | some C =>
          if C.1 = d ∨ d ∉ blocks Dd ∨ m.2.2 then none
          else
            let r := cutAfter C.2 a
            some (Dd.map (fun B =>
              if B.1 = C.1 then (B.1, r.1)
              else if B.1 = d then (B.1, B.2 ++ [m] ++ r.2)
              else B))

/-- A whole atomic group: admitted when every command succeeds. -/
def runGroup (Dd : Doc) : List Cmd → Option Doc
  | [] => some Dd
  | c :: cs =>
      match cmdStep Dd c with
      | none => none
      | some Dd' => runGroup Dd' cs

/-- `slots(i, k, x)`: the live slots of a text run. -/
def slotsOf (i : Key) (k : Id) (x : List Nat) : List Slot :=
  (List.range x.length).map (fun j =>
    (addrItem nm i (k.1 + j, k.2), x.getD j 0, true))

/-- `commands(k, p)`: the atomic group prepared at issuance. These
arguments are fixed without calling the concrete renderer. -/
def commands (k : Id) : Payload → List Cmd
  | .bootstrap x =>
      [.create 0 0 none,
       .insert (0, AddrTail.start) (slotsOf nm .initial k x)]
  | .create a =>
      [.create (nm.beta (.issued k)) (nm.beta (.issued k)) (a.map nm.beta)]
  | .insert _ i o x => [.insert (addrOrigin nm i o) (slotsOf nm i k x)]
  | .erase _ i X => [.delete (X.map (fun j => addrItem nm i j))]
  | .split b i o =>
      [.create (nm.beta (.issued k)) (nm.beta (.issued k)) (some (nm.beta b)),
       .split (addrOrigin nm i o) (addrItem nm i k, 0, false)
         (nm.beta (.issued k))]

/-- The independent sequential specification. There is no query transition
returning `none`. -/
def specMachine : HistoryMachine type.OType type.QType type.ValType where
  State := Doc
  initial := []
  transition s label t :=
    match label with
    | .update o => runGroup s (commands nm o.id o.payload) = some t
    | .query _ answer => t = s ∧ answer = some (docView s)

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec type := (specMachine nm).toSpec

/-! ## Issuance -/

/-- Issuance: the transaction's source ID is fresh, both as a row identity
and as a block key.

The appendix's guard is stronger: it reconstructs a reference state
`M = (I, H, O)` and checks the request against it. That reconstruction is
not ported here. A weaker guard certifies more executions, so what is stated
here is the conservative direction, and nothing below depends on the
difference. -/
def issuance : Issuance (D nm).toMRDTSig where
  CanIssue := fun e F =>
    let s : St := F
    (∀ g ∈ s, ∀ i rho, g = .birth i rho → rho.1 ≠ e.op.id)
      ∧ (∀ g ∈ s, ∀ a, g ≠ .created (.issued e.op.id) a)

end LeanProofs1.Implementations.NotionCore
