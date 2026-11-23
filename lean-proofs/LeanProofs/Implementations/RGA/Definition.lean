import LeanProofs1.Interface.Implementation
import LeanProofs1.Soundness.SequentialSpec
import Mathlib.Data.List.Sort
import Mathlib.Data.Set.Finite.Basic

/-!
# RGA: the implementation tuple

The RGA row, following Appendix `app:dt-rga`. An insertion names its
predecessor and takes its own timestamp as identity; a deletion records an
identity permanently.

```
  o = AddAfter a       insert after the element with identity a
  o = Remove x         tombstone the element with identity x
```

The state is a pair of Boolean predicates: the insertion edges `(t, a)` and
the deleted identities. Both components are grow-only, so

```
  do((A,T), t, r, AddAfter a) = (A ∪ {(t,a)}, T)
  do((A,T), t, r, Remove x)   = (A, T ∪ {x})
  merge(l, a, b)              = l ∪ a ∪ b        componentwise
```

and **every pair of events commutes**, which is why `rc` is empty. The query
materialises the insertion tree by sorting the edges on increasing identity,
folding them into a list, and dropping the tombstoned entries.

`issuance` is the guard `G` of Section 3: identity `0` is the root and is
never issued, an insertion's anchor is either the root or an identity already
born and not deleted, and an insertion's own identity is fresh.

No proof appears in this file.
-/

namespace LeanProofs1.Implementations.RGA

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- `O_type`. An insertion carries its own identity beside its anchor.

The appendix says "insertion uses timestamp `t` as its identity". Definition 4
hands the specification the **operation**, not the event, so the identity has
to sit in the operation for the specification to allocate it. `issuance`
below closes the gap: it admits an insertion only when its identity is the
event's own timestamp, so on every certified execution this is the
appendix's tuple. -/
inductive AppOp where
  | addAfter (id anchor : Nat)
  | remove (target : Nat)
  deriving DecidableEq, Repr

/-- The identity an insertion allocates. -/
def newId : AppOp → Nat
  | .addAfter i _ => i
  | .remove _ => 0

/-- An insertion edge: the new identity, then its anchor. -/
abbrev Entry := Nat × Nat

/-- `Sigma`: the insertion edges and the tombstones, as predicates. -/
abbrev St := (Entry → Bool) × (Nat → Bool)

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type : MRDTType where
  OType := AppOp
  decOType := inferInstance
  QType := Unit
  ValType := List Nat

/-- `do`: set one bit in one component, and leave the other alone. -/
def step (s : St) (e : Op AppOp) : St :=
  match e.op with
  | .addAfter i a => (fun p => s.1 p || decide (p = (i, a)), s.2)
  | .remove x => (s.1, fun y => s.2 y || decide (y = x))

/-- `merge`: componentwise union of the base and both branches. -/
def mergeState (l a b : St) : St :=
  (fun p => l.1 p || (a.1 p || b.1 p), fun x => l.2 x || (a.2 x || b.2 x))

/-! ## The query -/

/-- Insert `value` just after `anchor`, with `0` naming the head. -/
def insertAfter (anchor value : Nat) : List Nat → List Nat
  | [] => if anchor = 0 then [value] else []
  | x :: tail =>
      if anchor = 0 then value :: x :: tail
      else if x = anchor then x :: value :: tail
      else x :: insertAfter anchor value tail

open Classical in
/-- A finite support when there is one. The fallback only totalises the
query on predicates outside the reachable states. -/
noncomputable def supportFinset {α : Type} [DecidableEq α] (f : α → Bool) : Finset α :=
  if h : Set.Finite {x | f x = true} then h.toFinset else ∅

/-- Order two edges by the identity they create. -/
def leEntry (a b : Entry) : Bool := decide (a.1 ≤ b.1)

/-- `query`: sort the edges by increasing identity, fold them into a list,
and drop the tombstoned identities. -/
noncomputable def read (s : St) : List Nat :=
  let ordered := (supportFinset s.1).toList.mergeSort leEntry
  let inserted := ordered.foldl (fun xs e => insertAfter e.2 e.1 xs) []
  inserted.filter (fun i => decide (i ∉ supportFinset s.2))

/-- `rc` is empty: the two updates are bit-sets in independent components,
so every pair of events commutes and nothing needs ordering. -/
def rcOf : AppOp → AppOp → OrderResult := fun _ _ => OrderResult.Either

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`. -/
noncomputable def D : Impl type where
  Sigma := St
  decSigma := fun _ _ => Classical.propDecidable _
  sigma0 := (fun _ => false, fun _ => false)
  do_ := step
  merge := mergeState
  query s _ := read s
  rc := rcOf


/-! ## `Spec`

The strict identified machine of the appendix. Its state is the live
identity list `B` beside the permanent allocation set `I`. An insertion is
admitted only when its identity is positive and unallocated and its anchor is
the root or live; a deletion is always admitted and is a no-op on an identity
that is not live. -/

/-- The specification's state: the visible list, and every identity ever
allocated. -/
abbrev SpecState := List Nat × Finset Nat

/-- The strict identified machine. -/
def specMachine : HistoryMachine type.OType type.QType type.ValType where
  State := SpecState
  initial := ([], ∅)
  transition s label t :=
    match label with
    | .update (.addAfter i a) =>
        0 < i ∧ i ∉ s.2 ∧ (a = 0 ∨ a ∈ s.1)
          ∧ t = (insertAfter a i s.1, insert i s.2)
    | .update (.remove x) => t = (s.1.filter (fun y => y ≠ x), s.2)
    | .query _ answer => t = s ∧ answer = s.1

/-- `Spec` as a language of histories. -/
def historySpec : Soundness.Spec type := specMachine.toSpec

/-! ## Issuance -/

/-- `born i`: some edge gives `i` an anchor. -/
def born (s : St) (i : Nat) : Prop := ∃ a, s.1 (i, a) = true

/-- Issuance: identity `0` is the root and is never issued; an insertion's
anchor is the root or an identity already born and not deleted, with a
smaller identity; and the insertion's own identity is fresh. A deletion
names something born and not already deleted. -/
def issuance : Issuance D.toMRDTSig where
  CanIssue := fun e s =>
    match e.op with
    | .addAfter i a =>
        i = e.time
          ∧ ((a = 0 ∧ 0 < i) ∨ (s.2 a = false ∧ a < i ∧ born s a))
          ∧ ¬ born s i ∧ s.2 i = false
    | .remove x => born s x ∧ s.2 x = false

end LeanProofs1.Implementations.RGA
