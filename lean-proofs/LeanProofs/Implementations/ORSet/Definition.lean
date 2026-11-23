import LeanProofs1.Interface.Implementation
import LeanProofs1.Soundness.SequentialSpec
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Image

/-!
# The OR-set: the implementation and the specification

The two definitions the obligations are stated about, and nothing else.
`D_type = < Sigma, sigma0, do, merge, query, rc >` is the tuple of Section 3,
with `rc` nonempty; `historySpec` is the `Spec` of Section 4, an ordinary
set with no timestamps anywhere; `issuance` is the guard `G`, which this row
does not use.

No proof appears in this file. Every obligation is in `VCs.lean`.
-/

namespace LeanProofs1.Implementations.ORSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs1.Interface

/-- `O_type`: add and remove an element. -/
inductive AppOp (A : Type) where
  | add (x : A)
  | remove (x : A)
  deriving DecidableEq, Repr

/-- An event: an operation with its timestamp and replica. -/
abbrev Event (A : Type) := Op (AppOp A)

variable (A : Type) [DecidableEq A]

/-- `type = < O_type, Q_type, Val_type >`. The query asks whether an element
is in the set. -/
@[reducible] def type : MRDTType where
  OType := AppOp A
  decOType := inferInstance
  QType := A
  ValType := Bool

/-- `Sigma`: the add records, each an element tagged by the timestamp of the
event that added it. -/
abbrev St (A : Type) := Finset (A × Timestamp)

variable {A}

/-- `do(sigma, t, r, o)`. An add inserts its own record; a remove erases every
record for its element, whatever added it. -/
def step (S : St A) (e : Event A) : St A :=
  match e.op with
  | .add x => insert (x, e.time) S
  | .remove x => S.filter (fun p => p.1 ≠ x)

/-- `merge(l,a,b)`. A record survives when it is in both branches, or when it
is new in one of them. The LCA state is a genuine input: it is what tells a
removal apart from an addition that has not yet propagated. -/
def mergeState (l a b : St A) : St A := (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

/-- The elements the client sees, with the timestamps erased. -/
def view (S : St A) : Finset A := S.image Prod.fst

/-- `rc`: `remove x` is ordered before `add x`. Nothing else is ordered. -/
def rc : AppOp A → AppOp A → OrderResult
  | .remove x, .add y => if x = y then OrderResult.Fst_then_snd else OrderResult.Either
  | .add x, .remove y => if x = y then OrderResult.Snd_then_fst else OrderResult.Either
  | _, _ => OrderResult.Either

variable (A)

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`.

Reducible so that `(D A).Sigma` unfolds to `St A` during instance search. -/
@[reducible] def D : Impl (type A) where
  Sigma := St A
  decSigma := inferInstance
  sigma0 := ∅
  do_ := step
  merge := mergeState
  query S x := decide (x ∈ view S)
  rc := rc

/-! ## `Spec` -/

/-- `Spec`: an ordinary set, with no timestamps anywhere. `add` inserts,
`remove` erases, and the query reports membership. -/
def specMachine : DeterministicSpec (type A).OType (type A).QType (type A).ValType where
  State := Finset A
  initial := ∅
  update S o := match o with
    | .add x => insert x S
    | .remove x => S.erase x
  query S x := decide (x ∈ S)

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec (type A) := (specMachine A).toSpec

variable {A}

/-! ## Issuance -/

variable (A)

/-- Issuance: `G(e, O) <=> true`. The exact OR-set needs no payload and no
side condition on the events a replica may mint. -/
def issuance : Issuance (D A).toMRDTSig where
  CanIssue := fun _ _ => True

variable {A}

end LeanProofs1.Implementations.ORSet
