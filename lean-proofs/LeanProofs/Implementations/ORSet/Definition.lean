import LeanProofs.Interface.Implementation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Image

/-!
# The OR-set: its implementation tuple

The OR-set row of Table 1, Appendix `app:dt-or-set`. This is the exact
observed-remove set of Section 2, Fig. 1, not the efficient encoding.

Every add is retained as an element/timestamp pair, so two adds of the same
element are distinct records. A remove erases every pair for its element,
which is why it does not commute with a concurrent add of that element.

This is the first row here whose `rc` is nonempty. `remove x` is ordered
before `add x`; every other pair is left unordered, as RC-NON-COMM requires.
-/

namespace LeanProofs.Implementations.ORSet

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

/-- `O_type`: add and remove an element. -/
inductive Act (A : Type) where
  | add (x : A)
  | remove (x : A)
  deriving DecidableEq, Repr

variable (A : Type) [DecidableEq A]

/-- `type = < O_type, Q_type, Val_type >`. The query asks whether an element
is in the set. -/
@[reducible] def type : MRDTType where
  OType := Act A
  decOType := inferInstance
  QType := A
  ValType := Bool

/-- `Sigma`: the add records, each an element tagged by the timestamp of the
event that added it. -/
abbrev St (A : Type) := Finset (A × Timestamp)

variable {A}

/-- `do(sigma, t, r, o)`. An add inserts its own record; a remove erases every
record for its element, whatever added it. -/
def step (S : St A) (e : Op (Act A)) : St A :=
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
def rc : Act A → Act A → OrderResult
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

end LeanProofs.Implementations.ORSet
