import LeanProofs.Interface.Implementation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Image

/-!
# The efficient OR-set: its implementation tuple

The Efficient OR-set row of Table 1, Appendix `app:dt-efficient-or-set`.

This row is **defined but not certified here**. `Obstruction.lean` records
why, with a machine-checked proof rather than a remark.

The difference from the exact OR-set is one clause: an `add` also drops the
issuer's own earlier record for the same element, so the state holds at most
one record per replica and element. That is what makes it efficient, and it
is also what puts it outside this development's interface.
-/

namespace LeanProofs.Implementations.EfficientORSet

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

/-- `O_type`: add and remove an element. -/
inductive Act (A : Type) where
  | add (x : A)
  | remove (x : A)
  deriving DecidableEq, Repr

variable (A : Type) [DecidableEq A]

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type : MRDTType where
  OType := Act A
  decOType := inferInstance
  QType := A
  ValType := Bool

/-- `Sigma`: at most one record per replica and element. -/
abbrev St (A : Type) := Finset (Replica × Timestamp × A)

variable {A}

/-- `do(sigma, t, r, o)`. The `filter` in the `add` branch is the efficient
encoding: the issuer replaces its own earlier record instead of adding a
second one. -/
def step (S : St A) (e : Op (Act A)) : St A :=
  match e.op with
  | .add x => insert (e.rep, e.time, x) (S.filter (fun p => ¬ (p.1 = e.rep ∧ p.2.2 = x)))
  | .remove x => S.filter (fun p => p.2.2 ≠ x)

/-- `merge(l,a,b)`, the same three-way shape as the exact OR-set. -/
def mergeState (l a b : St A) : St A := (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

/-- The elements the client sees. -/
def elements (S : St A) : Finset A := S.image (fun p => p.2.2)

/-- `rc`: `remove x` before `add x`, as for the exact OR-set. -/
def rc : Act A → Act A → OrderResult
  | .remove x, .add y => if x = y then OrderResult.Fst_then_snd else OrderResult.Either
  | .add x, .remove y => if x = y then OrderResult.Snd_then_fst else OrderResult.Either
  | _, _ => OrderResult.Either

variable (A)

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`. -/
@[reducible] def D : Impl (type A) where
  Sigma := St A
  decSigma := inferInstance
  sigma0 := ∅
  do_ := step
  merge := mergeState
  query S x := decide (x ∈ elements S)
  rc := rc

end LeanProofs.Implementations.EfficientORSet
