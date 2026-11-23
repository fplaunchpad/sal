import LeanProofs.Interface.Implementation
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic

/-!
# The enumerable grow-only set: its implementation tuple

The enumerable carrier of the Grow-only set row, Appendix
`app:dt-grow-only-set`: "the enumerable carrier uses `Finset(A)` so clients
can enumerate elements". Peritext uses this representation for rendering.

Same abstraction as `GrowOnlySet`, different carrier. Unlike the mathematical
and Boolean carriers this one is **computable**: `Finset` has decidable
equality, so `decSigma` needs no appeal to choice.
-/

namespace LeanProofs.Implementations.FiniteGrowOnlySet

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

variable (A : Type) [DecidableEq A]

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type : MRDTType where
  OType := A
  decOType := inferInstance
  QType := Unit
  ValType := Finset A

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`. -/
def D : Impl (type A) where
  Sigma := Finset A
  decSigma := inferInstance
  sigma0 := ∅
  do_ S e := insert e.op S
  merge _ a b := a ∪ b
  query S _ := S
  rc _ _ := OrderResult.Either

end LeanProofs.Implementations.FiniteGrowOnlySet
