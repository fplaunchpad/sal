import LeanProofs.Interface.Implementation

/-!
# The grow-only set: its implementation tuple

`D_type = < Sigma, sigma0, do, merge, query, rc >` for the Grow-only set row
of Table 1, following Appendix `app:dt-grow-only-set`.

* **State** a mathematical set `S`, **initial** the empty set.
* **Payload** an element `o`.
* **Update** `e(S) = S union {o}`; timestamp and replica are ignored.
* **Merge** `merge(l,a,b) = a union b`; the base `l` is ignored.
* **Query** input `()`, return the whole set `S`.
* **rc** empty.

Insertion permanently adds an element, so an element learned on either branch
survives the merge. The appendix also lists an enumerable `Finset` carrier and
a Boolean carrier; this is the mathematical one.
-/

namespace LeanProofs.Implementations.GrowOnlySet

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

variable (A : Type) [DecidableEq A]

/-- `type = < O_type, Q_type, Val_type >`. The payload is an element.

Reducible so that `(type A).OType` unfolds to `A` during instance search. -/
@[reducible] def type : MRDTType where
  OType := A
  decOType := inferInstance
  QType := Unit
  ValType := Set A

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`.

`decSigma` is classical: equality of mathematical sets is not decidable, and
it is bookkeeping rather than part of the paper's tuple. -/
noncomputable def D : Impl (type A) where
  Sigma := Set A
  decSigma := fun a b => Classical.propDecidable (a = b)
  sigma0 := ∅
  do_ S e := insert e.op S
  merge _ a b := a ∪ b
  query S _ := S
  rc _ _ := OrderResult.Either

end LeanProofs.Implementations.GrowOnlySet
