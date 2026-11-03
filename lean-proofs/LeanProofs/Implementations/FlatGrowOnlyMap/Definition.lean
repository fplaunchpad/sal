import LeanProofs.Interface.Implementation

/-!
# The flat grow-only map: its implementation tuple

`D_type = < Sigma, sigma0, do, merge, query, rc >` for the Grow-only map row
of Table 1, following Appendix `app:dt-flat-grow-only-map`.

* **State** a Boolean function `S`, **initial** constantly false.
* **Payload** an element `o`; for the map row it is a key-value pair.
* **Update** `e(S)(x) = S(x) or (x = o)`; timestamp and replica are ignored.
* **Merge** `merge(l,a,b)(x) = l(x) or a(x) or b(x)`.
* **Query** input `()`, return the whole characteristic function `S`.
* **rc** empty.

The map is an insertion-only set of pairs, queried as a whole collection, so
several values may coexist at one key. On reachable merge inputs `l` is
contained in both branches, so the pointwise disjunction is their union; the
tuple below does not rely on that, and the obligations hold at every state.
-/

namespace LeanProofs.Implementations.FlatGrowOnlyMap

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

variable (A : Type) [DecidableEq A]

/-- `type = < O_type, Q_type, Val_type >`. For the map row `A` is a pair of
keys and values. -/
@[reducible] def type : MRDTType where
  OType := A
  decOType := inferInstance
  QType := Unit
  ValType := A → Bool

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`.

`decSigma` is classical: equality of Boolean functions is not decidable. -/
noncomputable def D : Impl (type A) where
  Sigma := A → Bool
  decSigma := fun a b => Classical.propDecidable (a = b)
  sigma0 := fun _ => false
  do_ S e := fun x => S x || decide (x = e.op)
  merge l a b := fun x => l x || a x || b x
  query S _ := S
  rc _ _ := OrderResult.Either

end LeanProofs.Implementations.FlatGrowOnlyMap
