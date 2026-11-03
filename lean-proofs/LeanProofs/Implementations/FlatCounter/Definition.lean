import LeanProofs.Interface.Implementation

/-!
# The counter: its implementation tuple

`D_type = < Sigma, sigma0, do, merge, query, rc >` for the Counter row of
Table 1, following Appendix `app:dt-counter`.

* **State** integer `z`, **initial** `0`.
* **Payload** `inc` or `dec`, with `delta(inc) = 1` and `delta(dec) = -1`.
* **Update** `e(z) = z + delta(o)`; timestamp and replica are ignored.
* **Merge** `merge(l,a,b) = a + b - l`.
* **Query** input `()`, return `z`.
* **rc** empty.

The integer-delta three-way counter uses ancestor subtraction; it is not a
saturating natural-number counter.
-/

namespace LeanProofs.Implementations.FlatCounter

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

/-- The payload: `inc` or `dec`. -/
inductive CounterOp where
  | inc
  | dec
  deriving DecidableEq, Repr

/-- `delta(inc) = 1`, `delta(dec) = -1`. -/
def delta : CounterOp → Int
  | .inc => 1
  | .dec => -1

/-- `type = < O_type, Q_type, Val_type >`. -/
def type : MRDTType where
  OType := CounterOp
  decOType := inferInstance
  QType := Unit
  ValType := Int

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`. -/
def D : Impl type where
  Sigma := Int
  decSigma := inferInstance
  sigma0 := 0
  do_ z e := z + delta e.op
  merge l a b := a + b - l
  query z _ := z
  rc _ _ := OrderResult.Either

end LeanProofs.Implementations.FlatCounter
