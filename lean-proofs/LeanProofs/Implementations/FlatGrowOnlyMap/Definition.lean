import LeanProofs1.Interface.Implementation
import LeanProofs1.Soundness.SequentialSpec

/-!
# The flat grow-only map: the implementation and the specification

The two definitions the obligations are stated about, and nothing else.
`D_type = < Sigma, sigma0, do, merge, query, rc >` is the tuple of Section 3;
`historySpec` is the `Spec` of Section 4, as a language of histories.
`issuance` is the guard `G` of Section 3.

No proof appears in this file. Every obligation is in `VCs.lean`.
-/

namespace LeanProofs1.Implementations.FlatGrowOnlyMap

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

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


/-! ## `Spec` -/

/-- The specification as a deterministic machine. -/
def specMachine : DeterministicSpec (type A).OType (type A).QType (type A).ValType where
  State := Finset A
  initial := ∅
  update S o := insert o S
  query S _ := fun x => decide (x ∈ S)

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec (type A) := (specMachine A).toSpec

/-! ## Issuance -/

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance (D A).toMRDTSig where
  CanIssue := fun _ _ => True

end LeanProofs1.Implementations.FlatGrowOnlyMap
