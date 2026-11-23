import LeanProofs1.Interface.Implementation
import LeanProofs1.Soundness.SequentialSpec
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic

/-!
# The finite grow-only set: the implementation and the specification

The two definitions the obligations are stated about, and nothing else.
`D_type = < Sigma, sigma0, do, merge, query, rc >` is the tuple of Section 3;
`historySpec` is the `Spec` of Section 4, as a language of histories.
`issuance` is the guard `G` of Section 3.

No proof appears in this file. Every obligation is in `VCs.lean`.
-/

namespace LeanProofs1.Implementations.FiniteGrowOnlySet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

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


/-! ## `Spec` -/

/-- The specification as a deterministic machine. -/
def specMachine : DeterministicSpec (type A).OType (type A).QType (type A).ValType where
  State := Finset A
  initial := ∅
  update S o := insert o S
  query S _ := S

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec (type A) := (specMachine A).toSpec

/-! ## Issuance -/

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance (D A).toMRDTSig where
  CanIssue := fun _ _ => True

end LeanProofs1.Implementations.FiniteGrowOnlySet
