import LeanProofs_no_spec_non_comm.Interface.Implementation
import LeanProofs_no_spec_non_comm.Soundness.SequentialSpec

/-!
# The counter: the implementation and the specification

The two definitions the obligations are stated about, and nothing else.
`D_type = < Sigma, sigma0, do, merge, query, rc >` is the tuple of Section 3;
`historySpec` is the `Spec` of Section 4, as a language of histories.
`issuance` is the guard `G` of Section 3, which this row does not use.

No proof appears in this file. Every obligation is in `VCs.lean`.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.FlatCounter

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.NoSpecNonComm.Interface

/-- The payload: `inc` or `dec`. -/
inductive AppOp where
  | inc
  | dec
  deriving DecidableEq, Repr

/-- `delta(inc) = 1`, `delta(dec) = -1`. -/
def delta : AppOp → Int
  | .inc => 1
  | .dec => -1

/-- `type = < O_type, Q_type, Val_type >`. -/
def type : MRDTType where
  OType := AppOp
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

/-! ## `Spec` -/

/-- The specification as a deterministic machine. -/
def specMachine : DeterministicSpec type.OType type.QType type.ValType where
  State := Int
  initial := 0
  update z o := z + delta o
  query z _ := z

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec type := specMachine.toSpec

/-! ## Issuance -/

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance D.toMRDTSig where
  CanIssue := fun _ _ => True

end LeanProofs.NoSpecNonComm.Implementations.FlatCounter
