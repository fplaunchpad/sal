import LeanProofs_no_spec_non_comm.Interface.Implementation
import LeanProofs_no_spec_non_comm.Soundness.SequentialSpec

/-!
# The grow-only set: the implementation and the specification

The two definitions the obligations are stated about, and nothing else.
`D_type = < Sigma, sigma0, do, merge, query, rc >` is the tuple of Section 3,
following Appendix `app:dt-grow-only-set`; `historySpec` is the `Spec` of
Section 4, as a language of histories. `issuance` is the guard `G` of
Section 3, which this row does not use.

* **State** a mathematical set `S`, **initial** the empty set.
* **Payload** an element `o`.
* **Update** `e(S) = S union {o}`; timestamp and replica are ignored.
* **Merge** `merge(l,a,b) = a union b`; the base `l` is ignored.
* **Query** input `()`, return the whole set `S`.
* **rc** empty.

Insertion permanently adds an element, so an element learned on either branch
survives the merge.

No proof appears in this file. Every obligation is in `VCs.lean`.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.GrowOnlySet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

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

/-! ## `Spec` -/

/-- The specification as a deterministic machine. -/
def specMachine : DeterministicSpec (type A).OType (type A).QType (type A).ValType where
  State := Set A
  initial := ∅
  update S o := insert o S
  query S _ := S

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec (type A) := (specMachine A).toSpec

/-! ## Issuance -/

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance (D A).toMRDTSig where
  CanIssue := fun _ _ => True

end LeanProofs.NoSpecNonComm.Implementations.GrowOnlySet
