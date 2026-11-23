import LeanProofs.Implementations.FiniteGrowOnlySet.SequentialSpec
import LeanProofs.Soundness.RALinearizability

/-!
# The enumerable grow-only set: Definition 4

The two clauses combined.
-/

namespace LeanProofs.Implementations.FiniteGrowOnlySet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable (A : Type) [DecidableEq A]
variable {A}

/-- **RA-linearizability.** -/
theorem raLinearizable :
    Soundness.CertifiedRA (D A) (historySpec A) (issuance A) :=
  Soundness.certifiedRA obligations specSound


end LeanProofs.Implementations.FiniteGrowOnlySet
