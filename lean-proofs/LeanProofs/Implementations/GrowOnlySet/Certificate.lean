import LeanProofs.Implementations.GrowOnlySet.SequentialSpec
import LeanProofs.Soundness.RALinearizability

/-!
# The grow-only set: Definition 4

The two clauses combined.
-/

namespace LeanProofs.Implementations.GrowOnlySet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1 LeanProofs.Interface

variable (A : Type) [DecidableEq A]
variable {A}

/-- **RA-linearizability.** Every certified execution of the grow-only set
satisfies Definition 4 against `Spec`. -/
theorem raLinearizable :
    Soundness.CertifiedRA (D A) (historySpec A) (issuance A) :=
  Soundness.certifiedRA obligations specSound

#print axioms raLinearizable

end LeanProofs.Implementations.GrowOnlySet
