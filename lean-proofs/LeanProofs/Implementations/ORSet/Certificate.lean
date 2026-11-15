import LeanProofs.Implementations.ORSet.SequentialSpec
import LeanProofs.Soundness.RALinearizability

/-!
# The OR-set: Definition 4

The two clauses combined.
-/

namespace LeanProofs.Implementations.ORSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {A : Type} [DecidableEq A]

/-- **RA-linearizability.** Every certified execution of the OR-set satisfies
Definition 4 against `Spec`, at the implementation's own nonempty `rc`. -/
theorem raLinearizable :
    Soundness.CertifiedRA (D A) (historySpec A) (issuance A) :=
  Soundness.certifiedRA_direct directObligations specSound

#print axioms joinLemma
#print axioms raLinearizable

end LeanProofs.Implementations.ORSet
