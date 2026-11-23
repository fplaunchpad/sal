import LeanProofs.Implementations.RemoveWinsSet.SequentialSpec
import LeanProofs.Soundness.RALinearizability

/-!
# The remove-wins set: Definition 4

The two clauses combined.
-/

namespace LeanProofs.Implementations.RemoveWinsSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {A : Type} [DecidableEq A] [Fintype A]

/-- **RA-linearizability.** Every certified execution of the remove-wins set
satisfies Definition 4 against `Spec`, at its own nonempty `rc` and under its
issuance guard. -/
theorem raLinearizable :
    Soundness.CertifiedRA (D A) (historySpec A) (issuance A) :=
  Soundness.certifiedRA_on obligations positive_of_mintHonest specSound

end LeanProofs.Implementations.RemoveWinsSet
