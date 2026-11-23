import LeanProofs.Implementations.FlatCounter.SequentialSpec
import LeanProofs.Soundness.RALinearizability

/-!
# The counter: Definition 4

The two clauses combined.
-/

namespace LeanProofs.Implementations.FlatCounter

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1 LeanProofs.Interface

/-- **RA-linearizability.** Every certified execution of the counter
satisfies Definition 4 against `Spec`. -/
theorem raLinearizable : Soundness.CertifiedRA D historySpec issuance :=
  Soundness.certifiedRA obligations specSound


end LeanProofs.Implementations.FlatCounter
