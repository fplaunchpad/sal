import LeanProofs.Implementations.FlatGrowOnlyMap.SequentialSpec
import LeanProofs.Soundness.RALinearizability

/-!
# The flat grow-only map: Definition 4

The two clauses combined.
-/

namespace LeanProofs.Implementations.FlatGrowOnlyMap

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {A : Type} [DecidableEq A]

/-- **RA-linearizability.** Every certified execution of the flat grow-only
map satisfies Definition 4 against `Spec`. -/
theorem raLinearizable :
    Soundness.CertifiedRA (D A) (historySpec A) (issuance A) :=
  Soundness.certifiedRA obligations specSound

#print axioms raLinearizable

end LeanProofs.Implementations.FlatGrowOnlyMap
