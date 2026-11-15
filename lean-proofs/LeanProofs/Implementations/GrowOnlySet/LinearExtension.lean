import LeanProofs.Implementations.GrowOnlySet.Laws
import LeanProofs.Soundness.LinearExtension

/-!
# The grow-only set: clause 1

Issuance, and the join lemma obtained from the obligations.
-/

namespace LeanProofs.Implementations.GrowOnlySet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1 LeanProofs.Interface

variable (A : Type) [DecidableEq A]

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance (D A).toMRDTSig where
  CanIssue := fun _ _ => True

variable {A}

end LeanProofs.Implementations.GrowOnlySet
