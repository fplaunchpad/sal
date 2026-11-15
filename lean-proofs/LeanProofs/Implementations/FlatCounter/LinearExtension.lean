import LeanProofs.Implementations.FlatCounter.Laws
import LeanProofs.Soundness.LinearExtension

/-!
# The counter: clause 1

Issuance, and the join lemma obtained from the obligations. Nothing here
mentions `Spec`.
-/

namespace LeanProofs.Implementations.FlatCounter

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1 LeanProofs.Interface

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance D.toMRDTSig where
  CanIssue := fun _ _ => True

end LeanProofs.Implementations.FlatCounter
