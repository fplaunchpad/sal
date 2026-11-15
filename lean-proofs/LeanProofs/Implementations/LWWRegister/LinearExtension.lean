import LeanProofs.Implementations.LWWRegister.Laws
import LeanProofs.Soundness.LinearExtension

/-!
# The LWW register: clause 1

Issuance, and the join lemma obtained from the obligations. Nothing here
mentions `Spec`.
-/

namespace LeanProofs.Implementations.LWWRegister

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance D.toMRDTSig where
  CanIssue := fun _ _ => True

end LeanProofs.Implementations.LWWRegister
