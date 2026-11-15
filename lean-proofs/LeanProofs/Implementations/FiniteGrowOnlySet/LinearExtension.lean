import LeanProofs.Implementations.FiniteGrowOnlySet.Laws
import LeanProofs.Soundness.LinearExtension

/-!
# The enumerable grow-only set: clause 1

Issuance, and the join lemma obtained from the obligations.
-/

namespace LeanProofs.Implementations.FiniteGrowOnlySet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable (A : Type) [DecidableEq A]

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance (D A).toMRDTSig where
  CanIssue := fun _ _ => True

variable {A}

end LeanProofs.Implementations.FiniteGrowOnlySet
