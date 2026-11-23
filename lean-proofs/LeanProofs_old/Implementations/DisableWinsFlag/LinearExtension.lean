import LeanProofs.Implementations.DisableWinsFlag.Laws
import LeanProofs.Metatheory.PaperAdequacy

/-!
# The flag core: clause 1

The join lemma obtained from the obligations, and issuance. Nothing here
mentions `Spec`.
-/

namespace LeanProofs.Implementations.DisableWinsFlag

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

/-- **The join lemma**: merging canonical states of two branches gives the
canonical state of the union of their event sets. -/
theorem joinLemma : PaperJoin D :=
  Metatheory.joinLemma obligations

/-! ## Issuance -/

/-- Issuance: `G(e, O) <=> true`. The source algorithm puts no side condition
on the events a replica may mint. -/
def issuance : Issuance D.toMRDTSig where
  CanIssue := fun _ _ => True

end LeanProofs.Implementations.DisableWinsFlag
