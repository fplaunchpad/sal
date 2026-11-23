import LeanProofs.Implementations.FlatCounter.Laws
import LeanProofs.Soundness.LinearExtension
import LeanProofs.Metatheory.PaperAdequacy

/-!
# The counter: clause 1

The join lemma obtained from the obligations, and issuance. Nothing here
mentions `Spec`.
-/

namespace LeanProofs.Implementations.FlatCounter

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1 LeanProofs.Interface

/-- **The join lemma**: merging canonical states of two branches gives the
canonical state of the union of their event sets.

It is `Metatheory.joinLemma` applied to this row's `obligations`, which is
how every row on this route obtains it. The certificate does not take it as
an argument, since `Soundness.certifiedRA` rebuilds it from the same
inputs; it is named here as the statement in its own right. -/
theorem joinLemma : PaperJoin D :=
  Metatheory.joinLemma obligations

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance D.toMRDTSig where
  CanIssue := fun _ _ => True

end LeanProofs.Implementations.FlatCounter
