import LeanProofs.Implementations.GrowOnlySet.Laws
import LeanProofs.Soundness.LinearExtension

/-!
# The grow-only set: clause 1

The join lemma obtained from the obligations, and issuance.
-/

namespace LeanProofs.Implementations.GrowOnlySet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1 LeanProofs.Interface

variable {A : Type} [DecidableEq A]

/-- **The join lemma**: merging canonical states of two branches gives the
canonical state of the union of their event sets.

It is `Metatheory.joinLemma` applied to this row's `obligations`, which is
how every row on this route obtains it. The certificate does not take it as
an argument, since `Soundness.certifiedRA` rebuilds it from the same bundle;
it is named here as the statement in its own right. -/
theorem joinLemma : @Join (D A).toMRDTSig (Interface.rcOrder (D A)) :=
  Metatheory.joinLemma obligations

variable (A)

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance (D A).toMRDTSig where
  CanIssue := fun _ _ => True

variable {A}

end LeanProofs.Implementations.GrowOnlySet
