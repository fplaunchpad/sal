import LeanProofs.Implementations.ORSet.Laws
import LeanProofs.Metatheory.PaperAdequacy

/-!
# The OR-set: clause 1

The join lemma, from the verification conditions in `Laws.lean`. The row's
certificate goes through `Soundness.certifiedRA`, which rebuilds this from
`obligations`, so what follows is the statement in its own right.
-/

namespace LeanProofs.Implementations.ORSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {A : Type} [DecidableEq A]

/-- **The join lemma**, from the verification conditions.

VC1 to VC5 are in `Laws.lean`, proved for this row from the closed
description of `can(E)` and not from `Join`, so there is nothing circular
here: `Metatheory.joinLemma` turns them into the join lemma exactly as it
does for a row whose events all commute.

Nothing on that route asks for commutation. What kept this row off it was
the arbitrary-state form of VC3, which is false for a `merge` that reads its
base. Once the conditions are stated as Section 5 states them, the route is
open. -/
theorem joinLemma : PaperJoin (D A) :=
  Metatheory.joinLemma obligations

/-! ## Issuance -/

variable (A)

/-- Issuance: `G(e, O) <=> true`. The exact OR-set needs no payload and no
side condition on the events a replica may mint. -/
def issuance : Issuance (D A).toMRDTSig where
  CanIssue := fun _ _ => True

variable {A}

end LeanProofs.Implementations.ORSet
