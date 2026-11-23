import LeanProofs.Implementations.RemoveWinsSet.Laws
import LeanProofs.Metatheory.PaperAdequacy

/-!
# The remove-wins set: clause 1

Issuance, the step from a mint-honest configuration to a `Positive` context,
and the join lemma obtained from the obligations. Nothing here mentions
`Spec`.

This is the one row whose join lemma is not an all-context statement. It
holds at the contexts `Positive` admits, which is exactly what the issuance
guard delivers, and `Soundness.certifiedRA_on` asks for nothing more.
-/

namespace LeanProofs.Implementations.RemoveWinsSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {A : Type} [DecidableEq A] [Fintype A]

/-! ## Issuance -/

/-- Issuance: `G(e, s) <=> 0 < time(e)`. The reserved timestamp `0` belongs
to the seed tags of `sigma0` and may not be minted. -/
def issuance (A : Type) [DecidableEq A] [Fintype A] : Issuance (D A).toMRDTSig where
  CanIssue := fun e _ => 0 < e.time

/-- **The guard, as a condition on contexts.** A mint-honest configuration
minted every event it observes under `G`, so every one of them carries a
positive timestamp. This is the only step in the development that reads the
issuance column of Table 1. -/
theorem positive_of_mintHonest (C : Configuration (D A).toMRDTSig)
    (hmint : MintHonest (D A).toMRDTSig (issuance A).CanIssue C) :
    Positive C.replayContext := by
  intro e he
  obtain ⟨_, _, _, hg⟩ := hmint e he
  exact hg

/-! ## The join lemma -/

/-- **The join lemma**: merging canonical states of two branches gives the
canonical state of the union of their event sets, at every context the
issuance guard admits.

It is `Metatheory.joinLemma` applied to this row's `obligations`, which is
how every row obtains it. The guard rides along in the statement: `Positive`
is the side condition the bundle is indexed by. The certificate does not
take the lemma as an argument, since `Soundness.certifiedRA_on` rebuilds it
from the same bundle; it is named here as the statement in its own right. -/
theorem joinLemma : PaperJoinOn (D A) Positive :=
  Metatheory.joinLemma obligations

end LeanProofs.Implementations.RemoveWinsSet
