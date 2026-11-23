import LeanProofs.Implementations.EfficientORSet.Laws
import LeanProofs.Metatheory.PaperAdequacy

/-!
# The efficient OR-set: clause 1

The join lemma, from the verification conditions in `Laws.lean`. The row's
certificate goes through `Soundness.certifiedRA`, which rebuilds it from
the same bundle, so what follows is the statement in its own right.

`Metatheory.joinLemma` is the same five-VC induction every other row runs,
at the representation `can^C(E) = s` read at `lo^C_E`. Nothing about
commutation is asked on the way in, and nothing about `rc` beyond the
guarded laws.
-/

namespace LeanProofs.Implementations.EfficientORSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {α : Type} [DecidableEq α]

/-- **The join lemma**, from the verification conditions: merging canonical
states produces the canonical state of the union of their event sets. -/
theorem joinLemma : PaperJoin (D α) :=
  Metatheory.joinLemma obligations

/-! ## Issuance -/

variable (α)

/-- Issuance: `G(e, O) <=> true`. The efficient OR-set reserves no
timestamp and needs no side condition on the events a replica may mint. -/
def issuance : Issuance (D α).toMRDTSig where
  CanIssue := fun _ _ => True

variable {α}

#print axioms joinLemma

end LeanProofs.Implementations.EfficientORSet
