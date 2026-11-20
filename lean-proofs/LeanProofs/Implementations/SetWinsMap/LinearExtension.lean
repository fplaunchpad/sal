import LeanProofs.Implementations.SetWinsMap.Laws

/-!
# The set-wins multimap: clause 1

The join lemma, from the verification conditions in `Laws.lean`.
-/

namespace LeanProofs.Implementations.SetWinsMap

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-- **The join lemma**, from the verification conditions in `Laws.lean`. -/
theorem joinLemma : @Join (D K V).toMRDTSig (Interface.rcOrder (D K V)) :=
  Metatheory.joinLemma_of_vcs laws rc_non_comm cond_comm joinLaws

/-! ## Issuance -/

variable (K V)

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance (D K V).toMRDTSig where
  CanIssue := fun _ _ => True

variable {K V}

end LeanProofs.Implementations.SetWinsMap
