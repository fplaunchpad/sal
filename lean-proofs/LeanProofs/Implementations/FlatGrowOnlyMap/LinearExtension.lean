import LeanProofs.Implementations.FlatGrowOnlyMap.Laws
import LeanProofs.Soundness.LinearExtension

/-!
# The flat grow-only map: clause 1

Issuance, and the join lemma obtained from the obligations. `fold_eq` is the
replay lemma the conformance file consumes.
-/

namespace LeanProofs.Implementations.FlatGrowOnlyMap

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {A : Type} [DecidableEq A]

/-- Replaying events into the Boolean carrier agrees pointwise with
replaying their payloads into a finite set. -/
theorem fold_eq (pi : List (D A).Event) (S : (D A).Sigma) (F : Finset A)
    (h : ∀ x, S x = decide (x ∈ F)) :
    (D A).applyList S pi
      = fun x => decide (x ∈ (pi.map Op.op).foldl (fun F o => insert o F) F) := by
  induction pi generalizing S F with
  | nil => funext x; exact h x
  | cons e rest ih =>
      refine ih _ _ ?_
      intro x
      change (S x || decide (x = e.op)) = decide (x ∈ insert e.op F)
      rw [h x]
      by_cases hx : x = e.op <;> by_cases hF : x ∈ F <;>
        simp [hx, hF, Finset.mem_insert]

variable (A)

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance (D A).toMRDTSig where
  CanIssue := fun _ _ => True

variable {A}

end LeanProofs.Implementations.FlatGrowOnlyMap
