import LeanProofs.Implementations.FlatGrowOnlyMap.LinearExtension
import LeanProofs.Soundness.SequentialSpec

/-!
# The flat grow-only map: clause 2

The sequential specification of Appendix `app:dt-flat-grow-only-map` and the
sequential premise.
-/

namespace LeanProofs.Implementations.FlatGrowOnlyMap

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {A : Type} [DecidableEq A]

/-! ## RA-linearizability -/

variable (A)

/-- The specification as a deterministic machine. -/
def specMachine : DeterministicSpec (type A).OType (type A).QType (type A).ValType where
  State := Finset A
  initial := ∅
  update S o := insert o S
  query S _ := fun x => decide (x ∈ S)

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec (type A) := (specMachine A).toSpec

variable {A}

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

/-- The sequential premise. -/
theorem specSound : Soundness.SpecSound (D A) (historySpec A) := by
  intro pi q
  have hlabels : projectedUpdates (D := (D A).toMRDTSig) pi
      = DeterministicSpec.updateLabels (pi.map Op.op) := by
    simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
      Function.comp]
  rw [hlabels, historySpec, (specMachine A).updates_query_iff]
  exact fold_eq pi (D A).sigma0 (∅ : Finset A) (fun _ => rfl)

/-! ## `Laws(D_type, Spec)`: the fourth law

SPEC-NON-COMM is the one law of Section 4 that mentions `Spec`, so it is
proved here rather than in `Laws.lean`. The specification inserts, so its two updates commute for the same reason
the implementation's do. -/

/-- Every pair of operations commutes in `Spec`. -/
theorem spec_commutes (o₁ o₂ : (type A).OType) :
    Interface.spec_commutes (historySpec A) o₁ o₂ :=
  (specMachine A).language_commutes o₁ o₂ (fun _ => Finset.insert_comm _ _ _)

/-- **SPEC-NON-COMM**: no implementation commutation erases a specification
conflict, because `Spec` has no conflict to erase. -/
theorem spec_non_comm : Interface.spec_non_comm (D A) (historySpec A) :=
  Interface.spec_non_comm_of_spec_commutes spec_commutes

end LeanProofs.Implementations.FlatGrowOnlyMap
