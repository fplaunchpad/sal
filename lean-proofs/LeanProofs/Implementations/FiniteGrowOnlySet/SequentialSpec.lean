import LeanProofs.Implementations.FiniteGrowOnlySet.LinearExtension
import LeanProofs.Soundness.SequentialSpec

/-!
# The enumerable grow-only set: clause 2

The sequential specification on the `Finset` carrier and the sequential
premise.
-/

namespace LeanProofs.Implementations.FiniteGrowOnlySet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable (A : Type) [DecidableEq A]
variable {A}

/-! ## RA-linearizability -/

variable (A)

/-- The specification as a deterministic machine. -/
def specMachine : DeterministicSpec (type A).OType (type A).QType (type A).ValType where
  State := Finset A
  initial := ∅
  update S o := insert o S
  query S _ := S

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec (type A) := (specMachine A).toSpec

variable {A}

/-- The sequential premise. -/
theorem specSound : Soundness.SpecSound (D A) (historySpec A) := by
  intro pi q
  have hlabels : projectedUpdates (D := (D A).toMRDTSig) pi
      = DeterministicSpec.updateLabels (pi.map Op.op) := by
    simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
      Function.comp]
  rw [hlabels, historySpec, (specMachine A).updates_query_iff]
  show (D A).applyList (D A).sigma0 pi
    = (pi.map Op.op).foldl (fun S o => insert o S) (∅ : Finset A)
  simp [Impl.applyList, List.foldl_map]
  rfl

end LeanProofs.Implementations.FiniteGrowOnlySet
