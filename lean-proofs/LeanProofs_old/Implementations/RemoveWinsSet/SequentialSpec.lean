import LeanProofs.Implementations.RemoveWinsSet.LinearExtension
import LeanProofs.Soundness.SequentialSpec

/-!
# The remove-wins set: clause 2

The set specification, the abstraction function `view`, and the sequential
premise.
-/

namespace LeanProofs.Implementations.RemoveWinsSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {A : Type} [DecidableEq A] [Fintype A]

/-! ## `Spec` and the certificate -/

variable (A)

/-- `Spec`: an ordinary set, empty at the start, with no timestamps
anywhere. -/
def specMachine : DeterministicSpec (type A).OType (type A).QType (type A).ValType where
  State := Finset A
  initial := ∅
  update S o := match o with
    | .add x => insert x S
    | .remove x => S.erase x
  query S x := decide (x ∈ S)

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec (type A) := (specMachine A).toSpec

variable {A}

@[simp] theorem view_sigma0 : view (sigma0 A) = ∅ := by
  ext y
  simp [view, sigma0]

/-- Erasing the timestamps commutes with the update. -/
@[simp] theorem view_step (S : St A) (e : (D A).Event) :
    view (step S e) = (specMachine A).update (view S) e.op := by
  rcases e with ⟨t, r, o⟩
  cases o with
  | remove x =>
      ext y
      simp only [view, step, specMachine, Op.op, Op.time, Finset.mem_sdiff,
        Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_insert,
        Finset.mem_erase]
      constructor
      · intro h
        exact ⟨fun hy => h ⟨(x, t), Or.inl rfl, hy ▸ rfl⟩,
          fun ⟨q, hq, hqy⟩ => h ⟨q, Or.inr hq, hqy⟩⟩
      · rintro ⟨hyx, h⟩ ⟨q, hq | hq, hqy⟩
        · exact hyx (by rw [← hqy, hq])
        · exact h ⟨q, hq, hqy⟩
  | add x =>
      ext y
      simp only [view, step, specMachine, Op.op, Finset.mem_sdiff,
        Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_filter,
        Finset.mem_insert]
      constructor
      · intro h
        by_cases hyx : y = x
        · exact Or.inl hyx
        · exact Or.inr (fun ⟨q, hq, hqy⟩ => h ⟨q, ⟨hq, by rw [hqy]; exact hyx⟩, hqy⟩)
      · rintro (rfl | h) ⟨q, ⟨hq, hqx⟩, hqy⟩
        · exact hqx (by rw [hqy])
        · exact h ⟨q, hq, hqy⟩

theorem view_fold (S : St A) (ops : List (D A).Event) :
    view (applySeq (D A).toMRDTSig.toUpdateSig S ops)
      = (ops.map Op.op).foldl (specMachine A).update (view S) := by
  induction ops generalizing S with
  | nil => rfl
  | cons e ops ih => simpa [applySeq] using ih (step S e)

/-- The sequential premise, unrestricted. -/
theorem specSound : Soundness.SpecSound (D A) (historySpec A) := by
  intro pi q
  have hlabels : projectedUpdates (D := (D A).toMRDTSig) pi
      = DeterministicSpec.updateLabels (pi.map Op.op) := by
    simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
      Function.comp]
  rw [hlabels, historySpec, (specMachine A).updates_query_iff]
  change decide (q ∈ view (applySeq (D A).toMRDTSig.toUpdateSig (sigma0 A) pi)) = _
  rw [view_fold, view_sigma0]
  rfl

end LeanProofs.Implementations.RemoveWinsSet
