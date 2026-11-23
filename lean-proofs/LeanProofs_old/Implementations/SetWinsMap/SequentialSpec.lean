import LeanProofs.Implementations.SetWinsMap.LinearExtension
import LeanProofs.Soundness.SequentialSpec

/-!
# The set-wins multimap: clause 2

The multimap specification, the abstraction function `view`, and the
sequential premise.
-/

namespace LeanProofs.Implementations.SetWinsMap

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-! ## `Spec` and the certificate -/

variable (K V)

/-- `Spec`: an ordinary multimap, with no timestamps anywhere. -/
def specMachine : DeterministicSpec (type K V).OType (type K V).QType (type K V).ValType where
  State := Finset (K × V)
  initial := ∅
  update S o := match o with
    | .set k v => insert (k, v) S
    | .del k => S.filter (fun q => q.1 ≠ k)
  query S k := (S.filter (fun q => q.1 = k)).image Prod.snd

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec (type K V) := (specMachine K V).toSpec

variable {K V}

@[simp] theorem view_empty : view (∅ : St K V) = ∅ := by simp [view]

/-- Erasing the timestamps commutes with the update. -/
@[simp] theorem view_step (S : St K V) (e : (D K V).Event) :
    view (step S e) = (specMachine K V).update (view S) e.op := by
  rcases e with ⟨t, r, o⟩
  cases o with
  | set k v => simp [step, view, specMachine, Op.op, Op.time]
  | del k =>
      ext q
      simp only [view, step, specMachine, Op.op, Finset.mem_image,
        Finset.mem_filter]
      constructor
      · rintro ⟨w, ⟨hw, hwk⟩, rfl⟩; exact ⟨⟨w, hw, rfl⟩, hwk⟩
      · rintro ⟨⟨w, hw, hwq⟩, hqk⟩; exact ⟨w, ⟨hw, hwq ▸ hqk⟩, hwq⟩

theorem view_fold (S : St K V) (ops : List (D K V).Event) :
    view (applySeq (D K V).toMRDTSig.toUpdateSig S ops)
      = (ops.map Op.op).foldl (specMachine K V).update (view S) := by
  induction ops generalizing S with
  | nil => rfl
  | cons e ops ih => simpa [applySeq] using ih (step S e)

/-- The sequential premise: every replay of the implementation is explained
by the ordinary multimap language. -/
theorem specSound : Soundness.SpecSound (D K V) (historySpec K V) := by
  intro pi q
  have hlabels : projectedUpdates (D := (D K V).toMRDTSig) pi
      = DeterministicSpec.updateLabels (pi.map Op.op) := by
    simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
      Function.comp]
  rw [hlabels, historySpec, (specMachine K V).updates_query_iff]
  change ((view (applySeq (D K V).toMRDTSig.toUpdateSig (∅ : St K V) pi)).filter
      (fun w => w.1 = q)).image Prod.snd = _
  rw [view_fold, view_empty]
  rfl

end LeanProofs.Implementations.SetWinsMap
