import LeanProofs.Implementations.ORSet.LinearExtension
import LeanProofs.Soundness.SequentialSpec

/-!
# The OR-set: clause 2

The ordinary-set specification, the abstraction function `view` of Section 6,
and the sequential premise.
-/

namespace LeanProofs.Implementations.ORSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {A : Type} [DecidableEq A]

/-! ## `Spec` and the certificate -/

variable (A)

/-- `Spec`: an ordinary set, with no timestamps anywhere. `add` inserts,
`remove` erases, and the query reports membership. -/
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

@[simp] theorem view_empty : view (∅ : St A) = ∅ := by simp [view]

/-- The client view tracks the ordinary-set update exactly. -/
@[simp] theorem view_step (S : St A) (e : (D A).Event) :
    view (step S e) = (specMachine A).update (view S) e.op := by
  rcases e with ⟨t, r, o⟩
  cases o with
  | add x => simp [step, view, specMachine, Op.op, Op.time]
  | remove x =>
      ext y
      simp only [view, step, specMachine, Op.op, Finset.mem_image,
        Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨q, ⟨hq, hqx⟩, rfl⟩; exact ⟨hqx, q, hq, rfl⟩
      · rintro ⟨hyx, q, hq, hqy⟩; exact ⟨q, ⟨hq, hqy ▸ hyx⟩, hqy⟩

theorem view_fold (S : St A) (ops : List (D A).Event) :
    view (applySeq (D A).toMRDTSig.toUpdateSig S ops)
      = (ops.map Op.op).foldl (specMachine A).update (view S) := by
  induction ops generalizing S with
  | nil => rfl
  | cons e ops ih => simpa [applySeq] using ih (step S e)

/-- The sequential premise: every replay of the implementation is explained
by the ordinary-set language, with no timestamp in any label. -/
theorem specSound : Soundness.SpecSound (D A) (historySpec A) := by
  intro pi q
  have hlabels : projectedUpdates (D := (D A).toMRDTSig) pi
      = DeterministicSpec.updateLabels (pi.map Op.op) := by
    simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
      Function.comp]
  rw [hlabels, historySpec, (specMachine A).updates_query_iff]
  change decide (q ∈ view (applySeq (D A).toMRDTSig.toUpdateSig (∅ : St A) pi)) = _
  rw [view_fold, view_empty]
  rfl

end LeanProofs.Implementations.ORSet
