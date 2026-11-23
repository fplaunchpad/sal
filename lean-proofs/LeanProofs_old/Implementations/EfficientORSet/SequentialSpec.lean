import LeanProofs.Implementations.EfficientORSet.LinearExtension
import LeanProofs.Soundness.SequentialSpec

/-!
# The efficient OR-set: clause 2

The ordinary-set specification of Appendix `app:dt-or-set`, the abstraction
function `elements` of Section 6, and the sequential premise. `elements`
erases the replica and the timestamp from every record, so a state holding
one record per replica per element reads as a plain set.

Nothing here mentions `merge`, `vis` or `rc`.
-/

namespace LeanProofs.Implementations.EfficientORSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {α : Type} [DecidableEq α]

variable (α)

/-- `Spec`: an ordinary set, with no replica and no timestamp anywhere.
`add` inserts, `remove` erases, and the query reports membership. -/
def specMachine : DeterministicSpec (itype α).OType (itype α).QType (itype α).ValType where
  State := Finset α
  initial := ∅
  update S o := match o with
    | .add x => insert x S
    | .remove x => S.erase x
  query S x := decide (x ∈ S)

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec (itype α) := (specMachine α).toSpec

variable {α}

@[simp] theorem elements_empty : elements (∅ : State α) = ∅ := by simp [elements]

/-- The client view tracks the ordinary-set update exactly. The replacement
an `add` performs is invisible through `elements`, and a `remove` drops
every record for its element, so no tombstone shows. -/
@[simp] theorem elements_update (s : State α) (e : Event α) :
    elements (update s e) = (specMachine α).update (elements s) e.op := by
  rcases e with ⟨t, r, o⟩
  cases o with
  | add x =>
    ext y
    simp only [elements, update, specMachine, Op.op, Finset.mem_image,
      Finset.mem_insert, Finset.mem_filter]
    constructor
    · rintro ⟨p, hp | hp, hpy⟩
      · subst p; exact Or.inl hpy.symm
      · exact Or.inr ⟨p, hp.1, hpy⟩
    · rintro (h | ⟨p, hp, hpy⟩)
      · exact ⟨(r, t, x), Or.inl rfl, h.symm⟩
      · by_cases hy : y = x
        · exact ⟨(r, t, x), Or.inl rfl, hy.symm⟩
        · exact ⟨p, Or.inr ⟨hp, fun h => hy (hpy.symm.trans h.2)⟩, hpy⟩
  | remove x =>
    ext y
    simp only [elements, update, specMachine, Op.op, Finset.mem_image,
      Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨p, ⟨hp, hpx⟩, hpy⟩
      exact ⟨fun h => hpx (hpy.trans h), p, hp, hpy⟩
    · rintro ⟨hy, p, hp, hpy⟩
      exact ⟨p, ⟨hp, fun h => hy (hpy.symm.trans h)⟩, hpy⟩

theorem elements_fold (s : State α) (ops : List (Event α)) :
    elements (applySeq (D α).toMRDTSig.toUpdateSig s ops)
      = (ops.map Op.op).foldl (specMachine α).update (elements s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons e ops ih => simpa [applySeq] using ih (update s e)

/-- The sequential premise: every replay of the implementation is explained
by the ordinary-set language, with no replica and no timestamp in any label. -/
theorem specSound : Soundness.SpecSound (D α) (historySpec α) := by
  intro pi q
  have hlabels : projectedUpdates (D := (D α).toMRDTSig) pi
      = DeterministicSpec.updateLabels (pi.map Op.op) := by
    simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
      Function.comp]
  rw [hlabels, historySpec, (specMachine α).updates_query_iff]
  change decide (q ∈ elements
    (applySeq (D α).toMRDTSig.toUpdateSig (∅ : State α) pi)) = _
  rw [elements_fold, elements_empty]
  rfl

end LeanProofs.Implementations.EfficientORSet
