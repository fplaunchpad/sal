import LeanProofs.Implementations.GrowOnlySet.LinearExtension
import LeanProofs.Soundness.SequentialSpec

/-!
# The grow-only set: clause 2

The independent sequential specification of Appendix `app:dt-grow-only-set`
and the sequential premise.
-/

namespace LeanProofs.Implementations.GrowOnlySet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1 LeanProofs.Interface

variable (A : Type) [DecidableEq A]
variable {A}

/-! ## RA-linearizability

`Spec` again, as a language of histories, which is the form Definition 4
uses. -/

variable (A)

/-- The specification as a deterministic machine. -/
def specMachine : DeterministicSpec (type A).OType (type A).QType (type A).ValType where
  State := Set A
  initial := ∅
  update S o := insert o S
  query S _ := S

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec (type A) := (specMachine A).toSpec

variable {A}

/-- The sequential premise: `ops(pi) . (q => b)` is admitted by `Spec`, with
`b` the implementation's own answer. -/
theorem specSound : Soundness.SpecSound (D A) (historySpec A) := by
  intro pi q
  have hlabels : projectedUpdates (D := (D A).toMRDTSig) pi
      = DeterministicSpec.updateLabels (pi.map Op.op) := by
    simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
      Function.comp]
  rw [hlabels, historySpec, (specMachine A).updates_query_iff]
  show (D A).query ((D A).applyList (D A).sigma0 pi) q
    = ((pi.map Op.op).foldl (fun S o => insert o S) (∅ : Set A))
  simp [Impl.applyList, List.foldl_map]
  rfl

/-! ## `Laws(D_type, Spec)`: the fourth law

SPEC-NON-COMM is the one law of Section 4 that mentions `Spec`, so it is
proved here rather than in `Laws.lean`. The specification inserts, so its two updates commute for the same reason
the implementation's do. -/

/-- Every pair of operations commutes in `Spec`. -/
theorem spec_commutes (o₁ o₂ : (type A).OType) :
    Interface.spec_commutes (historySpec A) o₁ o₂ :=
  (specMachine A).language_commutes o₁ o₂ (fun _ => Set.insert_comm _ _ _)

/-- **SPEC-NON-COMM**: no implementation commutation erases a specification
conflict, because `Spec` has no conflict to erase. -/
theorem spec_non_comm : Interface.spec_non_comm (D A) (historySpec A) :=
  Interface.spec_non_comm_of_spec_commutes spec_commutes

end LeanProofs.Implementations.GrowOnlySet
