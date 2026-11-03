import LeanProofs.Implementations.FiniteGrowOnlySet.Laws
import LeanProofs.Metatheory.Adequacy
import LeanProofs.Soundness.RALinearizability

/-!
# The enumerable grow-only set: `Spec` and its certificate

Specification, issuance guard, and the RA-linearizability certificate.
-/

namespace LeanProofs.Implementations.FiniteGrowOnlySet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable (A : Type) [DecidableEq A]

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance (D A).toMRDTSig where
  CanIssue := fun _ _ => True

/-- `Spec`: a finite set, initially empty, with `S -e-> S union {o}`. -/
@[reducible] def Spec : SequentialSpec (D A).toMRDTSig where
  State := Finset A
  init := ∅
  step S e := insert e.op S
  Legal := fun _ => True
  query := fun S _ => S

variable {A}

/-- SPEC-NON-COMM: two insertions commute in `Spec` as well. -/
theorem spec_non_comm (e₁ e₂ : (D A).Event) (S : (Spec A).State) :
    (Spec A).step ((Spec A).step S e₁) e₂ = (Spec A).step ((Spec A).step S e₂) e₁ := by
  change insert e₂.op (insert e₁.op S) = insert e₁.op (insert e₂.op S)
  exact Finset.insert_comm _ _ _

theorem conformance : Conformance (D A) (Spec A) (· = ·) :=
  ⟨fun _ => True.intro, fun _ => rfl, fun _ _ => rfl⟩

/-- **The certificate.** -/
noncomputable def certificate : VerifiedMRDT (D A).toMRDTSig :=
  Metatheory.raLinearizable obligations (issuance A) (Spec A) (· = ·) conformance

/-- The join lemma, proved by the metatheory from the obligations. -/
theorem joinLemma : @Join (D A).toMRDTSig (Metatheory.rcOrder (D A)) :=
  Metatheory.joinLemma obligations

/-- **VC4** CAUSAL-DELTA, derived rather than assumed. -/
theorem vc4_causal_delta : CausalDeltaLaw (D A).toMRDTSig :=
  Metatheory.vc4_causal_delta obligations

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

/-- **RA-linearizability.** -/
theorem raLinearizable :
    Soundness.CertifiedRA (D A) (historySpec A) (issuance A) :=
  Soundness.certifiedRA obligations specSound

#print axioms joinLemma
#print axioms certificate
#print axioms raLinearizable

end LeanProofs.Implementations.FiniteGrowOnlySet
