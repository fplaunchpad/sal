import LeanProofs.Implementations.FlatGrowOnlyMap.Laws
import LeanProofs.Metatheory.Adequacy
import LeanProofs.Soundness.RALinearizability

/-!
# The flat grow-only map: `Spec` and its certificate

The independent sequential specification of Appendix
`app:dt-flat-grow-only-map`, the issuance guard, and the RA-linearizability
certificate obtained by applying the metatheory.

The specification stores a **finite set** and answers with its characteristic
function, while the implementation stores the Boolean function directly. The
bridge between the two is `fold_eq` below, and it is the only real work in
this file.
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

/-- `Spec`: state a finite set, initially empty, with `S -e-> S union {o}`
and `S -rd=>y-> S` when `y` is the characteristic function of `S`.

Reducible so that `(Spec A).State` unfolds to `Finset A` during instance
search. -/
@[reducible] def Spec : SequentialSpec (D A).toMRDTSig where
  State := Finset A
  init := ∅
  step S e := insert e.op S
  Legal := fun _ => True
  query := fun S _ => fun x => decide (x ∈ S)

variable {A}

/-- `Rel` relates the Boolean carrier to the specification's finite set. -/
def Rel (S : (D A).Sigma) (F : (Spec A).State) : Prop := ∀ x, S x = decide (x ∈ F)

private theorem run_eq (pi : List (D A).Event) :
    (D A).applyList (D A).sigma0 pi = fun x => decide (x ∈ (Spec A).run pi) := by
  have := fold_eq pi (D A).sigma0 (∅ : Finset A) (fun _ => rfl)
  simpa [SequentialMachine.run, Spec, List.foldl_map] using this

/-- SPEC-NON-COMM: two insertions commute in `Spec` as well. -/
theorem spec_non_comm (e₁ e₂ : (D A).Event) (F : (Spec A).State) :
    (Spec A).step ((Spec A).step F e₁) e₂ = (Spec A).step ((Spec A).step F e₂) e₁ := by
  change insert e₂.op (insert e₁.op F) = insert e₁.op (insert e₂.op F)
  exact Finset.insert_comm _ _ _

theorem conformance : Conformance (D A) (Spec A) Rel := by
  refine ⟨fun _ => True.intro, fun pi => ?_, fun pi q => ?_⟩
  · intro x; rw [run_eq pi]
  · change (D A).applyList (D A).sigma0 pi = fun x => decide (x ∈ (Spec A).run pi)
    exact run_eq pi

/-- **The certificate.** -/
noncomputable def certificate : VerifiedMRDT (D A).toMRDTSig :=
  Metatheory.raLinearizable obligations (issuance A) (Spec A) Rel conformance

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
  query S _ := fun x => decide (x ∈ S)

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
  exact fold_eq pi (D A).sigma0 (∅ : Finset A) (fun _ => rfl)

/-- **RA-linearizability.** Every certified execution of the flat grow-only
map satisfies Definition 4 against `Spec`. -/
theorem raLinearizable :
    Soundness.CertifiedRA (D A) (historySpec A) (issuance A) :=
  Soundness.certifiedRA obligations specSound

#print axioms joinLemma
#print axioms certificate
#print axioms raLinearizable

end LeanProofs.Implementations.FlatGrowOnlyMap
