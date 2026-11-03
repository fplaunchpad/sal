import LeanProofs.Implementations.FlatCounter.Laws
import LeanProofs.Metatheory.Adequacy
import LeanProofs.Soundness.RALinearizability

/-!
# The counter: `Spec` and its certificate

The independent sequential specification of Appendix `app:dt-counter`, the
issuance guard, and the RA-linearizability certificate obtained by applying
the metatheory.
-/

namespace LeanProofs.Implementations.FlatCounter

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1 LeanProofs.Interface

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance D.toMRDTSig where
  CanIssue := fun _ _ => True

/-- `Spec`: state an integer `z`, initially `0`, with `z -e-> z + delta(o)`
and `z -rd=>y-> z` when `y = z`. Defined without consulting the
implementation. -/
def Spec : SequentialSpec D.toMRDTSig where
  State := Int
  init := 0
  step z e := z + delta e.op
  Legal := fun _ => True
  query := fun z _ => z

/-- SPEC-NON-COMM holds trivially here: the specification's operations
commute too, so it asks nothing the implementation does not already give. -/
theorem spec_non_comm (e₁ e₂ : D.Event) (z : Spec.State) :
    Spec.step (Spec.step z e₁) e₂ = Spec.step (Spec.step z e₂) e₁ := by
  change Int at z
  change (z + delta e₁.op) + delta e₂.op = (z + delta e₂.op) + delta e₁.op
  omega

theorem conformance : Conformance D Spec (· = ·) :=
  ⟨fun _ => True.intro, fun _ => rfl, fun _ _ => rfl⟩

/-- **The certificate.** Every stored version of every certified execution is
RA-linearizable against `Spec`. -/
noncomputable def certificate : VerifiedMRDT D.toMRDTSig :=
  Metatheory.raLinearizable obligations issuance Spec (· = ·) conformance

/-- The join lemma for this counter, restated. It is proved by the
metatheory from the obligations, not here. -/
theorem joinLemma : @Join D.toMRDTSig (Metatheory.rcOrder D) :=
  Metatheory.joinLemma obligations

/-- **VC4** CAUSAL-DELTA, derived rather than assumed. -/
theorem vc4_causal_delta : CausalDeltaLaw D.toMRDTSig :=
  Metatheory.vc4_causal_delta obligations

/-! ## RA-linearizability

`Spec` again, as a language of histories, which is the form Definition 4
uses. It is the same machine, read as the set of admitted histories. -/

/-- The specification as a deterministic machine. -/
def specMachine : DeterministicSpec type.OType type.QType type.ValType where
  State := Int
  initial := 0
  update z o := z + delta o
  query z _ := z

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec type := specMachine.toSpec

/-- The sequential premise: `ops(pi) . (q => b)` is admitted by `Spec`, with
`b` the implementation's own answer. -/
theorem specSound : Soundness.SpecSound D historySpec := by
  intro pi q
  have hlabels : projectedUpdates (D := D.toMRDTSig) pi
      = DeterministicSpec.updateLabels (pi.map Op.op) := by
    simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
      Function.comp]
  rw [hlabels, historySpec, specMachine.updates_query_iff]
  show D.query (D.applyList D.sigma0 pi) q
    = ((pi.map Op.op).foldl (fun z o => z + delta o) 0)
  simp [Impl.applyList, List.foldl_map]
  rfl

/-- **RA-linearizability.** Every certified execution of the counter
satisfies Definition 4 against `Spec`. -/
theorem raLinearizable : Soundness.CertifiedRA D historySpec issuance :=
  Soundness.certifiedRA obligations specSound

#print axioms joinLemma
#print axioms certificate
#print axioms raLinearizable

end LeanProofs.Implementations.FlatCounter
