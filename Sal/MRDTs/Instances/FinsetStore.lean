import Sal.MRDTs.Framework.Product
import Sal.MRDTs.Metatheory.Correctness

/-! # Finite grow-only auxiliary store

The production Peritext carrier needs an enumerable representation for
rendering and state collection.  This is the finite counterpart of
`AddStore`; it has the same grow-only semantics and proof package.
-/

namespace Sal.MRDTs.Instances.FinsetStore

open Sal.MRDTs.Foundation

variable (α : Type) [DecidableEq α]

def D : MRDTSig where
  State := Finset α
  dec_state := inferInstance
  init := ∅
  AppOp := α
  dec_op := inferInstance
  Query := Unit
  Value := Finset α
  update s e := insert e.2.2 s
  merge := (· ∪ ·)
  query s _ := s
  rc _ _ := RcRes.Either
  mergeL _ a b := a ∪ b
  merge_init_slice _ _ := rfl

variable {α}

theorem all_comm (a b : Op (D α).AppOp) :
    (D α).toCRDTSig.commutes a b := by
  intro s
  apply Finset.ext
  intro x
  simp [D, or_left_comm]

theorem updateVCs : UpdateVCs (D α).toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b _ _
    constructor
    · intro h
      exact absurd (all_comm a b) h
    · rintro (h | h) <;> exact RcRes.noConfusion h
  · intro a b c _ _
    rintro ⟨h, _⟩
    exact RcRes.noConfusion h
  · intro s a b c π _ _ _ h _
    exact RcRes.noConfusion h

theorem coreVCs3 : CoreVCs3 (D α) := by
  refine ⟨updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b; apply Finset.ext; intro x; simp [D, or_comm]
  · intro s; apply Finset.ext; intro x; simp [D]
  · intro l a b e; apply Finset.ext; intro x
    simp [D, or_assoc, or_left_comm, or_comm]
  · intro a e π₀ π₂ _ _; apply Finset.ext; intro x
    simp [D, or_assoc, or_left_comm, or_comm]

theorem deltaVCs3 : DeltaVCs3 (D α) := by
  constructor
  · intro m x₀ x₁ x₂ c; apply Finset.ext; intro x
    simp [D, or_assoc, or_left_comm, or_comm]
  · intro l m x c y; apply Finset.ext; intro z
    simp [D, or_assoc, or_left_comm, or_comm]

theorem join : JoinLemma3 (D α) :=
  join_lemma3_of_cd' coreVCs3 deltaVCs3
    (cdVC3_of_all_comm coreVCs3 all_comm)

def generation : Issuance (D α) where
  CanIssue := fun _ _ => True

def convergence : ConvergenceCertificate (D α) generation where
  soundV := fun h => ra_of_mintCertifiedV (fun _ _ => join _) h

def spec : SequentialSpec (D α) where
  State := Finset α
  init := ∅
  step s e := insert e.2.2 s
  Legal := fun _ => True
  query := fun s _ => s

def sequential : SequentialRefinement (D α) spec.toSequentialMachine where
  Honest := fun _ => True
  Rel := (· = ·)
  init := rfl
  sound := fun _ _ => rfl

noncomputable def verified : VerifiedMRDT (D α) where
  issuance := generation
  arbitration := ArbitrationSpec.raw (D α)
  convergence := convergence
  Spec := spec
  Rel := (· = ·)
  legalization := LegalizationCertificate.ofTotal
    (fun _ => True.intro)
    (fun ops => sequential.sound ops True.intro)
    (fun _ _ => rfl)

#print axioms join
#print axioms verified

end Sal.MRDTs.Instances.FinsetStore
