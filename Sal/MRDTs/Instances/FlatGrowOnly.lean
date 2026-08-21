import Sal.MRDTs.Instances.Common
import Sal.MRDTs.Metatheory.Correctness

/-! # Boolean grow-only stores

The production grow-only set and grow-only map share one pointwise-Boolean
MRDT proof.  The map instance treats key/value pairs as immutable entries.
-/

namespace Sal.MRDTs.Instances.FlatGrowOnly

open Sal.MRDTs.Foundation
open Sal.MRDTs.Instances
open Classical

variable (A : Type) [DecidableEq A]

noncomputable def D : MRDTSig where
  State := A → Bool
  dec_state := fun _ _ => Classical.propDecidable _
  init := fun _ => false
  AppOp := A
  dec_op := inferInstance
  Query := Unit
  Value := A → Bool
  update s e x := s x || decide (x = e.2.2)
  merge a b x := a x || b x
  query s _ := s
  rc _ _ := RcRes.Either
  mergeL l a b x := l x || (a x || b x)
  merge_init_slice _ _ := rfl

variable {A}

theorem all_comm (a b : Op (D A).AppOp) :
    (D A).toCRDTSig.commutes a b := by
  intro s
  funext x
  exact bor_rc (s x) (decide (x = a.2.2)) (decide (x = b.2.2))

theorem updateVCs : UpdateVCs (D A).toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b _ _
    constructor
    · intro h; exact absurd (all_comm a b) h
    · rintro (h | h) <;>
        (rw [show (D A).rc _ _ = RcRes.Either from rfl] at h;
         exact RcRes.noConfusion h)
  · intro a b c _ _
    rintro ⟨h, _⟩
    rw [show (D A).rc _ _ = RcRes.Either from rfl] at h
    exact RcRes.noConfusion h
  · intro s a b c π _ _ _ h _
    rw [show (D A).rc _ _ = RcRes.Either from rfl] at h
    exact RcRes.noConfusion h

theorem coreVCs3 : CoreVCs3 (D A) := by
  refine ⟨updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b; funext x; exact bor_comm (l x) (a x) (b x)
  · intro s; funext x; exact bor_init (s x)
  · intro l a b e; funext x
    exact bor_0op (l x) (a x) (b x) (decide (x = e.2.2))
  · intro a e π₀ π₂ _ _; funext x
    exact bor_peel
      (applySeq (D A).toCRDTSig (D A).init π₀ x) (a x)
      (applySeq (D A).toCRDTSig (D A).init π₂ x)
      (decide (x = e.2.2))

theorem deltaVCs3 : DeltaVCs3 (D A) := by
  constructor
  · intro m x₀ x₁ x₂ c; funext x
    exact bor_redis (m x) (x₀ x) (x₁ x) (x₂ x) (c x)
  · intro l m x c y; funext p
    exact bor_lredis (l p) (m p) (x p) (c p) (y p)

theorem join : JoinLemma3 (D A) :=
  join_lemma3_of_cd' coreVCs3 deltaVCs3
    (cdVC3_of_all_comm coreVCs3 all_comm)

def generation : GenerationContract (D A) where
  Guard := fun _ _ => True
  History := fun _ => True
  history_of_mint := fun _ _ => trivial

def convergence : ConvergenceCertificate (D A) generation where
  sound := fun h => ra_of_mintCertified (fun _ _ => join _) h
  soundV := fun h => ra_of_mintCertifiedV (fun _ _ => join _) h

def spec : SequentialSpec (Op A) where
  State := A → Bool
  init := fun _ => false
  step s e x := s x || decide (x = e.2.2)

def sequential : SequentialRefinement (D A) spec where
  Honest := fun _ => True
  Rel := (· = ·)
  init := rfl
  sound := fun _ _ => rfl

noncomputable def verified : VerifiedMRDT (D A) where
  generation := generation
  convergence := convergence
  Spec := spec
  sequential := sequential
  sequential_of_mint := fun _ _ => trivial
  safety := SafetyCertificate.trivial generation

noncomputable abbrev GOSet := D Nat
noncomputable abbrev GOMap := D (Nat × Nat)
noncomputable def gosetVerified : VerifiedMRDT GOSet := verified
noncomputable def gomapVerified : VerifiedMRDT GOMap := verified

#print axioms join
#print axioms gosetVerified
#print axioms gomapVerified

end Sal.MRDTs.Instances.FlatGrowOnly
