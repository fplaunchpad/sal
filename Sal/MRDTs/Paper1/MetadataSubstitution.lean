import Sal.MRDTs.Paper1.AbstractORSet

/-! A metadata substitution obligation independent of representation Join.
The generic merge induction may replace a state by another representation of
the same indexed history. This contract preserves both abstract results and
metadata validity, conditional on validity of the comparison result. It does
not assume that merge preserves representation or that merge is a congruence
on arbitrary observationally equivalent concrete states. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT
open Foundation
variable {D : MRDTSig}

def MetadataSubstitution (A : Model D) (R : Representation D) : Prop :=
  ∀ (C : ReplayContext D.toUpdateSig) (E₁ E₂ : Set (Op D.AppOp))
    (l a b l' a' b' : D.State),
    (∀ e ∈ E₁, e ∈ C.events) → (∀ e ∈ E₂, e ∈ C.events) →
    R C (E₁ ∩ E₂) l → R C E₁ a → R C E₂ b →
    R C (E₁ ∩ E₂) l' → R C E₁ a' → R C E₂ b' →
    Equivalent A (D.merge l a b) (D.merge l' a' b') ∧
      (R C (E₁ ∪ E₂) (D.merge l' a' b') → R C (E₁ ∪ E₂) (D.merge l a b))

/-- Exact metadata uniqueness is a stronger, independently checkable way to
discharge guarded substitution. It does not assert uniqueness of all concrete
states with the same abstraction. -/
theorem metadataSubstitution_of_unique {A : Model D} {R : Representation D}
    (unique : ∀ C E s t, (∀ e ∈ E, e ∈ C.events) → R C E s → R C E t → s = t) :
    MetadataSubstitution A R := by
  intro C E₁ E₂ l a b l' a' b' sup₁ sup₂ hl ha hb hl' ha' hb'
  have el := unique C (E₁ ∩ E₂) l l' (fun e he => sup₁ e he.1) hl hl'
  have ea := unique C E₁ a a' sup₁ ha ha'
  have eb := unique C E₂ b b' sup₂ hb hb'
  subst l'
  subst a'
  subst b'
  exact ⟨equivalent_refl A _,id⟩

end Sal.MRDTs.Paper1.AbstractMRDT

namespace Sal.MRDTs.Paper1.ORSet.AbstractSpec
open Foundation
variable {α : Type} [DecidableEq α]

theorem metadataSubstitution : AbstractMRDT.MetadataSubstitution
    (model (α := α)) representation := by
  apply AbstractMRDT.metadataSubstitution_of_unique
  intro C E s t supported hs ht
  letI : ReplayPolicy (D α).toUpdateSig := (conflict α).lift
  exact isCanonicalState_unique_of_replayLaws restrictedLaws.replayLaws supported hs ht

end Sal.MRDTs.Paper1.ORSet.AbstractSpec

namespace Sal.MRDTs.Paper1.EfficientORSet.AbstractSpec
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

theorem metadataSubstitution : AbstractMRDT.MetadataSubstitution
    (model (α := α)) representation := by
  apply AbstractMRDT.metadataSubstitution_of_unique
  intro C E s t _ hs ht
  apply Finset.ext
  intro p
  exact (hs.1 p).trans (ht.1 p).symm

end Sal.MRDTs.Paper1.EfficientORSet.AbstractSpec
