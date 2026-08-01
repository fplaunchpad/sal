import Sal.ConditionedMRDTs.Metatheory.WitnessClass

/-!
# A compatibility interface for ternary Join lemmas

The conditioned development has several intentionally different notions of a
canonical state: the plain existential witness, restricted witness classes,
coherent witnesses, and observational quotients.  Their ternary Join statements
nevertheless share the same event-set geometry.

This file factors that geometry without replacing any established interface.
It is an adapter layer: instances can continue proving `JoinLemma3At` or
`JoinLemma3AtW`, while generic developments may consume `JoinKitAt`.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

/-- A choice of canonical-state predicate.  Forgetting to the base adequacy
predicate is deliberately separate: an arbitrary arbitration or observational
quotient need not admit such a map. -/
structure CanonicalizationDoctrine (D : ConditionedMRDTSig) where
  Canon : Sal.Emulation.Configuration D.toCRDTSig →
    Set (Op D.AppOp) → D.State → Prop

/-- A doctrine whose witnesses can be consumed by the original, plain
adequacy layer. -/
def WeakensToPlain (D : ConditionedMRDTSig)
    (K : CanonicalizationDoctrine D) : Prop :=
  ∀ {C E s}, K.Canon C E s → IsCanonicalState C E s

/-- The event-set geometry common to the plain and witness-restricted ternary
Join hooks.  Further doctrines may add premises outside this core; adapters
should expose those premises through their surrounding configuration contract. -/
def JoinKitAt (D : ConditionedMRDTSig) (K : CanonicalizationDoctrine D)
    (C : Sal.Emulation.Configuration D.toCRDTSig) : Prop :=
  ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
    K.Canon C (ev₁ ∩ ev₂) s₀ →
    K.Canon C ev₁ s₁ → K.Canon C ev₂ s₂ →
    K.Canon C (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

/-- The ordinary canonical-state doctrine. -/
def plainDoctrine (D : ConditionedMRDTSig) : CanonicalizationDoctrine D where
  Canon := IsCanonicalState

/-- A witness-class canonicalization doctrine. -/
def witnessDoctrine (D : ConditionedMRDTSig)
    (W : List (Op D.AppOp) → Prop) : CanonicalizationDoctrine D where
  Canon := IsCanonicalStateW W

theorem plainDoctrine_weakens (D : ConditionedMRDTSig) :
    WeakensToPlain D (plainDoctrine D) := id

theorem witnessDoctrine_weakens (D : ConditionedMRDTSig)
    (W : List (Op D.AppOp) → Prop) :
    WeakensToPlain D (witnessDoctrine D W) := IsCanonicalStateW.weaken

/-- The compatibility interface is definitionally the established plain Join
hook when instantiated with the plain doctrine. -/
theorem joinKitAt_plain_iff (D : ConditionedMRDTSig)
    (C : Sal.Emulation.Configuration D.toCRDTSig) :
    JoinKitAt D (plainDoctrine D) C ↔ JoinLemma3At D C := by
  rfl

/-- The compatibility interface is definitionally the established restricted
witness Join hook when instantiated with a witness doctrine. -/
theorem joinKitAt_witness_iff (D : ConditionedMRDTSig)
    (W : List (Op D.AppOp) → Prop)
    (C : Sal.Emulation.Configuration D.toCRDTSig) :
    JoinKitAt D (witnessDoctrine D W) C ↔ JoinLemma3AtW D W C := by
  rfl

end Sal.ConditionedMRDTs
