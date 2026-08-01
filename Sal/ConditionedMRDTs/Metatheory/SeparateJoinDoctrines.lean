import Sal.ConditionedMRDTs.Metatheory.AbstractJoin
import Sal.ConditionedMRDTs.Metatheory.GenericEqQuotient_H
import Sal.ConditionedMRDTs.Metatheory.WitnessCoherence

/-!
# Separate doctrines for the stronger Join routes

The state-equality Join family varies only its canonicity predicate and is
captured by `AbstractJoinAt`.  The observational and coherent-witness routes
carry additional, counterexample-justified premises.  They therefore remain
separate public doctrines rather than being hidden behind a sum type or a
weak common interface.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open GenericEqQuotient

/-- The premises and canonicity judgment of an observational Join.  Invariant,
universe, and closure obligations are fields, so the ternary event geometry is
independent of the particular observational quotient. -/
structure ObservationalJoinDoctrine (D : ConditionedMRDTSig) where
  Canon : (Op D.AppOp → Op D.AppOp → Prop) →
    Set (Op D.AppOp) → D.State → Prop
  StateOK : D.State → Prop
  UniverseOK : (Op D.AppOp → Op D.AppOp → Prop) →
    Set (Op D.AppOp) → Prop
  Closed : (Op D.AppOp → Op D.AppOp → Prop) →
    Set (Op D.AppOp) → Prop

def ObservationalJoinAt (D : ConditionedMRDTSig)
    (K : ObservationalJoinDoctrine D) : Prop :=
  ∀ (vis : Op D.AppOp → Op D.AppOp → Prop)
    (events ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    K.UniverseOK vis events →
    K.StateOK s₀ → K.StateOK s₁ → K.StateOK s₂ →
    (∀ {a b c}, vis a b → vis b c → vis a c) →
    (∀ a, ¬ vis a a) →
    (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
    K.Closed vis ev₁ → K.Closed vis ev₂ →
    K.Canon vis (ev₁ ∩ ev₂) s₀ →
    K.Canon vis ev₁ s₁ → K.Canon vis ev₂ s₂ →
    K.Canon vis (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

/-- The exact `EqJoinLemma3C_H` policy, with honesty and timestamp uniqueness
kept together as the universe obligation. -/
def eqHJoinDoctrine (D : ConditionedMRDTSig) (E : EqEquiv D)
    (W : Op D.AppOp → D.State → Prop) (H : List (Op D.AppOp) → Prop)
    (HonJ : (Op D.AppOp → Op D.AppOp → Prop) →
      Set (Op D.AppOp) → Prop) : ObservationalJoinDoctrine D where
  Canon := IsCanonicalStateEqH H E W
  StateOK := D.Inv
  UniverseOK vis events := HonJ vis events ∧
    ∀ a b, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1
  Closed := fullClosureRel

theorem observationalJoinAt_eqH_iff (D : ConditionedMRDTSig) (E : EqEquiv D)
    (W : Op D.AppOp → D.State → Prop) (H : List (Op D.AppOp) → Prop)
    (HonJ : (Op D.AppOp → Op D.AppOp → Prop) →
      Set (Op D.AppOp) → Prop) :
    ObservationalJoinAt D (eqHJoinDoctrine D E W H HonJ) ↔
      EqJoinLemma3C_H D E W H HonJ := by
  constructor
  · intro h vis events ev₁ ev₂ s₀ s₁ s₂ hHon h₀ h₁ h₂ htrans hirr
      huniq hsub₁ hsub₂ hclosed₁ hclosed₂ hcan₀ hcan₁ hcan₂
    exact h vis events ev₁ ev₂ s₀ s₁ s₂ ⟨hHon, huniq⟩ h₀ h₁ h₂
      htrans hirr hsub₁ hsub₂ hclosed₁ hclosed₂ hcan₀ hcan₁ hcan₂
  · intro h vis events ev₁ ev₂ s₀ s₁ s₂ hctx h₀ h₁ h₂ htrans hirr
      hsub₁ hsub₂ hclosed₁ hclosed₂ hcan₀ hcan₁ hcan₂
    exact h vis events ev₁ ev₂ s₀ s₁ s₂ hctx.1 h₀ h₁ h₂ htrans hirr
      hctx.2 hsub₁ hsub₂ hclosed₁ hclosed₂ hcan₀ hcan₁ hcan₂

/-- Named witnesses and their ancestry/output alignment form a distinct Join
doctrine.  Unlike `AbstractJoinDoctrine`, its conclusion must return a witness
and prove coherence with both branches. -/
structure CoherentWitnessJoinDoctrine (D : ConditionedMRDTSig) where
  Witness : Type
  Canon : Sal.Emulation.Configuration D.toCRDTSig →
    Set (Op D.AppOp) → D.State → Witness → Prop
  Align : Witness → Witness → Prop

def CoherentWitnessJoinAt (D : ConditionedMRDTSig)
    (K : CoherentWitnessJoinDoctrine D)
    (C : Sal.Emulation.Configuration D.toCRDTSig) : Prop :=
  ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State)
    (ρ₀ ρ₁ ρ₂ : K.Witness),
    (∀ {a b c}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a, ¬ C.vis a a) →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
    K.Canon C (ev₁ ∩ ev₂) s₀ ρ₀ →
    K.Canon C ev₁ s₁ ρ₁ → K.Canon C ev₂ s₂ ρ₂ →
    K.Align ρ₀ ρ₁ → K.Align ρ₀ ρ₂ →
    ∃ ρm, K.Canon C (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂) ρm ∧
      K.Align ρ₁ ρm ∧ K.Align ρ₂ ρm

def coherentListJoinDoctrine (D : ConditionedMRDTSig)
    (W : List (Op D.AppOp) → Prop)
    (K : List (Op D.AppOp) → List (Op D.AppOp) → Prop) :
    CoherentWitnessJoinDoctrine D where
  Witness := List (Op D.AppOp)
  Canon := IsCanonWitness W
  Align := K

theorem coherentWitnessJoinAt_iff (D : ConditionedMRDTSig)
    (W : List (Op D.AppOp) → Prop)
    (K : List (Op D.AppOp) → List (Op D.AppOp) → Prop)
    (C : Sal.Emulation.Configuration D.toCRDTSig) :
    CoherentWitnessJoinAt D (coherentListJoinDoctrine D W K) C ↔
      JoinLemma3AtWC D W K C := by
  rfl

#print axioms observationalJoinAt_eqH_iff
#print axioms coherentWitnessJoinAt_iff

end Sal.ConditionedMRDTs
