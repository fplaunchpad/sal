import Sal.ConditionedMRDTs.Metatheory.JoinKit
import Sal.ConditionedMRDTs.Metatheory.ArbAdequacyFull

/-!
# Ambient- and arbitration-parametric Join geometry

`JoinKitAt` uses the replica-keyed core because that is the historical API.
Arbitration adequacy uses the full ternary configuration.  This file factors
the geometry above both ambient choices; the adapter theorems prove that no
hypothesis is gained or lost.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

structure AbstractJoinDoctrine (D : ConditionedMRDTSig) where
  Ambient : Type
  vis : Ambient → Op D.AppOp → Op D.AppOp → Prop
  events : Ambient → Set (Op D.AppOp)
  Canon : Ambient → Set (Op D.AppOp) → D.State → Prop

def AbstractJoinAt (D : ConditionedMRDTSig)
    (K : AbstractJoinDoctrine D) (A : K.Ambient) : Prop :=
  ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    (∀ {a b c}, K.vis A a b → K.vis A b c → K.vis A a c) →
    (∀ a, ¬ K.vis A a a) →
    (∀ a ∈ ev₁, a ∈ K.events A) → (∀ a ∈ ev₂, a ∈ K.events A) →
    (∀ a b, K.vis A a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, K.vis A a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
    K.Canon A (ev₁ ∩ ev₂) s₀ →
    K.Canon A ev₁ s₁ → K.Canon A ev₂ s₂ →
    K.Canon A (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

def coreJoinDoctrine (D : ConditionedMRDTSig) : AbstractJoinDoctrine D where
  Ambient := Sal.Emulation.Configuration D.toCRDTSig
  vis C := C.vis
  events C := C.events
  Canon C := IsCanonicalState C

def witnessJoinDoctrine (D : ConditionedMRDTSig)
    (W : List (Op D.AppOp) → Prop) : AbstractJoinDoctrine D where
  Ambient := Sal.Emulation.Configuration D.toCRDTSig
  vis C := C.vis
  events C := C.events
  Canon C := IsCanonicalStateW W C

def arbitrationJoinDoctrine (D : ConditionedMRDTSig)
    (arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop) :
    AbstractJoinDoctrine D where
  Ambient := Configuration D
  vis C := C.vis
  events C := C.events
  Canon C := IsCanonicalStateArb C arb

theorem abstractJoinAt_core_iff (D : ConditionedMRDTSig)
    (C : Sal.Emulation.Configuration D.toCRDTSig) :
    AbstractJoinAt D (coreJoinDoctrine D) C ↔ JoinLemma3At D C := by
  rfl

theorem abstractJoinAt_witness_iff (D : ConditionedMRDTSig)
    (W : List (Op D.AppOp) → Prop)
    (C : Sal.Emulation.Configuration D.toCRDTSig) :
    AbstractJoinAt D (witnessJoinDoctrine D W) C ↔ JoinLemma3AtW D W C := by
  rfl

theorem abstractJoinAt_arb_iff {D : ConditionedMRDTSig}
    (arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop)
    (C : Configuration D) :
    AbstractJoinAt D (arbitrationJoinDoctrine D arb) C ↔
      JoinLemma3AtArb C arb := by
  rfl

#print axioms abstractJoinAt_core_iff
#print axioms abstractJoinAt_witness_iff
#print axioms abstractJoinAt_arb_iff

end Sal.ConditionedMRDTs
