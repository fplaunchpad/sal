import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.MRDT_Instances.Common
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge

/-!
# Grow-Only Map — flat VC discharge and the conditioned capstone

Split out of the original monolithic `MRDT_Instances.lean`; declarations
verbatim, names unchanged.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## Grow-Only Map (production mirror: `Sal/MRDTs/Grow_Only_Map`;
uncurried `mysel`-view: `(key, value)`-membership) -/

def gomUpdate (s : ℕ × ℕ → Bool) (o : Op (ℕ × ℕ)) : ℕ × ℕ → Bool :=
  fun p => s p || decide (p = o.2.2)

noncomputable def GOMap : ConditionedMRDTSig where
  State := ℕ × ℕ → Bool
  dec_state := fun _ _ => Classical.propDecidable _
  init := fun _ => false
  AppOp := ℕ × ℕ
  dec_op := inferInstance
  Query := Unit
  Value := ℕ × ℕ → Bool
  update := gomUpdate
  merge := fun a b => fun p => false || (a p || b p)
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b => fun p => l p || (a p || b p)
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem GOMap_rc_either : ∀ o₁ o₂ : Op GOMap.AppOp,
    GOMap.toCRDTSig.rc o₁ o₂ = RcRes.Either := fun _ _ => rfl

theorem GOMap_all_comm : ∀ a b : Op GOMap.AppOp,
    GOMap.toCRDTSig.commutes a b := by
  intro a b s
  funext p
  exact bor_rc (s p) (decide (p = a.2.2)) (decide (p = b.2.2))

theorem GOMap_updateVCs : UpdateVCs GOMap.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (GOMap_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [GOMap_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [GOMap_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [GOMap_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem GOMap_coreVCs3 : CoreVCs3 GOMap := by
  refine ⟨GOMap_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    funext p
    exact bor_comm (l p) (a p) (b p)
  · intro s
    funext p
    exact bor_init (s p)
  · intro l a b e
    funext p
    exact bor_0op (l p) (a p) (b p) (decide (p = e.2.2))
  · intro a e π₀ π₂ _ _
    funext p
    exact bor_peel (applySeq GOMap.toCRDTSig GOMap.init π₀ p) (a p)
      (applySeq GOMap.toCRDTSig GOMap.init π₂ p) (decide (p = e.2.2))

theorem GOMap_deltaVCs3 : DeltaVCs3 GOMap := by
  constructor
  · intro m x₀ x₁ x₂ c
    funext p
    exact bor_redis (m p) (x₀ p) (x₁ p) (x₂ p) (c p)
  · intro l m x c y
    funext p
    exact bor_lredis (l p) (m p) (x p) (c p) (y p)

open LabeledTS in
/-- End-to-end RA-linearizability for the production Grow-Only Map. -/
theorem gomap_ra_linearizable3
    (C : Configuration GOMap)
    (hReach : (labeledTS3 GOMap).ReachableFrom
      (initConfig GOMap trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable_of_core_delta_cd3 GOMap_coreVCs3 GOMap_deltaVCs3
    (cdVC3_of_all_comm GOMap_coreVCs3 GOMap_all_comm) C hReach


/-! ## The conditioned capstone — identity instantiation of the generic framework -/

section
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.FlatGeneric

/-- **Grow-Only Map over the generic framework.** -/
theorem GOMap_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.ConditionedMRDTs.GOMap) (WTop Sal.ConditionedMRDTs.GOMap)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.GOMap)
      (invInvVCTop Sal.ConditionedMRDTs.GOMap)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.ConditionedMRDTs.GOMap) (WTop Sal.ConditionedMRDTs.GOMap)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.GOMap)
      (invInvVCTop Sal.ConditionedMRDTs.GOMap) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.ConditionedMRDTs.GOMap
      Sal.ConditionedMRDTs.GOMap_coreVCs3.toCD
      (Sal.ConditionedMRDTs.feasibleDeltaVCs3_of_delta Sal.ConditionedMRDTs.GOMap_coreVCs3
        Sal.ConditionedMRDTs.GOMap_deltaVCs3)
      (Sal.ConditionedMRDTs.cdVC3_of_all_comm Sal.ConditionedMRDTs.GOMap_coreVCs3
        Sal.ConditionedMRDTs.GOMap_all_comm) trivial)) C hReach

#print axioms GOMap_ra_linearizable3_eq

end

end Sal.ConditionedMRDTs
