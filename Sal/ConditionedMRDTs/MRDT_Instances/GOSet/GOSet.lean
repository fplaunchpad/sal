import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.ArbAdequacyReach
import Sal.ConditionedMRDTs.MRDT_Instances.Common
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge

/-!
# Grow-Only Set: flat VC discharge and the conditioned capstone

The production Grow-Only Set as a `ConditionedMRDTSig`, its RA-linearizability
VC discharge, and the conditioned capstone over the generic framework.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## Grow-Only Set (production mirror: `Sal/MRDTs/Grow_Only_Set`) -/

def goUpdate (s : ℕ → Bool) (o : Op ℕ) : ℕ → Bool :=
  fun x => s x || decide (x = o.2.2)

noncomputable def GOSet : ConditionedMRDTSig where
  State := ℕ → Bool
  dec_state := fun _ _ => Classical.propDecidable _
  init := fun _ => false
  AppOp := ℕ
  dec_op := inferInstance
  Query := Unit
  Value := ℕ → Bool
  update := goUpdate
  merge := fun a b => fun x => false || (a x || b x)
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b => fun x => l x || (a x || b x)
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem GOSet_rc_either : ∀ o₁ o₂ : Op GOSet.AppOp,
    GOSet.toCRDTSig.rc o₁ o₂ = RcRes.Either := fun _ _ => rfl

theorem GOSet_all_comm : ∀ a b : Op GOSet.AppOp,
    GOSet.toCRDTSig.commutes a b := by
  intro a b s
  funext x
  exact bor_rc (s x) (decide (x = a.2.2)) (decide (x = b.2.2))

theorem GOSet_updateVCs : UpdateVCs GOSet.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (GOSet_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [GOSet_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [GOSet_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [GOSet_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem GOSet_coreVCs3 : CoreVCs3 GOSet := by
  refine ⟨GOSet_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    funext x
    exact bor_comm (l x) (a x) (b x)
  · intro s
    funext x
    exact bor_init (s x)
  · intro l a b e
    funext x
    exact bor_0op (l x) (a x) (b x) (decide (x = e.2.2))
  · intro a e π₀ π₂ _ _
    funext x
    exact bor_peel (applySeq GOSet.toCRDTSig GOSet.init π₀ x) (a x)
      (applySeq GOSet.toCRDTSig GOSet.init π₂ x) (decide (x = e.2.2))

theorem GOSet_deltaVCs3 : DeltaVCs3 GOSet := by
  constructor
  · intro m x₀ x₁ x₂ c
    funext x
    exact bor_redis (m x) (x₀ x) (x₁ x) (x₂ x) (c x)
  · intro l m x c y
    funext p
    exact bor_lredis (l p) (m p) (x p) (c p) (y p)

open LabeledTS in
/-- End-to-end RA-linearizability for the production Grow-Only Set. -/
theorem goset_ra_linearizable3
    (C : Configuration GOSet)
    (hReach : (labeledTS3 GOSet).ReachableFrom
      (initConfig GOSet trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_via_capstone GOSet_coreVCs3.toCD GOSet_coreVCs3.update_core
    (feasibleDeltaVCs3_of_delta GOSet_coreVCs3 GOSet_deltaVCs3)
    (cdVC3_of_all_comm GOSet_coreVCs3 GOSet_all_comm) C hReach


/-! ## The conditioned capstone, identity instantiation of the generic framework -/

section
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.FlatGeneric

/-- **Grow-Only Set over the generic framework.** -/
theorem GOSet_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.ConditionedMRDTs.GOSet) (WTop Sal.ConditionedMRDTs.GOSet)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.GOSet)
      (invInvVCTop Sal.ConditionedMRDTs.GOSet)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.ConditionedMRDTs.GOSet) (WTop Sal.ConditionedMRDTs.GOSet)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.GOSet)
      (invInvVCTop Sal.ConditionedMRDTs.GOSet) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.ConditionedMRDTs.GOSet
      Sal.ConditionedMRDTs.GOSet_coreVCs3.toCD
      (Sal.ConditionedMRDTs.feasibleDeltaVCs3_of_delta Sal.ConditionedMRDTs.GOSet_coreVCs3
        Sal.ConditionedMRDTs.GOSet_deltaVCs3)
      (Sal.ConditionedMRDTs.cdVC3_of_all_comm Sal.ConditionedMRDTs.GOSet_coreVCs3
        Sal.ConditionedMRDTs.GOSet_all_comm) trivial)) C hReach

#print axioms GOSet_ra_linearizable3_eq

end

end Sal.ConditionedMRDTs
