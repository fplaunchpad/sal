import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.ArbAdequacyReach
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge

/-!
# PN-Counter: flat VC discharge and the conditioned capstone

The production PN-Counter as a `ConditionedMRDTSig`, its RA-linearizability VC
discharge, and the conditioned capstone over the generic framework.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## PN-Counter (production mirror: `Sal/MRDTs/PN_Counter`) -/

inductive PNOp : Type where
  | inc
  | dec
deriving DecidableEq

def pnUpdate (s : Int) (o : Op PNOp) : Int :=
  match o.2.2 with
  | .inc => s + 1
  | .dec => s - 1

def PN : ConditionedMRDTSig where
  State := Int
  dec_state := inferInstance
  init := 0
  AppOp := PNOp
  dec_op := inferInstance
  Query := Unit
  Value := Int
  update := pnUpdate
  merge := fun a b => a + b - (0 : Int)
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b => a + b - l
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem PN_update_inc (s : Int) (ts r : ℕ) :
    PN.update s (ts, r, PNOp.inc) = s + 1 := rfl

theorem PN_update_dec (s : Int) (ts r : ℕ) :
    PN.update s (ts, r, PNOp.dec) = s - 1 := rfl

theorem PN_mergeL_eq (l a b : Int) : PN.mergeL l a b = a + b - l := rfl

theorem PN_init_eq : PN.init = (0 : Int) := rfl

theorem PN_rc_either : ∀ o₁ o₂ : Op PN.AppOp,
    PN.toCRDTSig.rc o₁ o₂ = RcRes.Either := fun _ _ => rfl

theorem PN_all_comm : ∀ a b : Op PN.AppOp, PN.toCRDTSig.commutes a b := by
  rintro ⟨tsa, ra, opa⟩ ⟨tsb, rb, opb⟩ s
  have go1 : ∀ x : Int, x + 1 - 1 = x - 1 + 1 := by omega
  have go2 : ∀ x : Int, x - 1 + 1 = x + 1 - 1 := by omega
  cases opa <;> cases opb
  · rfl
  · exact go1 s
  · exact go2 s
  · rfl

theorem PN_updateVCs : UpdateVCs PN.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (PN_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [PN_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [PN_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [PN_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem PN_coreVCs3 : CoreVCs3 PN := by
  refine ⟨PN_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    simp only [PN_mergeL_eq]
    have go : ∀ l' a' b' : Int, a' + b' - l' = b' + a' - l' := by omega
    exact go l a b
  · intro s
    simp only [PN_mergeL_eq, PN_init_eq]
    have go : ∀ s' : Int, (0 : Int) + s' - 0 = s' := by omega
    exact go s
  · rintro l a b ⟨ts, r, op⟩
    have goi : ∀ l' a' b' : Int,
        a' + 1 + (b' + 1) - (l' + 1) = a' + b' - l' + 1 := by omega
    have god : ∀ l' a' b' : Int,
        a' - 1 + (b' - 1) - (l' - 1) = a' + b' - l' - 1 := by omega
    cases op
    · exact goi l a b
    · exact god l a b
  · rintro a ⟨ts, r, op⟩ π₀ π₂ _ _
    have goi : ∀ x y z : Int, y + 1 + z - x = y + z - x + 1 := by omega
    have god : ∀ x y z : Int, y - 1 + z - x = y + z - x - 1 := by omega
    cases op
    · exact goi _ a _
    · exact god _ a _

theorem PN_deltaVCs3 : DeltaVCs3 PN := by
  constructor
  · intro m x₀ x₁ x₂ c
    simp only [PN_mergeL_eq]
    have go : ∀ m' x₀' x₁' x₂' c' : Int,
        x₁' + c' - m' + (x₂' + c' - m') - (x₀' + c' - m')
          = x₁' + x₂' - x₀' + c' - m' := by omega
    exact go m x₀ x₁ x₂ c
  · intro l m x c y
    simp only [PN_mergeL_eq]
    have go : ∀ l' m' x' c' y' : Int,
        x' + c' - m' + y' - l' = x' + y' - l' + c' - m' := by omega
    exact go l m x c y

open LabeledTS in
/-- End-to-end RA-linearizability for the production PN-Counter. -/
theorem pn_ra_linearizable3
    (C : Configuration PN)
    (hReach : (labeledTS3 PN).ReachableFrom
      (initConfig PN trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_via_capstone PN_coreVCs3.toCD PN_coreVCs3.update_core
    (feasibleDeltaVCs3_of_delta PN_coreVCs3 PN_deltaVCs3)
    (cdVC3_of_all_comm PN_coreVCs3 PN_all_comm) C hReach


/-! ## The conditioned capstone, identity instantiation of the generic framework -/

section
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.FlatGeneric

/-- **PN-Counter over the generic framework.** -/
theorem PN_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.ConditionedMRDTs.PN) (WTop Sal.ConditionedMRDTs.PN)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.PN)
      (invInvVCTop Sal.ConditionedMRDTs.PN)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.ConditionedMRDTs.PN) (WTop Sal.ConditionedMRDTs.PN)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.PN)
      (invInvVCTop Sal.ConditionedMRDTs.PN) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.ConditionedMRDTs.PN
      Sal.ConditionedMRDTs.PN_coreVCs3.toCD
      (Sal.ConditionedMRDTs.feasibleDeltaVCs3_of_delta Sal.ConditionedMRDTs.PN_coreVCs3
        Sal.ConditionedMRDTs.PN_deltaVCs3)
      (Sal.ConditionedMRDTs.cdVC3_of_all_comm Sal.ConditionedMRDTs.PN_coreVCs3
        Sal.ConditionedMRDTs.PN_all_comm) trivial)) C hReach

#print axioms PN_ra_linearizable3_eq

end

end Sal.ConditionedMRDTs
