import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.ArbAdequacyReach
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge

/-!
# Increment-Only Counter — flat VC discharge and the conditioned capstone

Split out of the original monolithic `MRDT_Instances.lean`; declarations
verbatim, names unchanged.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## Increment-Only Counter (production mirror:
`Sal/MRDTs/Increment_Only_Counter`; the metatheory's `Counter` toy is this
RDT up to the singleton op type) -/

inductive IOCOp : Type where
  | incr
deriving DecidableEq

def IOC : ConditionedMRDTSig where
  State := Int
  dec_state := inferInstance
  init := 0
  AppOp := IOCOp
  dec_op := inferInstance
  Query := Unit
  Value := Int
  update := fun s _ => s + 1
  merge := fun a b => a + b - (0 : Int)
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b => a + b - l
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem IOC_update_eq (s : Int) (e : Op IOC.AppOp) :
    IOC.update s e = s + 1 := rfl

theorem IOC_mergeL_eq (l a b : Int) : IOC.mergeL l a b = a + b - l := rfl

theorem IOC_init_eq : IOC.init = (0 : Int) := rfl

theorem IOC_rc_either : ∀ o₁ o₂ : Op IOC.AppOp,
    IOC.toCRDTSig.rc o₁ o₂ = RcRes.Either := fun _ _ => rfl

theorem IOC_all_comm : ∀ a b : Op IOC.AppOp, IOC.toCRDTSig.commutes a b :=
  fun _ _ _ => rfl

theorem IOC_updateVCs : UpdateVCs IOC.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (IOC_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [IOC_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [IOC_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [IOC_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem IOC_coreVCs3 : CoreVCs3 IOC := by
  refine ⟨IOC_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    simp only [IOC_mergeL_eq]
    have go : ∀ l' a' b' : Int, a' + b' - l' = b' + a' - l' := by omega
    exact go l a b
  · intro s
    simp only [IOC_mergeL_eq, IOC_init_eq]
    have go : ∀ s' : Int, (0 : Int) + s' - 0 = s' := by omega
    exact go s
  · intro l a b e
    simp only [IOC_update_eq, IOC_mergeL_eq]
    have go : ∀ l' a' b' : Int,
        a' + 1 + (b' + 1) - (l' + 1) = a' + b' - l' + 1 := by omega
    exact go l a b
  · intro a e π₀ π₂ _ _
    simp only [IOC_update_eq, IOC_mergeL_eq]
    have go : ∀ x y z : Int, y + 1 + z - x = y + z - x + 1 := by omega
    exact go _ _ _

theorem IOC_deltaVCs3 : DeltaVCs3 IOC := by
  constructor
  · intro m x₀ x₁ x₂ c
    simp only [IOC_mergeL_eq]
    have go : ∀ m' x₀' x₁' x₂' c' : Int,
        x₁' + c' - m' + (x₂' + c' - m') - (x₀' + c' - m')
          = x₁' + x₂' - x₀' + c' - m' := by omega
    exact go m x₀ x₁ x₂ c
  · intro l m x c y
    simp only [IOC_mergeL_eq]
    have go : ∀ l' m' x' c' y' : Int,
        x' + c' - m' + y' - l' = x' + y' - l' + c' - m' := by omega
    exact go l m x c y

open LabeledTS in
/-- End-to-end RA-linearizability for the production Increment-Only
Counter. -/
theorem ioc_ra_linearizable3
    (C : Configuration IOC)
    (hReach : (labeledTS3 IOC).ReachableFrom
      (initConfig IOC trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_via_capstone IOC_coreVCs3.toCD IOC_coreVCs3.update_core
    (feasibleDeltaVCs3_of_delta IOC_coreVCs3 IOC_deltaVCs3)
    (cdVC3_of_all_comm IOC_coreVCs3 IOC_all_comm) C hReach


/-! ## The conditioned capstone — identity instantiation of the generic framework -/

section
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.FlatGeneric

/-- **Increment-Only Counter over the generic framework.** -/
theorem IOC_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.ConditionedMRDTs.IOC) (WTop Sal.ConditionedMRDTs.IOC)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.IOC)
      (invInvVCTop Sal.ConditionedMRDTs.IOC)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.ConditionedMRDTs.IOC) (WTop Sal.ConditionedMRDTs.IOC)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.IOC)
      (invInvVCTop Sal.ConditionedMRDTs.IOC) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.ConditionedMRDTs.IOC
      Sal.ConditionedMRDTs.IOC_coreVCs3.toCD
      (Sal.ConditionedMRDTs.feasibleDeltaVCs3_of_delta Sal.ConditionedMRDTs.IOC_coreVCs3
        Sal.ConditionedMRDTs.IOC_deltaVCs3)
      (Sal.ConditionedMRDTs.cdVC3_of_all_comm Sal.ConditionedMRDTs.IOC_coreVCs3
        Sal.ConditionedMRDTs.IOC_all_comm) trivial)) C hReach

#print axioms IOC_ra_linearizable3_eq

end

end Sal.ConditionedMRDTs
