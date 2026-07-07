import Sal.MRDTs.Metatheory.MRDT_Instances
import Sal.MRDTs.Metatheory.Conditioned.FlatGeneric_Bridge

/-!
# The nine flat production MRDTs, over the generic conditioned framework

*Additive; 0 `sorry`.*

**All twelve production instances now stand on the one framework.** Each flat MRDT's existing
closure-indexed Join Lemma (the same `ConditionedContract` data its `_adequate_viaContract`
theorem routes through — no VC re-proved) is fed to the flat collapse
(`FlatGeneric.flat_ra_linearizable3_eq`), instantiating the generic conditioned metatheorem
`RA_linearizable_up_to_eq_H` at the identity observational equivalence: `≈ := =`,
`Inv = applicable = W = ⊤`, witness discipline `H = ⊤`.  The conclusion is
`IsRALinearizable3Eq` over the quotient ternary system — the same statement shape, through the
same theorem, as the tombstone-free RGA's `rga_tombstone_free_ra_linearizable3_eq`; only the
instantiation parameters differ.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.Metatheory.MRDTInstancesGeneric

open Sal.Emulation
open Sal.Metatheory.GenericEqQuotient
open Sal.Metatheory.GoodConfig3H
open Sal.Metatheory.FlatGeneric
open Sal.Metatheory (Configuration initConfig labeledTS3 JoinLemma3C fullClosure
  ConditionedContract)

/-- The full-closure Join Lemma bundled in any contract (`anti` along
`closure_below_full`). -/
def contractJoinFull (c : ConditionedContract) :
    JoinLemma3C c.D (Sal.Metatheory.fullClosure c.D.toCRDTSig) :=
  Sal.Metatheory.JoinLemma3C.anti c.closure_below_full c.join

/-- **OR-Set over the generic framework.** -/
theorem ORSet_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.Metatheory.ORSet) (WTop Sal.Metatheory.ORSet)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.ORSet)
      (invInvVCTop Sal.Metatheory.ORSet)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.Metatheory.ORSet) (WTop Sal.Metatheory.ORSet)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.ORSet)
      (invInvVCTop Sal.Metatheory.ORSet) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.Metatheory.ORSet
      Sal.Metatheory.ORSet_coreVCs3CD Sal.Metatheory.ORSet_feasibleDeltaVCs3
      Sal.Metatheory.ORSet_cdVC3 trivial)) C hReach

/-- **OR-Set-efficient over the generic framework.** -/
theorem ORSetE_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.Metatheory.ORSetE) (WTop Sal.Metatheory.ORSetE)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.ORSetE)
      (invInvVCTop Sal.Metatheory.ORSetE)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.Metatheory.ORSetE) (WTop Sal.Metatheory.ORSetE)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.ORSetE)
      (invInvVCTop Sal.Metatheory.ORSetE) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.Metatheory.ORSetE
      Sal.Metatheory.ORSetE_coreVCs3CD Sal.Metatheory.ORSetE_feasibleDeltaVCs3
      Sal.Metatheory.ORSetE_cdVC3 trivial)) C hReach

/-- **Enable-wins flag over the generic framework** (full-closure corner). -/
theorem EWFlag_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.Metatheory.EWFlag) (WTop Sal.Metatheory.EWFlag)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.EWFlag)
      (invInvVCTop Sal.Metatheory.EWFlag)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.Metatheory.EWFlag) (WTop Sal.Metatheory.EWFlag)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.EWFlag)
      (invInvVCTop Sal.Metatheory.EWFlag) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofJoinF Sal.Metatheory.EWFlag
      Sal.Metatheory.EWFlag_joinLemma3F trivial)) C hReach

/-- **Grow-Only Set over the generic framework.** -/
theorem GOSet_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.Metatheory.GOSet) (WTop Sal.Metatheory.GOSet)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.GOSet)
      (invInvVCTop Sal.Metatheory.GOSet)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.Metatheory.GOSet) (WTop Sal.Metatheory.GOSet)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.GOSet)
      (invInvVCTop Sal.Metatheory.GOSet) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.Metatheory.GOSet
      Sal.Metatheory.GOSet_coreVCs3.toCD
      (Sal.Metatheory.feasibleDeltaVCs3_of_delta Sal.Metatheory.GOSet_coreVCs3
        Sal.Metatheory.GOSet_deltaVCs3)
      (Sal.Metatheory.cdVC3_of_all_comm Sal.Metatheory.GOSet_coreVCs3
        Sal.Metatheory.GOSet_all_comm) trivial)) C hReach

/-- **Grow-Only Map over the generic framework.** -/
theorem GOMap_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.Metatheory.GOMap) (WTop Sal.Metatheory.GOMap)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.GOMap)
      (invInvVCTop Sal.Metatheory.GOMap)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.Metatheory.GOMap) (WTop Sal.Metatheory.GOMap)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.GOMap)
      (invInvVCTop Sal.Metatheory.GOMap) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.Metatheory.GOMap
      Sal.Metatheory.GOMap_coreVCs3.toCD
      (Sal.Metatheory.feasibleDeltaVCs3_of_delta Sal.Metatheory.GOMap_coreVCs3
        Sal.Metatheory.GOMap_deltaVCs3)
      (Sal.Metatheory.cdVC3_of_all_comm Sal.Metatheory.GOMap_coreVCs3
        Sal.Metatheory.GOMap_all_comm) trivial)) C hReach

/-- **Increment-Only Counter over the generic framework.** -/
theorem IOC_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.Metatheory.IOC) (WTop Sal.Metatheory.IOC)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.IOC)
      (invInvVCTop Sal.Metatheory.IOC)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.Metatheory.IOC) (WTop Sal.Metatheory.IOC)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.IOC)
      (invInvVCTop Sal.Metatheory.IOC) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.Metatheory.IOC
      Sal.Metatheory.IOC_coreVCs3.toCD
      (Sal.Metatheory.feasibleDeltaVCs3_of_delta Sal.Metatheory.IOC_coreVCs3
        Sal.Metatheory.IOC_deltaVCs3)
      (Sal.Metatheory.cdVC3_of_all_comm Sal.Metatheory.IOC_coreVCs3
        Sal.Metatheory.IOC_all_comm) trivial)) C hReach

/-- **PN-Counter over the generic framework.** -/
theorem PN_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.Metatheory.PN) (WTop Sal.Metatheory.PN)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.PN)
      (invInvVCTop Sal.Metatheory.PN)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.Metatheory.PN) (WTop Sal.Metatheory.PN)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.PN)
      (invInvVCTop Sal.Metatheory.PN) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.Metatheory.PN
      Sal.Metatheory.PN_coreVCs3.toCD
      (Sal.Metatheory.feasibleDeltaVCs3_of_delta Sal.Metatheory.PN_coreVCs3
        Sal.Metatheory.PN_deltaVCs3)
      (Sal.Metatheory.cdVC3_of_all_comm Sal.Metatheory.PN_coreVCs3
        Sal.Metatheory.PN_all_comm) trivial)) C hReach

/-- **Tombstone RGA over the generic framework.** -/
theorem RGAM_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.Metatheory.RGAM) (WTop Sal.Metatheory.RGAM)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.RGAM)
      (invInvVCTop Sal.Metatheory.RGAM)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.Metatheory.RGAM) (WTop Sal.Metatheory.RGAM)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.RGAM)
      (invInvVCTop Sal.Metatheory.RGAM) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.Metatheory.RGAM
      Sal.Metatheory.RGAM_coreVCs3.toCD
      (Sal.Metatheory.feasibleDeltaVCs3_of_delta Sal.Metatheory.RGAM_coreVCs3
        Sal.Metatheory.RGAM_deltaVCs3)
      (Sal.Metatheory.cdVC3_of_all_comm Sal.Metatheory.RGAM_coreVCs3
        Sal.Metatheory.RGAM_all_comm) trivial)) C hReach

/-- **Peritext over the generic framework.** -/
theorem Peritext_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.Metatheory.Peritext) (WTop Sal.Metatheory.Peritext)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.Peritext)
      (invInvVCTop Sal.Metatheory.Peritext)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.Metatheory.Peritext) (WTop Sal.Metatheory.Peritext)
      (invPresTop fun _ => trivial) (congVCEq Sal.Metatheory.Peritext)
      (invInvVCTop Sal.Metatheory.Peritext) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.Metatheory.Peritext
      Sal.Metatheory.Peritext_coreVCs3.toCD
      (Sal.Metatheory.feasibleDeltaVCs3_of_delta Sal.Metatheory.Peritext_coreVCs3
        Sal.Metatheory.Peritext_deltaVCs3)
      (Sal.Metatheory.cdVC3_of_all_comm Sal.Metatheory.Peritext_coreVCs3
        Sal.Metatheory.Peritext_all_comm) trivial)) C hReach

/-! ## Axiom audit -/

#print axioms ORSet_ra_linearizable3_eq
#print axioms ORSetE_ra_linearizable3_eq
#print axioms EWFlag_ra_linearizable3_eq
#print axioms GOSet_ra_linearizable3_eq
#print axioms GOMap_ra_linearizable3_eq
#print axioms IOC_ra_linearizable3_eq
#print axioms PN_ra_linearizable3_eq
#print axioms RGAM_ra_linearizable3_eq
#print axioms Peritext_ra_linearizable3_eq

end Sal.Metatheory.MRDTInstancesGeneric
