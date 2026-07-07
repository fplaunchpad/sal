import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.MRDT_Instances.Common
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge

/-!
# RGA (tombstone-based) — flat VC discharge and the conditioned capstone

Split out of the original monolithic `MRDT_Instances.lean`; declarations
verbatim, names unchanged.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## RGA, tombstone-based (production mirror: `Sal/MRDTs/RGA`) —
Tier-1 in disguise: both components grow-only, `rc = Either`, all pairs
commute, LCA-inclusive union merge. -/

inductive RGAOp : Type where
  | addAfter : ℕ → ℕ → RGAOp
  | remove : ℕ → RGAOp
deriving DecidableEq

def rgaUpdate (s : ((ℕ × ℕ × ℕ) → Bool) × (ℕ → Bool)) (o : Op RGAOp) :
    ((ℕ × ℕ × ℕ) → Bool) × (ℕ → Bool) :=
  match o.2.2 with
  | .addAfter af el => (fun p => s.1 p || decide (p = (o.1, af, el)), s.2)
  | .remove id => (s.1, fun x => s.2 x || decide (x = id))

noncomputable def RGAM : ConditionedMRDTSig where
  State := ((ℕ × ℕ × ℕ) → Bool) × (ℕ → Bool)
  dec_state := fun _ _ => Classical.propDecidable _
  init := (fun _ => false, fun _ => false)
  AppOp := RGAOp
  dec_op := inferInstance
  Query := Unit
  Value := ((ℕ × ℕ × ℕ) → Bool) × (ℕ → Bool)
  update := rgaUpdate
  merge := fun a b =>
    (fun p => false || (a.1 p || b.1 p), fun x => false || (a.2 x || b.2 x))
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b =>
    (fun p => l.1 p || (a.1 p || b.1 p), fun x => l.2 x || (a.2 x || b.2 x))
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem RGAM_rc_either : ∀ o₁ o₂ : Op RGAM.AppOp,
    RGAM.toCRDTSig.rc o₁ o₂ = RcRes.Either := fun _ _ => rfl

theorem RGAM_all_comm : ∀ a b : Op RGAM.AppOp,
    RGAM.toCRDTSig.commutes a b := by
  rintro ⟨tsa, ra, opa⟩ ⟨tsb, rb, opb⟩ s
  cases opa <;> cases opb
  · exact Prod.ext (funext fun p => bor_rc (s.1 p) _ _) rfl
  · rfl
  · rfl
  · exact Prod.ext rfl (funext fun x => bor_rc (s.2 x) _ _)

theorem RGAM_updateVCs : UpdateVCs RGAM.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (RGAM_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [RGAM_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [RGAM_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [RGAM_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem RGAM_coreVCs3 : CoreVCs3 RGAM := by
  refine ⟨RGAM_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    exact Prod.ext (funext fun p => bor_comm (l.1 p) (a.1 p) (b.1 p))
      (funext fun x => bor_comm (l.2 x) (a.2 x) (b.2 x))
  · intro s
    exact Prod.ext (funext fun p => bor_init (s.1 p))
      (funext fun x => bor_init (s.2 x))
  · rintro l a b ⟨ts, r, op⟩
    cases op with
    | addAfter af el =>
      exact Prod.ext (funext fun p => bor_0op (l.1 p) (a.1 p) (b.1 p) _) rfl
    | remove id =>
      exact Prod.ext rfl (funext fun x => bor_0op (l.2 x) (a.2 x) (b.2 x) _)
  · rintro a ⟨ts, r, op⟩ π₀ π₂ _ _
    cases op with
    | addAfter af el =>
      exact Prod.ext (funext fun p =>
        bor_peel ((applySeq RGAM.toCRDTSig RGAM.init π₀).1 p) (a.1 p)
          ((applySeq RGAM.toCRDTSig RGAM.init π₂).1 p) _) rfl
    | remove id =>
      exact Prod.ext rfl (funext fun x =>
        bor_peel ((applySeq RGAM.toCRDTSig RGAM.init π₀).2 x) (a.2 x)
          ((applySeq RGAM.toCRDTSig RGAM.init π₂).2 x) _)

theorem RGAM_deltaVCs3 : DeltaVCs3 RGAM := by
  constructor
  · intro m x₀ x₁ x₂ c
    exact Prod.ext
      (funext fun p => bor_redis (m.1 p) (x₀.1 p) (x₁.1 p) (x₂.1 p) (c.1 p))
      (funext fun x => bor_redis (m.2 x) (x₀.2 x) (x₁.2 x) (x₂.2 x) (c.2 x))
  · intro l m x c y
    exact Prod.ext
      (funext fun p => bor_lredis (l.1 p) (m.1 p) (x.1 p) (c.1 p) (y.1 p))
      (funext fun q => bor_lredis (l.2 q) (m.2 q) (x.2 q) (c.2 q) (y.2 q))

open LabeledTS in
/-- End-to-end RA-linearizability for the production tombstone RGA. -/
theorem rga_ra_linearizable3
    (C : Configuration RGAM)
    (hReach : (labeledTS3 RGAM).ReachableFrom
      (initConfig RGAM trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable_of_core_delta_cd3 RGAM_coreVCs3 RGAM_deltaVCs3
    (cdVC3_of_all_comm RGAM_coreVCs3 RGAM_all_comm) C hReach


/-! ## The conditioned capstone — identity instantiation of the generic framework -/

section
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.FlatGeneric

/-- **Tombstone RGA over the generic framework.** -/
theorem RGAM_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.ConditionedMRDTs.RGAM) (WTop Sal.ConditionedMRDTs.RGAM)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.RGAM)
      (invInvVCTop Sal.ConditionedMRDTs.RGAM)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.ConditionedMRDTs.RGAM) (WTop Sal.ConditionedMRDTs.RGAM)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.RGAM)
      (invInvVCTop Sal.ConditionedMRDTs.RGAM) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.ConditionedMRDTs.RGAM
      Sal.ConditionedMRDTs.RGAM_coreVCs3.toCD
      (Sal.ConditionedMRDTs.feasibleDeltaVCs3_of_delta Sal.ConditionedMRDTs.RGAM_coreVCs3
        Sal.ConditionedMRDTs.RGAM_deltaVCs3)
      (Sal.ConditionedMRDTs.cdVC3_of_all_comm Sal.ConditionedMRDTs.RGAM_coreVCs3
        Sal.ConditionedMRDTs.RGAM_all_comm) trivial)) C hReach

#print axioms RGAM_ra_linearizable3_eq

end

end Sal.ConditionedMRDTs
