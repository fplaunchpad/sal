import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.MRDT_Instances.Common
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge

/-!
# Peritext — flat VC discharge and the conditioned capstone

Split out of the original monolithic `MRDT_Instances.lean`; declarations
verbatim, names unchanged.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## Peritext (production mirror: `Sal/MRDTs/Peritext`) — three grow-only
components (chars, tombstones, anchor-attached marks; `RemoveMark` *adds* a
mark record with `isAdd = false`), `rc = Either`, all pairs commute. -/

/-- Flattened `MarkOp`: `(opId, startId, startSide, endId, endSide,
markType, isAdd)`. -/
abbrev PtMark : Type :=
  (ℕ × ℕ) × (ℕ × ℕ) × Bool × (ℕ × ℕ) × Bool × ℕ × Bool

/-- Flattened `AnchorAttachment`: `(endId, endSide, mark)`. -/
abbrev PtAnchor : Type := (ℕ × ℕ) × Bool × PtMark

/-- Flattened `CharRec`: `(opId, after, ch)`. -/
abbrev PtChar : Type := (ℕ × ℕ) × (ℕ × ℕ) × ℕ

inductive PtOp : Type where
  | insert : ℕ → ℕ × ℕ → PtOp
  | remove : ℕ × ℕ → PtOp
  | addMark : ℕ × ℕ → Bool → ℕ × ℕ → Bool → ℕ → PtOp
  | removeMark : ℕ × ℕ → Bool → ℕ × ℕ → Bool → ℕ → PtOp
deriving DecidableEq

abbrev PtState : Type :=
  (PtChar → Bool) × ((ℕ × ℕ) → Bool) × (PtAnchor → Bool)

noncomputable def ptUpdate (s : PtState) (o : Op PtOp) : PtState :=
  match o.2.2 with
  | .insert ch af =>
      (fun q => s.1 q || decide (q = ((o.1, o.2.1), af, ch)), s.2.1, s.2.2)
  | .remove t =>
      (s.1, fun q => s.2.1 q || decide (q = t), s.2.2)
  | .addMark sI sS eI eS mt =>
      (s.1, s.2.1, fun q =>
        s.2.2 q || decide (q = (eI, eS, ((o.1, o.2.1), sI, sS, eI, eS, mt,
          true))))
  | .removeMark sI sS eI eS mt =>
      (s.1, s.2.1, fun q =>
        s.2.2 q || decide (q = (eI, eS, ((o.1, o.2.1), sI, sS, eI, eS, mt,
          false))))

noncomputable def Peritext : ConditionedMRDTSig where
  State := PtState
  dec_state := fun _ _ => Classical.propDecidable _
  init := (fun _ => false, fun _ => false, fun _ => false)
  AppOp := PtOp
  dec_op := inferInstance
  Query := Unit
  Value := PtState
  update := ptUpdate
  merge := fun a b =>
    (fun q => false || (a.1 q || b.1 q),
     fun q => false || (a.2.1 q || b.2.1 q),
     fun q => false || (a.2.2 q || b.2.2 q))
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b =>
    (fun q => l.1 q || (a.1 q || b.1 q),
     fun q => l.2.1 q || (a.2.1 q || b.2.1 q),
     fun q => l.2.2 q || (a.2.2 q || b.2.2 q))
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem Peritext_rc_either : ∀ o₁ o₂ : Op Peritext.AppOp,
    Peritext.toCRDTSig.rc o₁ o₂ = RcRes.Either := fun _ _ => rfl

theorem Peritext_all_comm : ∀ a b : Op Peritext.AppOp,
    Peritext.toCRDTSig.commutes a b := by
  rintro ⟨tsa, ra, opa⟩ ⟨tsb, rb, opb⟩ s
  cases opa <;> cases opb <;>
    first
      | rfl
      | exact Prod.ext (funext fun q => bor_rc (s.1 q) _ _) rfl
      | exact Prod.ext rfl (Prod.ext (funext fun q => bor_rc (s.2.1 q) _ _)
          rfl)
      | exact Prod.ext rfl (Prod.ext rfl
          (funext fun q => bor_rc (s.2.2 q) _ _))

theorem Peritext_updateVCs : UpdateVCs Peritext.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (Peritext_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [Peritext_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [Peritext_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [Peritext_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem Peritext_coreVCs3 : CoreVCs3 Peritext := by
  refine ⟨Peritext_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    exact Prod.ext (funext fun q => bor_comm (l.1 q) (a.1 q) (b.1 q))
      (Prod.ext (funext fun q => bor_comm (l.2.1 q) (a.2.1 q) (b.2.1 q))
        (funext fun q => bor_comm (l.2.2 q) (a.2.2 q) (b.2.2 q)))
  · intro s
    exact Prod.ext (funext fun q => bor_init (s.1 q))
      (Prod.ext (funext fun q => bor_init (s.2.1 q))
        (funext fun q => bor_init (s.2.2 q)))
  · rintro l a b ⟨ts, r, op⟩
    cases op <;>
      first
        | exact Prod.ext
            (funext fun q => bor_0op (l.1 q) (a.1 q) (b.1 q) _) rfl
        | exact Prod.ext rfl (Prod.ext
            (funext fun q => bor_0op (l.2.1 q) (a.2.1 q) (b.2.1 q) _) rfl)
        | exact Prod.ext rfl (Prod.ext rfl
            (funext fun q => bor_0op (l.2.2 q) (a.2.2 q) (b.2.2 q) _))
  · rintro a ⟨ts, r, op⟩ π₀ π₂ _ _
    cases op <;>
      first
        | exact Prod.ext (funext fun q =>
            bor_peel ((applySeq Peritext.toCRDTSig Peritext.init π₀).1 q)
              (a.1 q)
              ((applySeq Peritext.toCRDTSig Peritext.init π₂).1 q) _) rfl
        | exact Prod.ext rfl (Prod.ext (funext fun q =>
            bor_peel ((applySeq Peritext.toCRDTSig Peritext.init π₀).2.1 q)
              (a.2.1 q)
              ((applySeq Peritext.toCRDTSig Peritext.init π₂).2.1 q) _) rfl)
        | exact Prod.ext rfl (Prod.ext rfl (funext fun q =>
            bor_peel ((applySeq Peritext.toCRDTSig Peritext.init π₀).2.2 q)
              (a.2.2 q)
              ((applySeq Peritext.toCRDTSig Peritext.init π₂).2.2 q) _))

theorem Peritext_deltaVCs3 : DeltaVCs3 Peritext := by
  constructor
  · intro m x₀ x₁ x₂ c
    exact Prod.ext
      (funext fun q => bor_redis (m.1 q) (x₀.1 q) (x₁.1 q) (x₂.1 q) (c.1 q))
      (Prod.ext
        (funext fun q =>
          bor_redis (m.2.1 q) (x₀.2.1 q) (x₁.2.1 q) (x₂.2.1 q) (c.2.1 q))
        (funext fun q =>
          bor_redis (m.2.2 q) (x₀.2.2 q) (x₁.2.2 q) (x₂.2.2 q) (c.2.2 q)))
  · intro l m x c y
    exact Prod.ext
      (funext fun q => bor_lredis (l.1 q) (m.1 q) (x.1 q) (c.1 q) (y.1 q))
      (Prod.ext
        (funext fun q =>
          bor_lredis (l.2.1 q) (m.2.1 q) (x.2.1 q) (c.2.1 q) (y.2.1 q))
        (funext fun q =>
          bor_lredis (l.2.2 q) (m.2.2 q) (x.2.2 q) (c.2.2 q) (y.2.2 q)))

open LabeledTS in
/-- End-to-end RA-linearizability for the production Peritext. -/
theorem peritext_ra_linearizable3
    (C : Configuration Peritext)
    (hReach : (labeledTS3 Peritext).ReachableFrom
      (initConfig Peritext trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable_of_core_delta_cd3 Peritext_coreVCs3 Peritext_deltaVCs3
    (cdVC3_of_all_comm Peritext_coreVCs3 Peritext_all_comm) C hReach


/-! ## The conditioned capstone — identity instantiation of the generic framework -/

section
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.FlatGeneric

/-- **Peritext over the generic framework.** -/
theorem Peritext_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.ConditionedMRDTs.Peritext) (WTop Sal.ConditionedMRDTs.Peritext)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.Peritext)
      (invInvVCTop Sal.ConditionedMRDTs.Peritext)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.ConditionedMRDTs.Peritext) (WTop Sal.ConditionedMRDTs.Peritext)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.Peritext)
      (invInvVCTop Sal.ConditionedMRDTs.Peritext) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.ConditionedMRDTs.Peritext
      Sal.ConditionedMRDTs.Peritext_coreVCs3.toCD
      (Sal.ConditionedMRDTs.feasibleDeltaVCs3_of_delta Sal.ConditionedMRDTs.Peritext_coreVCs3
        Sal.ConditionedMRDTs.Peritext_deltaVCs3)
      (Sal.ConditionedMRDTs.cdVC3_of_all_comm Sal.ConditionedMRDTs.Peritext_coreVCs3
        Sal.ConditionedMRDTs.Peritext_all_comm) trivial)) C hReach

#print axioms Peritext_ra_linearizable3_eq

end

end Sal.ConditionedMRDTs
