import Sal.MRDTs.Metatheory.Adequacy

/-! Native bounded-counter convergence over the plain MRDT semantics. -/


set_option maxHeartbeats 1000000

namespace Sal.MRDTs.Instances.BoundedCounter

open Sal.MRDTs.Foundation
open Classical

/-! ## §1  The mirror -/

inductive BCOp : Type where
  | inc
  | dec
deriving DecidableEq

abbrev BCState : Type := (ℕ → ℤ) × (ℕ → ℤ)

/-- Bump `f` at slot `r`. -/
def bcBump (f : ℕ → ℤ) (r : ℕ) : ℕ → ℤ := fun k => if k = r then f k + 1 else f k

def bcUpdate (s : BCState) (o : Op BCOp) : BCState :=
  match o.2.2 with
  | .inc => (bcBump s.1 o.2.1, s.2)
  | .dec => (s.1, bcBump s.2 o.2.1)

def bcMergeL (l a b : BCState) : BCState :=
  (fun k => a.1 k + b.1 k - l.1 k, fun k => a.2 k + b.2 k - l.2 k)

noncomputable def BC : MRDTSig where
  State := BCState
  dec_state := fun a b => Classical.propDecidable (a = b)
  init := (fun _ => 0, fun _ => 0)
  AppOp := BCOp
  dec_op := inferInstance
  Query := ℕ
  Value := ℤ
  update := bcUpdate
  merge := fun a b => bcMergeL (fun _ => 0, fun _ => 0) a b
  query := fun s r => s.1 r - s.2 r
  rc := fun _ _ => RcRes.Either
  mergeL := bcMergeL
  merge_init_slice := fun _ _ => rfl

/-! Component-level reduction lemmas: everything downstream is `omega` on
these. -/

theorem bcBump_apply (f : ℕ → ℤ) (r k : ℕ) :
    bcBump f r k = f k + (if k = r then 1 else 0) := by
  by_cases h : k = r <;> simp [bcBump, h]

theorem bcUpdate_inc_fst (s : BCState) (ts r k : ℕ) :
    (bcUpdate s (ts, r, BCOp.inc)).1 k = s.1 k + (if k = r then 1 else 0) := by
  by_cases h : k = r <;> simp [bcUpdate, bcBump, h]

theorem bcUpdate_inc_snd (s : BCState) (ts r k : ℕ) :
    (bcUpdate s (ts, r, BCOp.inc)).2 k = s.2 k := rfl

theorem bcUpdate_dec_fst (s : BCState) (ts r k : ℕ) :
    (bcUpdate s (ts, r, BCOp.dec)).1 k = s.1 k := rfl

theorem bcUpdate_dec_snd (s : BCState) (ts r k : ℕ) :
    (bcUpdate s (ts, r, BCOp.dec)).2 k = s.2 k + (if k = r then 1 else 0) := by
  by_cases h : k = r <;> simp [bcUpdate, bcBump, h]

theorem bcMergeL_fst (l a b : BCState) (k : ℕ) :
    (bcMergeL l a b).1 k = a.1 k + b.1 k - l.1 k := rfl

theorem bcMergeL_snd (l a b : BCState) (k : ℕ) :
    (bcMergeL l a b).2 k = a.2 k + b.2 k - l.2 k := rfl

theorem BC_update_eq (s : BCState) (o : Op BCOp) :
    BC.update s o = bcUpdate s o := rfl

theorem BC_mergeL_eq (l a b : BCState) : BC.mergeL l a b = bcMergeL l a b := rfl

theorem BC_init_fst (k : ℕ) : BC.init.1 k = 0 := rfl

theorem BC_init_snd (k : ℕ) : BC.init.2 k = 0 := rfl

theorem BC_rc_either : ∀ o₁ o₂ : Op BC.AppOp,
    BC.toCRDTSig.rc o₁ o₂ = RcRes.Either := fun _ _ => rfl

/-- Two `BCState`s with equal slot values are equal. -/
theorem bcState_ext {s t : BCState}
    (h1 : ∀ k, s.1 k = t.1 k) (h2 : ∀ k, s.2 k = t.2 k) : s = t := by
  obtain ⟨s1, s2⟩ := s
  obtain ⟨t1, t2⟩ := t
  simp only [Prod.mk.injEq]
  exact ⟨funext h1, funext h2⟩

/-! ## §2  The flat discharge (the PN-Counter's route, pointwise) -/

theorem BC_all_comm : ∀ a b : Op BC.AppOp, BC.toCRDTSig.commutes a b := by
  rintro ⟨tsa, ra, opa⟩ ⟨tsb, rb, opb⟩ s
  show bcUpdate (bcUpdate s (tsa, ra, opa)) (tsb, rb, opb)
      = bcUpdate (bcUpdate s (tsb, rb, opb)) (tsa, ra, opa)
  cases opa <;> cases opb <;>
    refine bcState_ext (fun k => ?_) (fun k => ?_) <;>
    simp only [bcUpdate_inc_fst, bcUpdate_inc_snd, bcUpdate_dec_fst,
      bcUpdate_dec_snd] <;>
    split_ifs <;> omega

theorem BC_updateVCs : UpdateVCs BC.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (BC_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [BC_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [BC_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [BC_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem BC_coreVCs3 : CoreVCs3 BC := by
  refine ⟨BC_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    refine bcState_ext (fun k => ?_) (fun k => ?_) <;>
      simp only [BC_mergeL_eq, bcMergeL_fst, bcMergeL_snd] <;> omega
  · intro s
    refine bcState_ext (fun k => ?_) (fun k => ?_) <;>
      simp only [BC_mergeL_eq, bcMergeL_fst, bcMergeL_snd, BC_init_fst,
        BC_init_snd] <;> omega
  · rintro l a b ⟨ts, r, op⟩
    show bcMergeL (bcUpdate l (ts, r, op)) (bcUpdate a (ts, r, op))
        (bcUpdate b (ts, r, op)) = bcUpdate (bcMergeL l a b) (ts, r, op)
    cases op <;>
      refine bcState_ext (fun k => ?_) (fun k => ?_) <;>
      simp only [bcMergeL_fst, bcMergeL_snd,
        bcUpdate_inc_fst, bcUpdate_inc_snd, bcUpdate_dec_fst,
        bcUpdate_dec_snd] <;>
      omega
  · rintro a ⟨ts, r, op⟩ π₀ π₂ _ _
    generalize applySeq BC.toCRDTSig BC.init π₀ = X
    generalize applySeq BC.toCRDTSig BC.init π₂ = Y
    show bcMergeL X (bcUpdate a (ts, r, op)) Y
        = bcUpdate (bcMergeL X a Y) (ts, r, op)
    cases op <;>
      refine bcState_ext (fun k => ?_) (fun k => ?_) <;>
      simp only [bcMergeL_fst, bcMergeL_snd,
        bcUpdate_inc_fst, bcUpdate_inc_snd, bcUpdate_dec_fst,
        bcUpdate_dec_snd] <;>
      omega

theorem BC_deltaVCs3 : DeltaVCs3 BC := by
  constructor
  · intro m x₀ x₁ x₂ c
    refine bcState_ext (fun k => ?_) (fun k => ?_) <;>
      simp only [BC_mergeL_eq, bcMergeL_fst, bcMergeL_snd] <;> omega
  · intro l m x c y
    refine bcState_ext (fun k => ?_) (fun k => ?_) <;>
      simp only [BC_mergeL_eq, bcMergeL_fst, bcMergeL_snd] <;> omega


open LabeledTS in
theorem ra_linearizable (C : Configuration BC)
    (hReach : (labeledTS BC).ReachableFrom (initConfig BC) C) :
    IsRALinearizableJoin C :=
  ra_linearizable3_of_join
    (join_lemma3_of_cd' BC_coreVCs3 BC_deltaVCs3
      (cdVC3_of_all_comm BC_coreVCs3 BC_all_comm)) C hReach

end Sal.MRDTs.Instances.BoundedCounter

