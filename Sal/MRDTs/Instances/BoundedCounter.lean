import Sal.MRDTs.Metatheory.Safety
import Sal.MRDTs.Metatheory.Correctness

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
    BC.toCRDTSig.replayOrder o₁ o₂ = RcRes.Either := fun _ _ => rfl

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

/-! ## Explicit generation, safety, and sequential certificates -/

def BCInv (s : BCState) : Prop := ∀ r, 0 ≤ s.2 r ∧ s.2 r ≤ s.1 r

def bcApplicable (o : Op BCOp) (s : BCState) : Prop :=
  match o.2.2 with
  | .inc => True
  | .dec => s.2 o.2.1 + 1 ≤ s.1 o.2.1

theorem bcApplicable_inv_pres {s : BCState} {o : Op BCOp}
    (hInv : BCInv s) (happ : bcApplicable o s) : BCInv (bcUpdate s o) := by
  obtain ⟨ts, r, op⟩ := o
  intro k
  have h1 := hInv k
  cases op with
  | inc =>
    rw [bcUpdate_inc_fst, bcUpdate_inc_snd]
    split_ifs <;> omega
  | dec =>
    have h2 : s.2 r + 1 ≤ s.1 r := happ
    rw [bcUpdate_dec_fst, bcUpdate_dec_snd]
    by_cases hk : k = r
    · subst hk; rw [if_pos rfl]; omega
    · rw [if_neg hk]; omega

def bcIsIncAt (r : ℕ) (e : Op BCOp) : Bool :=
  match e.2.2 with | .inc => decide (e.2.1 = r) | .dec => false

def bcIsDecAt (r : ℕ) (e : Op BCOp) : Bool :=
  match e.2.2 with | .inc => false | .dec => decide (e.2.1 = r)

theorem bc_fold_incs (π : List (Op BCOp)) (s : BCState) (r : ℕ) :
    (applySeq BC.toCRDTSig s π).1 r = s.1 r + (π.countP (bcIsIncAt r) : ℤ) := by
  induction π generalizing s with
  | nil => simp [applySeq]
  | cons o π ih =>
    obtain ⟨ts, ro, op⟩ := o
    rw [show applySeq BC.toCRDTSig s ((ts, ro, op) :: π) =
        applySeq BC.toCRDTSig (bcUpdate s (ts, ro, op)) π from rfl,
      ih, List.countP_cons]
    cases op with
    | inc =>
      rw [bcUpdate_inc_fst]
      by_cases h : ro = r
      · subst h
        simp [bcIsIncAt]
        push_cast
        omega
      · have h' : ¬ r = ro := fun hh => h hh.symm
        simp [bcIsIncAt, h, h']
    | dec => rw [bcUpdate_dec_fst]; simp [bcIsIncAt]

theorem bc_fold_decs (π : List (Op BCOp)) (s : BCState) (r : ℕ) :
    (applySeq BC.toCRDTSig s π).2 r = s.2 r + (π.countP (bcIsDecAt r) : ℤ) := by
  induction π generalizing s with
  | nil => simp [applySeq]
  | cons o π ih =>
    obtain ⟨ts, ro, op⟩ := o
    rw [show applySeq BC.toCRDTSig s ((ts, ro, op) :: π) =
        applySeq BC.toCRDTSig (bcUpdate s (ts, ro, op)) π from rfl,
      ih, List.countP_cons]
    cases op with
    | dec =>
      rw [bcUpdate_dec_snd]
      by_cases h : ro = r
      · subst h
        simp [bcIsDecAt]
        push_cast
        omega
      · have h' : ¬ r = ro := fun hh => h hh.symm
        simp [bcIsDecAt, h, h']
    | inc => rw [bcUpdate_inc_snd]; simp [bcIsDecAt]

theorem bc_inv_init : BCInv BC.init := fun _ => ⟨le_refl 0, le_refl 0⟩

private theorem bcIsIncAt_rep {r : ℕ} {x : Op BCOp}
    (h : bcIsIncAt r x = true) : x.2.1 = r := by
  obtain ⟨ts, ro, op⟩ := x
  cases op with
  | inc => simpa [bcIsIncAt] using h
  | dec => simp [bcIsIncAt] at h

private theorem bcIsDecAt_rep {r : ℕ} {x : Op BCOp}
    (h : bcIsDecAt r x = true) : x.2.1 = r := by
  obtain ⟨ts, ro, op⟩ := x
  cases op with
  | inc => simp [bcIsDecAt] at h
  | dec => simpa [bcIsDecAt] using h

theorem bc_safetyStep : SafetyStepOn BC BCInv bcApplicable := by
  intro C E S e σS σP hEev hEcl heE hSsub heS hScl hfut hpast hσS hσP hInv happ
  obtain ⟨ts, r, op⟩ := e
  cases op with
  | inc =>
    rw [BC_update_eq]
    exact bcApplicable_inv_pres hInv (by trivial)
  | dec =>
    obtain ⟨ρS, hpS, _hrS, hfS⟩ := hσS
    obtain ⟨ρP, hpP, _hrP, hfP⟩ := hσP
    have hinc : ρS.countP (bcIsIncAt r) = ρP.countP (bcIsIncAt r) :=
      countP_prefix_eq_causal_past hEev hSsub heE heS hfut hpast hpS hpP
        (bcIsIncAt r) (fun _ hx => bcIsIncAt_rep hx)
    have hdec : ρS.countP (bcIsDecAt r) = ρP.countP (bcIsDecAt r) :=
      countP_prefix_eq_causal_past hEev hSsub heE heS hfut hpast hpS hpP
        (bcIsDecAt r) (fun _ hx => bcIsDecAt_rep hx)
    have hS1 : σS.1 r = (ρS.countP (bcIsIncAt r) : ℤ) := by
      rw [← hfS, bc_fold_incs, BC_init_fst]; omega
    have hS2 : σS.2 r = (ρS.countP (bcIsDecAt r) : ℤ) := by
      rw [← hfS, bc_fold_decs, BC_init_snd]; omega
    have hP1 : σP.1 r = (ρP.countP (bcIsIncAt r) : ℤ) := by
      rw [← hfP, bc_fold_incs, BC_init_fst]; omega
    have hP2 : σP.2 r = (ρP.countP (bcIsDecAt r) : ℤ) := by
      rw [← hfP, bc_fold_decs, BC_init_snd]; omega
    rw [BC_update_eq]
    apply bcApplicable_inv_pres hInv
    show σS.2 r + 1 ≤ σS.1 r
    change σP.2 r + 1 ≤ σP.1 r at happ
    omega

private theorem bcJoin : JoinLemma3 BC :=
  join_lemma3_of_cd' BC_coreVCs3 BC_deltaVCs3
    (cdVC3_of_all_comm BC_coreVCs3 BC_all_comm)

def generation : Issuance BC where
  CanIssue := bcApplicable

def convergence : ConvergenceCertificate BC generation where
  soundV := fun h => ra_of_mintCertifiedV (fun _ _ => bcJoin _) h

private theorem honestApp_of_mint {C : Configuration BC}
    (h : MintHonest BC bcApplicable C) : HonestAppOn BC bcApplicable C := by
  intro e he
  obtain ⟨π, hp, hr, hg⟩ := h e he
  exact ⟨applySeq BC.toCRDTSig BC.init π, ⟨π, hp, hr, rfl⟩, hg⟩

theorem versions_safe {C : Configuration BC}
    (h : MintCertifiedReach BC generation C) : VersionsSatisfy BCInv C := by
  have hG := goodConfig_of_mintCertified (fun _ _ => bcJoin _) h
  have hCC := causalCanonical_of_all_comm_rc_either BC_all_comm BC_rc_either hG
  exact version_inv_on_of_causal_canonical bc_inv_init bc_safetyStep hG hCC
    (honestApp_of_mint h.mintHonest)

theorem versions_safeV {C : Configuration BC}
    (h : MintCertifiedReachV BC (canonicalVirtualLCA BC) generation C) :
    VersionsSatisfy BCInv C := by
  have hG := goodConfig_of_mintCertifiedV (fun _ _ => bcJoin _) h
  have hCC := causalCanonical_of_all_comm_rc_either BC_all_comm BC_rc_either hG
  exact version_inv_on_of_causal_canonical bc_inv_init bc_safetyStep hG hCC
    (honestApp_of_mint h.mintHonest)

def safety : SafetyCertificate BC (canonicalVirtualLCA BC) generation where
  Safe := BCInv
  Observable := BCInv
  preservationV := versions_safeV
  consequence := fun _ h => h

def sequentialSpec : SequentialMachine (Op BCOp) where
  State := ℕ → ℤ
  init := fun _ => 0
  step q e := fun r => match e.2.2 with
    | .inc => q r + if r = e.2.1 then 1 else 0
    | .dec => q r - if r = e.2.1 then 1 else 0

def SequentialHonest (ops : List (Op BCOp)) : Prop :=
  ∀ pre suf, ops = pre ++ suf → BCInv (applySeq BC.toCRDTSig BC.init pre)

def bcIsInc (e : Op BCOp) : Bool :=
  match e.2.2 with | .inc => true | .dec => false

def canonical (ops : List (Op BCOp)) : List (Op BCOp) :=
  ops.filter bcIsInc ++ ops.filter (!bcIsInc ·)

/-- A legal abstract bounded-counter history admits the canonical
increment-before-decrement form and never consumes more rights at any replica
than the history creates there. -/
def ClientLegal (ops : List (Op BCOp)) : Prop :=
  (∃ source, ops = canonical source) ∧
  ∀ r, (ops.countP (bcIsDecAt r) : ℤ) ≤
    (ops.countP (bcIsIncAt r) : ℤ)

def clientSpec : SequentialSpec BC where
  toSequentialMachine := sequentialSpec
  Legal := ClientLegal
  query := fun q r => q r

theorem canonical_perm : ∀ ops : List (Op BCOp), ops.Perm (canonical ops) := by
  intro ops
  unfold canonical
  induction ops with
  | nil => simp
  | cons e rest ih =>
      cases h : bcIsInc e
      · simpa [h] using List.perm_cons_append_cons e ih
      · simpa [h] using ih.cons e

theorem canonical_listPermOf {ops : List (Op BCOp)}
    {E : Set (Op BCOp)} (h : listPermOf ops E) :
    listPermOf (canonical ops) E := by
  have hp := canonical_perm ops
  exact ⟨hp.nodup h.1, fun e => (hp.mem_iff (a := e)).symm.trans (h.2 e)⟩

theorem canonical_fold (ops : List (Op BCOp)) :
    applySeq BC.toCRDTSig BC.init (canonical ops) =
      applySeq BC.toCRDTSig BC.init ops :=
  applySeq_perm_of_all_comm BC_all_comm (canonical_perm ops).symm BC.init

theorem lo_false (C : Configuration BC) (a b : Op BCOp) :
    ¬ Sal.MRDTs.Foundation.lo C.core a b := by
  rintro (⟨_, hnoncomm⟩ | ⟨_, _, hrc, _⟩)
  · exact hnoncomm (BC_all_comm a b)
  · rw [BC_rc_either] at hrc
    exact RcRes.noConfusion hrc

theorem respects_lo (C : Configuration BC) (ops : List (Op BCOp)) :
    respects ops (Sal.MRDTs.Foundation.lo C.core) := by
  induction ops with
  | nil => exact List.Pairwise.nil
  | cons e rest ih =>
      exact List.pairwise_cons.mpr ⟨fun b _ => lo_false C b e, ih⟩

theorem sequential_run (ops : List (Op BCOp)) : ∀ r,
    sequentialSpec.run ops r =
      (applySeq BC.toCRDTSig BC.init ops).1 r -
      (applySeq BC.toCRDTSig BC.init ops).2 r := by
  induction ops using List.reverseRecOn with
  | nil => intro r; rfl
  | append_singleton ops e ih =>
    intro r
    obtain ⟨ts, ro, op⟩ := e
    rw [SequentialMachine.run_append_single, applySeq_append_single]
    cases op with
    | inc =>
      change sequentialSpec.run ops r + (if r = ro then 1 else 0) = _
      rw [ih r]
      simp only [BC_update_eq, bcUpdate_inc_fst, bcUpdate_inc_snd]
      split_ifs <;> omega
    | dec =>
      change sequentialSpec.run ops r - (if r = ro then 1 else 0) = _
      rw [ih r]
      simp only [BC_update_eq, bcUpdate_dec_fst, bcUpdate_dec_snd]
      split_ifs <;> omega

theorem sequentialHonest_of_linear {ops : List (Op BCOp)}
    (h : LinearMintHistory BC bcApplicable ops) : SequentialHonest ops := by
  intro pre
  induction pre using List.reverseRecOn with
  | nil => intro suf heq; exact bc_inv_init
  | append_singleton pre e ih =>
      intro suf heq
      have heq' : ops = pre ++ e :: suf := by simpa [List.append_assoc] using heq
      have hInv := ih (e :: suf) heq'
      rw [applySeq_append_single]
      rw [BC_update_eq]
      exact bcApplicable_inv_pres hInv (h.guarded pre e suf heq')

def sequential : SequentialRefinement BC sequentialSpec where
  Honest := SequentialHonest
  Rel := fun s q => BCInv s ∧ ∀ r, q r = s.1 r - s.2 r
  init := ⟨bc_inv_init, fun _ => rfl⟩
  sound := fun ops h => ⟨h ops [] (by simp), sequential_run ops⟩

noncomputable def sequentialCorrectness : SequentialCorrectnessCertificate BC generation
    (InteractionSpec.raw BC)
    clientSpec sequential.Rel where
  sound C exec replay := by
    intro v s E hver
    obtain ⟨ops, hperm, _, hfold⟩ := replay v s E hver
    let π := canonical ops
    have hπfold : applySeq BC.toCRDTSig BC.init π = s := by
      exact (canonical_fold ops).trans hfold
    have hsafe : BCInv s := by
      cases exec with
      | ordinary reach => exact versions_safe reach v s E hver
      | virtual reach => exact versions_safeV reach v s E hver
    have hcount : ∀ r, (π.countP (bcIsDecAt r) : ℤ) ≤
        (π.countP (bcIsIncAt r) : ℤ) := by
      intro r
      have hr := hsafe r
      rw [← hπfold, bc_fold_incs, bc_fold_decs, BC_init_fst,
        BC_init_snd] at hr
      omega
    have hrel : sequential.Rel s (clientSpec.run π) := by
      refine ⟨hsafe, ?_⟩
      intro r
      change sequentialSpec.run π r = s.1 r - s.2 r
      rw [sequential_run, hπfold]
    refine ⟨π, canonical_listPermOf hperm,
      respects_interactionLoOn_raw_of_lo (respects_lo C π),
      ⟨⟨ops, rfl⟩, hcount⟩, hrel, ?_⟩
    intro r
    exact (hrel.2 r).symm

noncomputable def verified : VerifiedMRDT BC where
  issuance := generation
  interaction := InteractionSpec.raw BC
  convergence := convergence
  Spec := clientSpec
  Rel := sequential.Rel
  sequentialCorrectness := sequentialCorrectness

#print axioms versions_safe
#print axioms versions_safeV
#print axioms verified

end Sal.MRDTs.Instances.BoundedCounter
