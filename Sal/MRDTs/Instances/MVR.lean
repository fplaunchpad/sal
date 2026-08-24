import Sal.MRDTs.Metatheory.Correctness

/-!
# Multi-Valued Register: flat VC discharge and the conditioned capstone

The production Multi-Valued Register as a `MRDTSig`, its
RA-linearizability VC discharge, and the conditioned capstone over the generic
framework.
-/

set_option maxHeartbeats 1000000

namespace Sal.MRDTs.Instances.MVR

open Sal.MRDTs.Foundation
open Classical

/-! ## The Multi-Valued Register discharge (feasible class, all-commuting)

The classical replace-on-write MVR (mirror of
`Sal/MRDTs/Multi_Valued_Register/Multi_Valued_Register_MRDT.lean`; documented
deviation: the op's overwritten-set payload is carried as a `List ℕ`, read
through its membership function).  State: timestamp-tagged writes × the
overwritten-log accumulator; both components grow-only under `do`, so ALL
operations commute, yet the merge is the OR-shaped
`(l∩a∩b) ∪ (a∖l) ∪ (b∖l)` per component, which fails the unconditional delta
laws on infeasible tuples (the `c∩l` corner).  MVR therefore sits in the
FEASIBLE class despite commuting.  All-commutation makes every punctured
downset empty (`B = init`), so no trichotomies are needed; the two nontrivial
feasible laws reduce to Boolean tautologies plus one σ-monotonicity fact
(canonical states of nested event sets are pointwise nested, both components
are unions over events). -/

inductive MVROp : Type where
  | write : ℕ → List ℕ → MVROp
deriving DecidableEq

/-- Production `do_`: record the tagged write, accumulate the overwritten log. -/
def mvrUpdate (s : ((ℕ × ℕ) → Bool) × (ℕ → Bool)) (o : Op MVROp) :
    ((ℕ × ℕ) → Bool) × (ℕ → Bool) :=
  match o.2.2 with
  | .write v O =>
      (fun p => s.1 p || decide (p = (o.1, v)),
       fun n => s.2 n || decide (n ∈ O))

/-- Three-way merge: the OR-shape per component. -/
def mvrMergeL (l a b : ((ℕ × ℕ) → Bool) × (ℕ → Bool)) :
    ((ℕ × ℕ) → Bool) × (ℕ → Bool) :=
  (fun p => (l.1 p && (a.1 p && b.1 p))
      || ((a.1 p && !l.1 p) || (b.1 p && !l.1 p)),
   fun n => (l.2 n && (a.2 n && b.2 n))
      || ((a.2 n && !l.2 n) || (b.2 n && !l.2 n)))

/-- The Multi-Valued Register MRDT. -/
noncomputable def MVR : MRDTSig where
  State := ((ℕ × ℕ) → Bool) × (ℕ → Bool)
  dec_state := fun _ _ => Classical.propDecidable _
  init := (fun _ => false, fun _ => false)
  AppOp := MVROp
  dec_op := inferInstance
  Query := Unit
  Value := ((ℕ × ℕ) → Bool) × (ℕ → Bool)
  update := mvrUpdate
  merge := fun a b => mvrMergeL (fun _ => false, fun _ => false) a b
  query := fun s _ => s
  mergeL := mvrMergeL
  merge_init_slice := fun _ _ => rfl

theorem MVR_rc_either (o₁ o₂ : Op MVROp) :
    MVR.toCRDTSig.replayOrder o₁ o₂ = RcRes.Either := rfl

/-! ### Projection unfolds and the update layer -/

theorem MVR_update_eq (st : MVR.State) (o : Op MVR.AppOp) :
    MVR.update st o = mvrUpdate st o := rfl

theorem MVR_mergeL_eq (l a b : MVR.State) :
    MVR.mergeL l a b = mvrMergeL l a b := rfl

theorem MVR_init_eq :
    MVR.init = ((fun _ => false, fun _ => false) : MVR.State) := rfl

theorem MVR_all_comm (o₁ o₂ : Op MVROp) : MVR.toCRDTSig.commutes o₁ o₂ := by
  intro s
  rcases o₁ with ⟨ts₁, r₁, op₁⟩
  rcases o₂ with ⟨ts₂, r₂, op₂⟩
  cases op₁ with
  | write v₁ O₁ =>
    cases op₂ with
    | write v₂ O₂ =>
      refine Prod.ext (funext fun p => ?_) (funext fun n => ?_) <;>
        simp only [MVR_update_eq, mvrUpdate]
      · cases s.1 p <;>
          cases hd₁ : decide (p = (ts₁, v₁)) <;>
          cases hd₂ : decide (p = (ts₂, v₂)) <;> rfl
      · cases s.2 n <;>
          cases hd₁ : decide (n ∈ O₁) <;>
          cases hd₂ : decide (n ∈ O₂) <;> rfl

theorem MVR_updateVCs : UpdateVCs MVR.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (MVR_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [MVR_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [MVR_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [MVR_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem MVR_mergeL_comm (l a b : MVR.State) :
    MVR.mergeL l a b = MVR.mergeL l b a := by
  refine Prod.ext (funext fun p => ?_) (funext fun n => ?_) <;>
    simp only [MVR_mergeL_eq, mvrMergeL]
  · cases l.1 p <;> cases a.1 p <;> cases b.1 p <;> rfl
  · cases l.2 n <;> cases a.2 n <;> cases b.2 n <;> rfl

theorem MVR_coreVCs3CD : CoreVCs3CD MVR :=
  ⟨MVR_updateVCs, MVR_mergeL_comm⟩

/-! ### σ-monotonicity (the one canonical fact) -/

/-- Component 1 bound: a tagged write in the fold has a `write` event. -/
theorem MVR_fold_bound₁ {ρ : List (Op MVROp)} {p : ℕ × ℕ}
    (h : (applySeq MVR.toCRDTSig MVR.init ρ).1 p = true) :
    ∃ o ∈ ρ, ∃ O, o.2.2 = MVROp.write p.2 O ∧ o.1 = p.1 := by
  induction ρ using List.reverseRecOn with
  | nil => exact absurd (show (false : Bool) = true from h) Bool.noConfusion
  | append_singleton ρ o ih =>
    rw [applySeq_append_single] at h
    rcases o with ⟨ts, rid, op⟩
    cases op with
    | write v O =>
      have h' : ((applySeq MVR.toCRDTSig MVR.init ρ).1 p
          || decide (p = (ts, v))) = true := h
      cases hfa : (applySeq MVR.toCRDTSig MVR.init ρ).1 p with
      | true =>
        obtain ⟨o', ho', O', h1, h2⟩ := ih hfa
        exact ⟨o', List.mem_append_left _ ho', O', h1, h2⟩
      | false =>
        rw [hfa] at h'
        have hp' : p = (ts, v) := of_decide_eq_true (by simpa using h')
        refine ⟨(ts, rid, MVROp.write v O),
          List.mem_append_right _ List.mem_cons_self, O, ?_, ?_⟩
        · show MVROp.write v O = MVROp.write p.2 O
          rw [hp']
        · show ts = p.1
          rw [hp']

/-- Component 2 bound: an accumulated overwrite has a contributing `write`. -/
theorem MVR_fold_bound₂ {ρ : List (Op MVROp)} {n : ℕ}
    (h : (applySeq MVR.toCRDTSig MVR.init ρ).2 n = true) :
    ∃ o ∈ ρ, ∃ v O, o.2.2 = MVROp.write v O ∧ n ∈ O := by
  induction ρ using List.reverseRecOn with
  | nil => exact absurd (show (false : Bool) = true from h) Bool.noConfusion
  | append_singleton ρ o ih =>
    rw [applySeq_append_single] at h
    rcases o with ⟨ts, rid, op⟩
    cases op with
    | write v O =>
      have h' : ((applySeq MVR.toCRDTSig MVR.init ρ).2 n
          || decide (n ∈ O)) = true := h
      cases hfa : (applySeq MVR.toCRDTSig MVR.init ρ).2 n with
      | true =>
        obtain ⟨o', ho', v', O', h1, h2⟩ := ih hfa
        exact ⟨o', List.mem_append_left _ ho', v', O', h1, h2⟩
      | false =>
        rw [hfa] at h'
        refine ⟨(ts, rid, MVROp.write v O),
          List.mem_append_right _ List.mem_cons_self, v, O, rfl,
          of_decide_eq_true (by simpa using h')⟩

/-- Both components are grow-only: truth is preserved by any suffix. -/
theorem MVR_fold_stays_true₁ {p : ℕ × ℕ} :
    ∀ (β : List (Op MVROp)) (s : MVR.State), s.1 p = true →
      (applySeq MVR.toCRDTSig s β).1 p = true := by
  intro β
  induction β with
  | nil => intro s hs; exact hs
  | cons o β ih =>
    intro s hs
    refine ih (MVR.update s o) ?_
    rcases o with ⟨ts, rid, op⟩
    cases op with
    | write v O =>
      show (s.1 p || decide (p = (ts, v))) = true
      rw [hs]
      rfl

theorem MVR_fold_stays_true₂ {n : ℕ} :
    ∀ (β : List (Op MVROp)) (s : MVR.State), s.2 n = true →
      (applySeq MVR.toCRDTSig s β).2 n = true := by
  intro β
  induction β with
  | nil => intro s hs; exact hs
  | cons o β ih =>
    intro s hs
    refine ih (MVR.update s o) ?_
    rcases o with ⟨ts, rid, op⟩
    cases op with
    | write v O =>
      show (s.2 n || decide (n ∈ O)) = true
      rw [hs]
      rfl

/-- A member `write` makes its tag live in the fold (component 1). -/
theorem MVR_contrib₁ {ρ : List (Op MVROp)} {ts rid v : ℕ} {O : List ℕ}
    (h : (ts, rid, MVROp.write v O) ∈ ρ) :
    (applySeq MVR.toCRDTSig MVR.init ρ).1 (ts, v) = true := by
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem h
  subst hsplit
  have hstep : applySeq MVR.toCRDTSig MVR.init
      (α ++ (ts, rid, MVROp.write v O) :: β)
      = applySeq MVR.toCRDTSig
          (MVR.update (applySeq MVR.toCRDTSig MVR.init α)
            (ts, rid, MVROp.write v O)) β := by
    simp [applySeq, List.foldl_append]
  rw [hstep]
  refine MVR_fold_stays_true₁ β _ ?_
  show ((applySeq MVR.toCRDTSig MVR.init α).1 (ts, v)
      || decide ((ts, v) = (ts, v))) = true
  rw [decide_eq_true rfl]
  cases (applySeq MVR.toCRDTSig MVR.init α).1 (ts, v) <;> rfl

/-- A member `write` accumulates its overwrites in the fold (component 2). -/
theorem MVR_contrib₂ {ρ : List (Op MVROp)} {ts rid v : ℕ} {O : List ℕ} {n : ℕ}
    (h : (ts, rid, MVROp.write v O) ∈ ρ) (hn : n ∈ O) :
    (applySeq MVR.toCRDTSig MVR.init ρ).2 n = true := by
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem h
  subst hsplit
  have hstep : applySeq MVR.toCRDTSig MVR.init
      (α ++ (ts, rid, MVROp.write v O) :: β)
      = applySeq MVR.toCRDTSig
          (MVR.update (applySeq MVR.toCRDTSig MVR.init α)
            (ts, rid, MVROp.write v O)) β := by
    simp [applySeq, List.foldl_append]
  rw [hstep]
  refine MVR_fold_stays_true₂ β _ ?_
  show ((applySeq MVR.toCRDTSig MVR.init α).2 n || decide (n ∈ O)) = true
  rw [decide_eq_true hn]
  cases (applySeq MVR.toCRDTSig MVR.init α).2 n <;> rfl

/-- **σ-monotonicity**: canonical states of nested event sets are pointwise
nested, in both components. -/
theorem MVR_canonical_mono
    {C : Sal.MRDTs.Foundation.Configuration MVR.toCRDTSig}
    {F G : Set (Op MVROp)} {s t : MVR.State}
    (hFG : ∀ o ∈ F, o ∈ G)
    (hs : IsCanonicalState C F s) (ht : IsCanonicalState C G t) :
    (∀ p, s.1 p = true → t.1 p = true) ∧
    (∀ n, s.2 n = true → t.2 n = true) := by
  obtain ⟨ρ, hρp, -, hρf⟩ := hs
  obtain ⟨π, hπp, -, hπf⟩ := ht
  constructor
  · intro p hp
    rw [← hρf] at hp
    obtain ⟨o, ho, O, hoT, hoTs⟩ := MVR_fold_bound₁ hp
    rcases o with ⟨ts, rid, op⟩
    have hoT' : op = MVROp.write p.2 O := hoT
    have hoTs' : ts = p.1 := hoTs
    subst hoT'
    subst hoTs'
    have hπm : (p.1, rid, MVROp.write p.2 O) ∈ π :=
      (hπp.2 _).mpr (hFG _ ((hρp.2 _).mp ho))
    rw [← hπf]
    have := MVR_contrib₁ (ρ := π) (ts := p.1) (rid := rid) (v := p.2)
      (O := O) hπm
    simpa using this
  · intro n hn
    rw [← hρf] at hn
    obtain ⟨o, ho, v, O, hoT, hnO⟩ := MVR_fold_bound₂ hn
    rcases o with ⟨ts, rid, op⟩
    have hoT' : op = MVROp.write v O := hoT
    subst hoT'
    have hπm : (ts, rid, MVROp.write v O) ∈ π :=
      (hπp.2 _).mpr (hFG _ ((hρp.2 _).mp ho))
    rw [← hπf]
    exact MVR_contrib₂ hπm hnO

/-! ### The punctured downset is empty (all-commutation) -/

theorem MVR_downset_empty (C : Sal.MRDTs.Foundation.Configuration MVR.toCRDTSig)
    (e : Op MVROp) : downset C e \ {e} = ∅ := by
  ext x
  simp only [Set.mem_diff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  rintro (hx | hx)
  · exact fun hne => hne hx
  · intro _
    exfalso
    cases hx with
    | single h' => exact h'.2 (MVR_all_comm _ _)
    | tail _ h' => exact h'.2 (MVR_all_comm _ _)

/-! ### The feasible delta laws and CD -/

theorem MVR_feasibleDeltaVCs3 : FeasibleDeltaVCs3 MVR := by
  refine ⟨?_, ?_, ?_⟩
  · -- feasible_init: unconditional for the MVR
    intro C ev s _ _
    refine Prod.ext (funext fun p => ?_) (funext fun n => ?_) <;>
      simp only [MVR_mergeL_eq, mvrMergeL, MVR_init_eq]
    · cases s.1 p <;> rfl
    · cases s.2 n <;> rfl
  · -- feasible_local_redistribute: B = init + σ-monotonicity s₀ ⊆ s₂
    intro C ev₁ ev₂ s₀ B t₁ s₂ e _ _ _ _ _ _ _ _ _ hc₀ hcB _ hc₂
    have hBinit : B = MVR.init :=
      isCanonicalState_empty (MVR_downset_empty C e) hcB
    subst hBinit
    have hsub : ∀ o ∈ ev₁ ∩ ev₂, o ∈ ev₂ := fun o ho => ho.2
    have hmono := MVR_canonical_mono hsub hc₀ hc₂
    rcases e with ⟨ts, rid, op⟩
    cases op with
    | write v O =>
      refine Prod.ext (funext fun p => ?_) (funext fun n => ?_) <;>
        simp only [MVR_mergeL_eq, MVR_update_eq, mvrMergeL, mvrUpdate,
          MVR_init_eq]
      · cases hs₀ : s₀.1 p
        · cases t₁.1 p <;> cases decide (p = (ts, v)) <;> cases s₂.1 p <;> rfl
        · have hs₂ : s₂.1 p = true := hmono.1 p hs₀
          rw [hs₂]
          cases t₁.1 p <;> cases decide (p = (ts, v)) <;> rfl
      · cases hs₀ : s₀.2 n
        · cases t₁.2 n <;> cases decide (n ∈ O) <;> cases s₂.2 n <;> rfl
        · have hs₂ : s₂.2 n = true := hmono.2 n hs₀
          rw [hs₂]
          cases t₁.2 n <;> cases decide (n ∈ O) <;> rfl
  · -- feasible_redistribute: B = init + a Boolean tautology
    intro C ev₁ ev₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ hcB _ _
    have hBinit : B = MVR.init :=
      isCanonicalState_empty (MVR_downset_empty C e) hcB
    subst hBinit
    rcases e with ⟨ts, rid, op⟩
    cases op with
    | write v O =>
      refine Prod.ext (funext fun p => ?_) (funext fun n => ?_) <;>
        simp only [MVR_mergeL_eq, MVR_update_eq, mvrMergeL, mvrUpdate,
          MVR_init_eq]
      · cases t₀.1 p <;> cases t₁.1 p <;> cases t₂.1 p <;>
          cases decide (p = (ts, v)) <;> rfl
      · cases t₀.2 n <;> cases t₁.2 n <;> cases t₂.2 n <;>
          cases decide (n ∈ O) <;> rfl

theorem MVR_cdVC3 : CDVC3 MVR := by
  intro C U A B e _ _ _ _ _ _ hA hB
  have hBinit : B = MVR.init :=
    isCanonicalState_empty (MVR_downset_empty C e) hB
  subst hBinit
  rcases e with ⟨ts, rid, op⟩
  cases op with
  | write v O =>
    refine Prod.ext (funext fun p => ?_) (funext fun n => ?_) <;>
      simp only [MVR_mergeL_eq, MVR_update_eq, mvrMergeL, mvrUpdate,
        MVR_init_eq]
    · cases A.1 p <;> cases decide (p = (ts, v)) <;> rfl
    · cases A.2 n <;> cases decide (n ∈ O) <;> rfl

/-! ## Client intent and the plain-framework production certificate -/

def mvrTag (s : MVR.State) (n : ℕ) : Prop := ∃ v, s.1 (n, v) = true

def mvrVis (s : MVR.State) (n : ℕ) : Prop := mvrTag s n ∧ s.2 n = false

def mvrView (s : MVR.State) (v : ℕ) : Prop :=
  ∃ n, s.1 (n, v) = true ∧ s.2 n = false

def mvrApplicable (o : Op MVROp) (s : MVR.State) : Prop :=
  (∀ v, s.1 (o.1, v) = false) ∧
  ∀ w O, o.2.2 = MVROp.write w O → ∀ n, n ∈ O ↔ mvrVis s n

def mvrOK (ρ : List (Op MVROp)) : Prop :=
  ∀ (σ : List (Op MVROp)) (o : Op MVROp) (τ : List (Op MVROp)),
    ρ = σ ++ o :: τ → mvrApplicable o (applySeq MVR.toCRDTSig MVR.init σ)

theorem mvrOK_prefix {ρ : List (Op MVROp)} {o : Op MVROp}
    (h : mvrOK (ρ ++ [o])) : mvrOK ρ := by
  intro σ o' τ heq
  exact h σ o' (τ ++ [o]) (by rw [heq]; simp)

def mvrSpecFold (ρ : List (Op MVROp)) : Option ℕ :=
  ρ.foldl (fun _ o => match o.2.2 with | .write v _ => some v) none

theorem mvrSpecFold_snoc (ρ : List (Op MVROp)) (ts r w : ℕ) (O : List ℕ) :
    mvrSpecFold (ρ ++ [(ts, r, MVROp.write w O)]) = some w := by
  unfold mvrSpecFold
  rw [List.foldl_append]
  rfl

theorem mvr_over_tags {ρ : List (Op MVROp)} (hOK : mvrOK ρ) :
    ∀ n, (applySeq MVR.toCRDTSig MVR.init ρ).2 n = true → mvrTag (applySeq MVR.toCRDTSig MVR.init ρ) n := by
  induction ρ using List.reverseRecOn with
  | nil =>
      intro n h
      have : (applySeq MVR.toCRDTSig MVR.init ([] : List (Op MVROp))).2 n = false := rfl
      rw [this] at h
      exact Bool.noConfusion h
  | append_singleton ρ o ih =>
      intro n h
      obtain ⟨ts, r, op⟩ := o
      cases op with
      | write w O =>
          rw [applySeq_append_single, MVR_update_eq] at h ⊢
          simp only [mvrUpdate, Bool.or_eq_true, decide_eq_true_eq] at h
          simp only [mvrTag, mvrUpdate, Bool.or_eq_true, decide_eq_true_eq]
          rcases h with h' | h'
          · obtain ⟨v', hv'⟩ := ih (mvrOK_prefix hOK) n h'
            exact ⟨v', Or.inl hv'⟩
          · have hO := (hOK ρ (ts, r, .write w O) [] (by simp)).2 w O rfl n
            obtain ⟨⟨v', hv'⟩, -⟩ := hO.mp h'
            exact ⟨v', Or.inl hv'⟩

theorem mvr_seq_sound {ρ : List (Op MVROp)} (hOK : mvrOK ρ) (v : ℕ) :
    mvrView (applySeq MVR.toCRDTSig MVR.init ρ) v ↔ mvrSpecFold ρ = some v := by
  induction ρ using List.reverseRecOn with
  | nil =>
      constructor
      · rintro ⟨n, hn, -⟩
        exact Bool.noConfusion hn
      · intro h
        simp [mvrSpecFold] at h
  | append_singleton ρ o ih =>
      obtain ⟨ts, r, op⟩ := o
      cases op with
      | write w O =>
          have hcond := hOK ρ (ts, r, .write w O) [] (by simp)
          have hfresh := hcond.1
          have hO := hcond.2 w O rfl
          rw [applySeq_append_single, MVR_update_eq, mvrSpecFold_snoc]
          simp only [mvrView, mvrUpdate, Bool.or_eq_true,
            decide_eq_true_eq, Bool.or_eq_false_iff,
            decide_eq_false_iff_not, Prod.mk.injEq]
          constructor
          · rintro ⟨n, hstake, hov, hnO⟩
            rcases hstake with hs | ⟨rfl, rfl⟩
            · exact absurd ((hO n).mpr ⟨⟨v, hs⟩, hov⟩) hnO
            · rfl
          · intro hspec
            have hvw : w = v := by simpa using hspec
            subst hvw
            have hnotag : ¬ mvrTag (applySeq MVR.toCRDTSig MVR.init ρ) ts := by
              rintro ⟨v', hv'⟩
              rw [hfresh v'] at hv'
              exact Bool.noConfusion hv'
            have h1 : (applySeq MVR.toCRDTSig MVR.init ρ).2 ts = false := by
              cases hh : (applySeq MVR.toCRDTSig MVR.init ρ).2 ts with
              | false => rfl
              | true =>
                  exact absurd (mvr_over_tags (mvrOK_prefix hOK) ts hh) hnotag
            have h2 : ts ∉ O := fun hin => hnotag ((hO ts).mp hin).1
            exact ⟨ts, Or.inr ⟨rfl, rfl⟩, h1, h2⟩

private theorem mvrJoin : JoinLemma3 MVR :=
  join_lemma3_of_cd_feasible MVR_coreVCs3CD MVR_feasibleDeltaVCs3 MVR_cdVC3

def generation : Issuance MVR where
  CanIssue := mvrApplicable

def convergence : ConvergenceCertificate MVR generation where
  soundV := fun h => ra_of_mintCertifiedV (fun _ _ => mvrJoin _) h

def spec : SequentialMachine (Op MVROp) where
  State := Option ℕ
  init := none
  step := fun _ o => match o.2.2 with | .write v _ => some v

theorem spec_run (ρ : List (Op MVROp)) : spec.run ρ = mvrSpecFold ρ := rfl

def sequential : SequentialRefinement MVR spec where
  Honest := mvrOK
  Rel := fun s q => ∀ v, mvrView s v ↔ q = some v
  init := by
    intro v
    constructor
    · rintro ⟨n, hn, -⟩
      exact Bool.noConfusion hn
    · intro h
      simp [spec] at h
  sound := by
    intro ρ hOK v
    rw [spec_run]
    exact mvr_seq_sound hOK v

noncomputable def replayVerified : ReplayVerifiedMRDT MVR where
  issuance := generation
  convergence := convergence
  Machine := spec
  sequential := sequential
  sequential_of_mint := fun _ h => by
    simpa [sequential, mvrOK, generation, mvrApplicable] using h.guarded

/-! ### Checked obstruction to a sequential-register legalization

Two replicas may concurrently issue writes from the empty register.  Their
merged MVR view contains both values.  No state of the ordinary sequential
register above can have that observation, so the replay certificate cannot be
promoted to `VerifiedMRDT` with this client specification. -/

def concurrentWrite₁ : Op MVROp := (1, 0, .write 10 [])
def concurrentWrite₂ : Op MVROp := (2, 1, .write 20 [])

noncomputable def concurrentState : MVR.State :=
  MVR.merge
    (MVR.update MVR.init concurrentWrite₁)
    (MVR.update MVR.init concurrentWrite₂)

theorem concurrent_writes_applicable :
    mvrApplicable concurrentWrite₁ MVR.init ∧
    mvrApplicable concurrentWrite₂ MVR.init := by
  simp [concurrentWrite₁, concurrentWrite₂, mvrApplicable, mvrVis, mvrTag,
    MVR_init_eq]

theorem concurrentState_views_both :
    mvrView concurrentState 10 ∧ mvrView concurrentState 20 := by
  constructor <;>
    simp [concurrentState, concurrentWrite₁, concurrentWrite₂, mvrView,
      MVR, mvrMergeL, mvrUpdate]

theorem concurrentState_no_sequential_register :
    ¬ ∃ q : spec.State, sequential.Rel concurrentState q := by
  rintro ⟨q, hq⟩
  obtain ⟨h10, h20⟩ := concurrentState_views_both
  have q10 : q = some 10 := (hq 10).mp h10
  have q20 : q = some 20 := (hq 20).mp h20
  have : (some 10 : Option ℕ) = some 20 := q10.symm.trans q20
  simp at this

#print axioms mvr_seq_sound
#print axioms replayVerified
#print axioms concurrentState_no_sequential_register

end Sal.MRDTs.Instances.MVR
