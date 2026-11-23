import Artifact.MRDTs.Metatheory.Correctness

/-!
# Historical grow-only MVR: implementation and algebraic reference

Production uses `MVRLiveContract.verified`, whose concrete state contains only
live tagged writes. This module retains the operation type, historical
algebraic model, and negative single-register control used by the proof suite.
The raw `MRDTSig` exposes its live value set. Its selected event `replayOrder` records observed
supersession. `MVRContract` supplies the finite-live-set specification and
complete public certificate; the single-register counterexample below rules
out only the old concurrent target, not the ordinary sequential special case.
-/

set_option maxHeartbeats 1000000

namespace LeanProofs.Implementations.MVRegister.MVR

open Artifact.MRDTs
open Artifact.MRDTs.Foundation
open Classical

/-! ## The Multi-Valued Register discharge (feasible class, all-commuting)

The classical replace-on-write MVR (mirror of
`Artifact/MRDTs/Multi_Valued_Register/Multi_Valued_Register_MRDT.lean`; documented
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

/-- Record the tagged write and accumulate the overwritten log. -/
def mvrUpdate (s : ((ℕ × ℕ) → Bool) × (ℕ → Bool)) (o : Op MVROp) :
    ((ℕ × ℕ) → Bool) × (ℕ → Bool) :=
  match o.2.2 with
  | .write v O =>
      (fun p => s.1 p || decide (p = (o.1, v)),
       fun n => s.2 n || decide (n ∈ O))

/-- Three-way merge: the OR-shape per component. -/
def mvrMerge (l a b : ((ℕ × ℕ) → Bool) × (ℕ → Bool)) :
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
  Value := Set ℕ
  update := mvrUpdate
  query := fun s _ v => ∃ n, s.1 (n, v) = true ∧ s.2 n = false
  merge := mvrMerge

def overwrites (o : Op MVROp) : List ℕ :=
  match o.2.2 with | .write _ O => O

/-- Observed supersession, not a timestamp winner among concurrent writes.
The timestamp guard excludes malformed cyclic payloads outside executions. -/
def replayOrder : EventOrder MVR.toUpdateSig where
  order a b := if a.1 < b.1 ∧ a.1 ∈ overwrites b then .Fst_then_snd
    else if b.1 < a.1 ∧ b.1 ∈ overwrites a then .Snd_then_fst else .Either

attribute [local instance] replayOrder

theorem replayOrder_before_iff (a b : Op MVROp) :
    MVR.toUpdateSig.replayBefore a b ↔ a.1 < b.1 ∧ a.1 ∈ overwrites b := by
  change (if a.1 < b.1 ∧ a.1 ∈ overwrites b then OrderResult.Fst_then_snd
    else if b.1 < a.1 ∧ b.1 ∈ overwrites a then .Snd_then_fst else .Either) =
      .Fst_then_snd ↔ _
  split <;> simp_all
  split <;> simp_all

theorem replayOrder_acyclic : ReplayAcyclic MVR.toUpdateSig := by
  intro a h
  have hlt : Relation.TransGen (fun a b : Op MVROp => a.1 < b.1) a a :=
    h.lift id (fun a b h => ((replayOrder_before_iff a b).mp h).1)
  rw [Relation.transGen_eq_self (show Transitive
    (fun a b : Op MVROp => a.1 < b.1) from fun _ _ _ => lt_trans)] at hlt
  exact (Nat.lt_irrefl _) hlt

/-! ### Projection unfolds and the update layer -/

theorem MVR_update_eq (st : MVR.State) (o : Op MVR.AppOp) :
    MVR.update st o = mvrUpdate st o := rfl

theorem MVR_merge_eq (l a b : MVR.State) :
    MVR.merge l a b = mvrMerge l a b := rfl

theorem MVR_init_eq :
    MVR.init = ((fun _ => false, fun _ => false) : MVR.State) := rfl

theorem MVR_all_comm (o₁ o₂ : Op MVROp) : MVR.toUpdateSig.commutes o₁ o₂ := by
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

theorem replayLaws : ReplayLaws MVR.toUpdateSig := by
  exact ReplayLaws.of_all_comm MVR_all_comm replayOrder_acyclic

theorem MVR_merge_comm (l a b : MVR.State) :
    MVR.merge l a b = MVR.merge l b a := by
  refine Prod.ext (funext fun p => ?_) (funext fun n => ?_) <;>
    simp only [MVR_merge_eq, mvrMerge]
  · cases l.1 p <;> cases a.1 p <;> cases b.1 p <;> rfl
  · cases l.2 n <;> cases a.2 n <;> cases b.2 n <;> rfl

theorem MVR_joinCoreLaws : JoinCoreLaws MVR :=
  ⟨replayLaws, MVR_merge_comm⟩

/-! ### σ-monotonicity (the one canonical fact) -/

/-- Component 1 bound: a tagged write in the fold has a `write` event. -/
theorem MVR_fold_bound₁ {ρ : List (Op MVROp)} {p : ℕ × ℕ}
    (h : (applySeq MVR.toUpdateSig MVR.init ρ).1 p = true) :
    ∃ o ∈ ρ, ∃ O, o.2.2 = MVROp.write p.2 O ∧ o.1 = p.1 := by
  induction ρ using List.reverseRecOn with
  | nil => exact absurd (show (false : Bool) = true from h) Bool.noConfusion
  | append_singleton ρ o ih =>
    rw [applySeq_append_single] at h
    rcases o with ⟨ts, rid, op⟩
    cases op with
    | write v O =>
      have h' : ((applySeq MVR.toUpdateSig MVR.init ρ).1 p
          || decide (p = (ts, v))) = true := h
      cases hfa : (applySeq MVR.toUpdateSig MVR.init ρ).1 p with
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
    (h : (applySeq MVR.toUpdateSig MVR.init ρ).2 n = true) :
    ∃ o ∈ ρ, ∃ v O, o.2.2 = MVROp.write v O ∧ n ∈ O := by
  induction ρ using List.reverseRecOn with
  | nil => exact absurd (show (false : Bool) = true from h) Bool.noConfusion
  | append_singleton ρ o ih =>
    rw [applySeq_append_single] at h
    rcases o with ⟨ts, rid, op⟩
    cases op with
    | write v O =>
      have h' : ((applySeq MVR.toUpdateSig MVR.init ρ).2 n
          || decide (n ∈ O)) = true := h
      cases hfa : (applySeq MVR.toUpdateSig MVR.init ρ).2 n with
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
      (applySeq MVR.toUpdateSig s β).1 p = true := by
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
      (applySeq MVR.toUpdateSig s β).2 n = true := by
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
    (applySeq MVR.toUpdateSig MVR.init ρ).1 (ts, v) = true := by
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem h
  subst hsplit
  have hstep : applySeq MVR.toUpdateSig MVR.init
      (α ++ (ts, rid, MVROp.write v O) :: β)
      = applySeq MVR.toUpdateSig
          (MVR.update (applySeq MVR.toUpdateSig MVR.init α)
            (ts, rid, MVROp.write v O)) β := by
    simp [applySeq, List.foldl_append]
  rw [hstep]
  refine MVR_fold_stays_true₁ β _ ?_
  show ((applySeq MVR.toUpdateSig MVR.init α).1 (ts, v)
      || decide ((ts, v) = (ts, v))) = true
  rw [decide_eq_true rfl]
  cases (applySeq MVR.toUpdateSig MVR.init α).1 (ts, v) <;> rfl

/-- A member `write` accumulates its overwrites in the fold (component 2). -/
theorem MVR_contrib₂ {ρ : List (Op MVROp)} {ts rid v : ℕ} {O : List ℕ} {n : ℕ}
    (h : (ts, rid, MVROp.write v O) ∈ ρ) (hn : n ∈ O) :
    (applySeq MVR.toUpdateSig MVR.init ρ).2 n = true := by
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem h
  subst hsplit
  have hstep : applySeq MVR.toUpdateSig MVR.init
      (α ++ (ts, rid, MVROp.write v O) :: β)
      = applySeq MVR.toUpdateSig
          (MVR.update (applySeq MVR.toUpdateSig MVR.init α)
            (ts, rid, MVROp.write v O)) β := by
    simp [applySeq, List.foldl_append]
  rw [hstep]
  refine MVR_fold_stays_true₂ β _ ?_
  show ((applySeq MVR.toUpdateSig MVR.init α).2 n || decide (n ∈ O)) = true
  rw [decide_eq_true hn]
  cases (applySeq MVR.toUpdateSig MVR.init α).2 n <;> rfl

/-- **σ-monotonicity**: canonical states of nested event sets are pointwise
nested, in both components. -/
theorem MVR_canonical_mono
    {C : Artifact.MRDTs.Foundation.ReplayContext MVR.toUpdateSig}
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

theorem MVR_downset_empty (C : Artifact.MRDTs.Foundation.ReplayContext MVR.toUpdateSig)
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

theorem MVR_feasibleDeltaLaws : FeasibleDeltaLaws MVR := by
  refine ⟨?_, ?_, ?_⟩
  · -- init: unconditional for the MVR
    intro C ev s _ _
    refine Prod.ext (funext fun p => ?_) (funext fun n => ?_) <;>
      simp only [MVR_merge_eq, mvrMerge, MVR_init_eq]
    · cases s.1 p <;> rfl
    · cases s.2 n <;> rfl
  · -- local_redistribute: B = init + σ-monotonicity s₀ ⊆ s₂
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
        simp only [MVR_merge_eq, MVR_update_eq, mvrMerge, mvrUpdate,
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
  · -- redistribute: B = init + a Boolean tautology
    intro C ev₁ ev₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ hcB _ _
    have hBinit : B = MVR.init :=
      isCanonicalState_empty (MVR_downset_empty C e) hcB
    subst hBinit
    rcases e with ⟨ts, rid, op⟩
    cases op with
    | write v O =>
      refine Prod.ext (funext fun p => ?_) (funext fun n => ?_) <;>
        simp only [MVR_merge_eq, MVR_update_eq, mvrMerge, mvrUpdate,
          MVR_init_eq]
      · cases t₀.1 p <;> cases t₁.1 p <;> cases t₂.1 p <;>
          cases decide (p = (ts, v)) <;> rfl
      · cases t₀.2 n <;> cases t₁.2 n <;> cases t₂.2 n <;>
          cases decide (n ∈ O) <;> rfl

theorem MVR_causalDeltaLaw : CausalDeltaLaw MVR := by
  intro C U A B e _ _ _ _ _ _ hA hB
  have hBinit : B = MVR.init :=
    isCanonicalState_empty (MVR_downset_empty C e) hB
  subst hBinit
  rcases e with ⟨ts, rid, op⟩
  cases op with
  | write v O =>
    refine Prod.ext (funext fun p => ?_) (funext fun n => ?_) <;>
      simp only [MVR_merge_eq, MVR_update_eq, mvrMerge, mvrUpdate,
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
    ρ = σ ++ o :: τ → mvrApplicable o (applySeq MVR.toUpdateSig MVR.init σ)

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
    ∀ n, (applySeq MVR.toUpdateSig MVR.init ρ).2 n = true → mvrTag (applySeq MVR.toUpdateSig MVR.init ρ) n := by
  induction ρ using List.reverseRecOn with
  | nil =>
      intro n h
      have : (applySeq MVR.toUpdateSig MVR.init ([] : List (Op MVROp))).2 n = false := rfl
      rw [this] at h
      exact Bool.noConfusion h
  | append_singleton ρ o ih =>
      intro n h
      obtain ⟨ts, r, op⟩ := o
      cases op with
      | write w O =>
          rw [applySeq_append_single, MRDTSig.toUpdateSig_update,
            MVR_update_eq] at h ⊢
          simp only [mvrUpdate, Bool.or_eq_true, decide_eq_true_eq] at h
          simp only [mvrTag, mvrUpdate, Bool.or_eq_true, decide_eq_true_eq]
          rcases h with h' | h'
          · obtain ⟨v', hv'⟩ := ih (mvrOK_prefix hOK) n h'
            exact ⟨v', Or.inl hv'⟩
          · have hO := (hOK ρ (ts, r, .write w O) [] (by simp)).2 w O rfl n
            obtain ⟨⟨v', hv'⟩, -⟩ := hO.mp h'
            exact ⟨v', Or.inl hv'⟩

theorem mvr_seq_sound {ρ : List (Op MVROp)} (hOK : mvrOK ρ) (v : ℕ) :
    mvrView (applySeq MVR.toUpdateSig MVR.init ρ) v ↔ mvrSpecFold ρ = some v := by
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
          rw [applySeq_append_single, MRDTSig.toUpdateSig_update,
            MVR_update_eq, mvrSpecFold_snoc]
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
            have hnotag : ¬ mvrTag (applySeq MVR.toUpdateSig MVR.init ρ) ts := by
              rintro ⟨v', hv'⟩
              rw [hfresh v'] at hv'
              exact Bool.noConfusion hv'
            have h1 : (applySeq MVR.toUpdateSig MVR.init ρ).2 ts = false := by
              cases hh : (applySeq MVR.toUpdateSig MVR.init ρ).2 ts with
              | false => rfl
              | true =>
                  exact absurd (mvr_over_tags (mvrOK_prefix hOK) ts hh) hnotag
            have h2 : ts ∉ O := fun hin => hnotag ((hO ts).mp hin).1
            exact ⟨ts, Or.inr ⟨rfl, rfl⟩, h1, h2⟩

theorem MVR_canonicalJoinLaws : CanonicalJoinLaws MVR where
  core := MVR_joinCoreLaws
  delta := MVR_feasibleDeltaLaws
  causal_delta := MVR_causalDeltaLaw

theorem mvrJoin : Join MVR := MVR_canonicalJoinLaws.join

def generation : Issuance MVR where
  CanIssue := mvrApplicable

def replayAdequacy : ReplayAdequacyCertificate MVR generation :=
  ReplayAdequacyCertificate.ofJoin generation mvrJoin

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

def writeValue (e : Op MVROp) : ℕ :=
  match e.2.2 with | .write v _ => v

def clientStep (s : Finset (ℕ × ℕ)) (e : Op MVROp) : Finset (ℕ × ℕ) :=
  insert (e.1, writeValue e) (s.filter (fun p => p.1 ∉ overwrites e))

/-- Overwrite targets must have been born, but need not still be live:
two concurrent writes can supersede the same previously visible write. -/
def clientLegal (ops : List (Op MVROp)) : Prop :=
  (ops.map Prod.fst).Nodup ∧
  ∀ pre e post, ops = pre ++ e :: post →
    ∀ n ∈ overwrites e, n ∈ pre.map Prod.fst

def queryValues (s : Finset (ℕ × ℕ)) : Set ℕ := {v | ∃ n, (n, v) ∈ s}

def clientSpec : SequentialSpec MVR where
  State := Finset (ℕ × ℕ)
  init := ∅
  step := clientStep
  Legal := clientLegal
  query := fun s _ => queryValues s

def stateRel (s : MVR.State) (q : Finset (ℕ × ℕ)) : Prop :=
  ∀ p, p ∈ q ↔ s.1 p = true ∧ s.2 p.1 = false

theorem fold_write_iff (ops : List (Op MVROp)) (p : ℕ × ℕ) :
    (applySeq MVR.toUpdateSig MVR.init ops).1 p = true ↔
      ∃ e ∈ ops, e.1 = p.1 ∧ writeValue e = p.2 := by
  constructor
  · intro h
    obtain ⟨e, he, O, hop, ht⟩ := MVR_fold_bound₁ h
    exact ⟨e, he, ht, by simp [writeValue, hop]⟩
  · rintro ⟨⟨t, r, ⟨v, O⟩⟩, he, ht, hv⟩
    have h := MVR_contrib₁ he
    simpa [writeValue] using (show
      (applySeq MVR.toUpdateSig MVR.init ops).1 p = true from by
        have hp : p = (t, v) := Prod.ext ht.symm hv.symm
        simpa [hp] using h)

theorem fold_overwrite_iff (ops : List (Op MVROp)) (n : ℕ) :
    (applySeq MVR.toUpdateSig MVR.init ops).2 n = true ↔
      ∃ e ∈ ops, n ∈ overwrites e := by
  constructor
  · intro h
    obtain ⟨e, he, v, O, hop, hn⟩ := MVR_fold_bound₂ h
    exact ⟨e, he, by simpa [overwrites, hop] using hn⟩
  · rintro ⟨⟨t, r, ⟨v, O⟩⟩, he, hn⟩
    exact MVR_contrib₂ he hn

/-- Every named overwrite is a birth visible to the issuer. -/
theorem issued_overwrite {C : Configuration MVR}
    (exec : CertifiedExecution MVR generation C) {b : Op MVROp}
    (hb : b ∈ C.events) {n : ℕ} (hn : n ∈ overwrites b) :
    ∃ a ∈ C.events, C.vis a b ∧ a.1 = n := by
  obtain ⟨ops, hp, _, hg⟩ := exec.mintHonest b hb
  obtain ⟨t, r, ⟨v, O⟩⟩ := b
  obtain ⟨⟨w, hw⟩, _⟩ := (hg.2 v O rfl n).mp hn
  obtain ⟨a, ha, ht, _⟩ := (fold_write_iff ops (n, w)).mp hw
  exact ⟨a, ((hp.2 a).mp ha).1, ((hp.2 a).mp ha).2, ht⟩

theorem issued_overwrite_lt {C : Configuration MVR}
    (exec : CertifiedExecution MVR generation C) {b : Op MVROp}
    (hb : b ∈ C.events) {n : ℕ} (hn : n ∈ overwrites b) : n < b.1 := by
  obtain ⟨a, _, hv, ht⟩ := issued_overwrite exec hb hn
  simpa [ht] using C.causal_mono hv

/-- On an issued write, the timestamp guard is already implied by the
observed-overwrite payload. This is the client-facing form of replayOrder. -/
theorem replayOrder_iff_overwrite_of_execution {C : Configuration MVR}
    (exec : CertifiedExecution MVR generation C) {a b : Op MVROp}
    (hb : b ∈ C.events) :
    MVR.toUpdateSig.replayBefore a b ↔ a.1 ∈ overwrites b := by
  rw [replayOrder_before_iff]
  exact ⟨And.right, fun h => ⟨issued_overwrite_lt exec hb h, h⟩⟩

theorem overwrite_iff_successor {C : Configuration MVR}
    (exec : CertifiedExecution MVR generation C) {E : Set (Op MVROp)}
    (hin : ∀ e ∈ E, e ∈ C.events)
    (hclosed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    {a : Op MVROp} (ha : a ∈ E) :
    (∃ b ∈ E, a.1 ∈ overwrites b) ↔ ∃ b ∈ E, C.vis a b := by
  constructor
  · rintro ⟨b, hb, hn⟩
    obtain ⟨birth, hm, hv, ht⟩ := issued_overwrite exec (hin b hb) hn
    have heq := C.replayContext.ts_unique hm (hin a ha) ht
    exact ⟨b, hb, heq ▸ hv⟩
  · rintro ⟨b, hb, hv⟩
    obtain ⟨ops, hp, _, hg⟩ := exec.mintHonest b (hin b hb)
    have hai : a ∈ ops := (hp.2 a).mpr ⟨hin a ha, hv⟩
    have hwrite := (fold_write_iff ops (a.1, writeValue a)).mpr ⟨a, hai, rfl, rfl⟩
    cases hov : (applySeq MVR.toUpdateSig MVR.init ops).2 a.1 with
    | true =>
      obtain ⟨c, hc, hn⟩ := (fold_overwrite_iff ops a.1).mp hov
      exact ⟨c, hclosed c b ((hp.2 c).mp hc).2 hb, hn⟩
    | false =>
      obtain ⟨t, r, ⟨v, O⟩⟩ := b
      exact ⟨(t, r, .write v O), hb, (hg.2 v O rfl a.1).mpr
        ⟨⟨writeValue a, hwrite⟩, hov⟩⟩

/-- Every stored version exposes exactly its causally maximal writes. -/
theorem version_maximal {C : Configuration MVR}
    (exec : CertifiedExecution MVR generation C)
    {v : Version} {s : MVR.State} {E : Set (Op MVROp)}
    (hver : C.ver v = some (s, E)) (p : ℕ × ℕ) :
    (s.1 p = true ∧ s.2 p.1 = false) ↔
      ∃ a ∈ E, a.1 = p.1 ∧ writeValue a = p.2 ∧ ∀ b ∈ E, ¬ C.vis a b := by
  have hcfg := exec.canonicalConfig (fun C _ => mvrJoin C.replayContext)
  obtain ⟨ops, hp, _, hf⟩ := hcfg.canonical v s E hver
  have hin := hcfg.version_events_supported v s E hver
  have hc := hcfg.version_events_causal v s E hver
  rw [← hf]
  constructor
  · rintro ⟨hw, ho⟩
    obtain ⟨a, ha, ht, hv⟩ := (fold_write_iff ops p).mp hw
    refine ⟨a, (hp.2 a).mp ha, ht, hv, ?_⟩
    intro b hb hab
    obtain ⟨c, hce, hn⟩ := (overwrite_iff_successor exec hin hc ((hp.2 a).mp ha)).mpr ⟨b, hb, hab⟩
    have ht' := (fold_overwrite_iff ops p.1).mpr ⟨c, (hp.2 c).mpr hce, ht ▸ hn⟩
    rw [ho] at ht'
    contradiction
  · rintro ⟨a, ha, ht, hv, hmax⟩
    refine ⟨(fold_write_iff ops p).mpr ⟨a, (hp.2 a).mpr ha, ht, hv⟩, ?_⟩
    cases ho : (applySeq MVR.toUpdateSig MVR.init ops).2 p.1 with
    | false => rfl
    | true =>
      obtain ⟨c, hc', hn⟩ := (fold_overwrite_iff ops p.1).mp ho
      obtain ⟨b, hb, hab⟩ := (overwrite_iff_successor exec hin hc ha).mp
        ⟨c, (hp.2 c).mp hc', ht.symm ▸ hn⟩
      exact (hmax b hb hab).elim

def chronological (ops : List (Op MVROp)) : List (Op MVROp) :=
  ops.mergeSort (fun a b => a.1 ≤ b.1)

theorem chronological_perm (ops : List (Op MVROp)) : (chronological ops).Perm ops :=
  List.mergeSort_perm _ _

theorem chronological_sorted (ops : List (Op MVROp)) :
    (chronological ops).Pairwise (fun a b => a.1 ≤ b.1) := by
  have htrans : ∀ a b c : Op MVROp, decide (a.1 ≤ b.1) = true →
      decide (b.1 ≤ c.1) = true → decide (a.1 ≤ c.1) = true := by
    intro a b c hab hbc
    exact decide_eq_true (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
  have htotal : ∀ a b : Op MVROp,
      (decide (a.1 ≤ b.1) || decide (b.1 ≤ a.1)) = true := by
    intro a b
    simpa using le_total a.1 b.1
  have h := List.pairwise_mergeSort htrans htotal ops
  simpa [chronological] using h

theorem chronological_respects (C : Configuration MVR) (E : Set (Op MVROp))
    (ops : List (Op MVROp)) : respects (chronological ops) (loOn C.replayContext E) := by
  apply (chronological_sorted ops).imp
  intro a b hab hlo
  rcases hlo with hvis | hrc
  · exact (not_lt_of_ge hab) (C.causal_mono hvis.1)
  · exact (not_lt_of_ge hab) ((replayOrder_before_iff b a).mp hrc.2.2.1).1

/-- Sorted witnesses fold to precisely the live finite set, without keeping
births or overwrite logs in the abstract state. -/
theorem fold_refines : ∀ ops : List (Op MVROp),
    ops.Pairwise (fun a b => a.1 ≤ b.1) →
    (∀ e ∈ ops, ∀ n ∈ overwrites e, n < e.1) →
    stateRel (applySeq MVR.toUpdateSig MVR.init ops) (clientSpec.run ops) := by
  intro ops
  induction ops using List.reverseRecOn with
  | nil =>
    intro _ _ p
    simp [clientSpec, SequentialSpec.run, SequentialMachine.run,
      applySeq, MVR_init_eq]
  | append_singleton pre e ih =>
    intro hs hb
    have hpre := (List.pairwise_append.mp hs).1
    have hbound : ∀ a ∈ pre, ∀ n ∈ overwrites a, n < a.1 :=
      fun a ha => hb a (List.mem_append_left _ ha)
    have heBound := hb e (by simp)
    have hbefore : ∀ a ∈ pre, a.1 ≤ e.1 := by
      intro a ha
      exact (List.pairwise_append.mp hs).2.2 a ha e (by simp)
    have hfresh : (applySeq MVR.toUpdateSig MVR.init pre).2 e.1 = false := by
      cases h : (applySeq MVR.toUpdateSig MVR.init pre).2 e.1 with
      | false => rfl
      | true =>
        obtain ⟨a, ha, hn⟩ := (fold_overwrite_iff pre e.1).mp h
        exact ((not_lt_of_ge (hbefore a ha)) (hbound a ha e.1 hn)).elim
    have hself : e.1 ∉ overwrites e := fun h => (Nat.lt_irrefl _) (heBound e.1 h)
    have hi := ih hpre hbound
    intro p
    rw [SequentialSpec.run_append_single, applySeq_append_single]
    obtain ⟨t, r, ⟨v, O⟩⟩ := e
    change p ∈ clientStep (clientSpec.run pre) (t, r, .write v O) ↔
      (mvrUpdate (applySeq MVR.toUpdateSig MVR.init pre) (t, r, .write v O)).1 p = true ∧
      (mvrUpdate (applySeq MVR.toUpdateSig MVR.init pre) (t, r, .write v O)).2 p.1 = false
    by_cases hp : p = (t, v)
    · subst p
      simp [clientStep, writeValue, mvrUpdate, hfresh, show t ∉ O from hself]
    · simp [clientStep, writeValue, overwrites, mvrUpdate, hp, hi p, and_assoc]

theorem chronological_legal {C : Configuration MVR}
    (exec : CertifiedExecution MVR generation C) {E : Set (Op MVROp)}
    (hin : ∀ e ∈ E, e ∈ C.events)
    (hclosed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    {ops : List (Op MVROp)} (hp : listPermOf ops E) :
    clientSpec.Legal (chronological ops) := by
  have hperm : listPermOf (chronological ops) E :=
    ⟨(chronological_perm ops).symm.nodup hp.1,
      fun a => (chronological_perm ops).mem_iff.trans (hp.2 a)⟩
  have hnd : ((chronological ops).map Prod.fst).Nodup := by
    apply hperm.1.map_on
    intro a ha b hb ht
    exact C.replayContext.ts_unique (hin a ((hperm.2 a).mp ha))
      (hin b ((hperm.2 b).mp hb)) ht
  refine ⟨hnd, ?_⟩
  intro pre e post hsplit n hn
  have he : e ∈ E := (hperm.2 e).mp (by rw [hsplit]; simp)
  obtain ⟨a, ha, hv, ht⟩ := issued_overwrite exec (hin e he) hn
  have hain : a ∈ chronological ops := (hperm.2 a).mpr (hclosed a e hv he)
  rw [hsplit, List.mem_append, List.mem_cons] at hain
  rcases hain with ha | rfl | ha
  · exact List.mem_map.mpr ⟨a, ha, ht⟩
  · exact ((Nat.lt_irrefl _) (C.causal_mono hv)).elim
  · have hsort := chronological_sorted ops
    rw [hsplit] at hsort
    have hle := (List.pairwise_cons.mp (List.pairwise_append.mp hsort).2.1).1 a ha
    exact ((not_lt_of_ge hle) (C.causal_mono hv)).elim

def clientSequentialCorrectness : SequentialCorrectnessCertificate MVR generation replayOrder clientSpec stateRel where
  sound C exec replay := by
    intro v s E hver
    have hcfg := exec.canonicalConfig (fun C _ => mvrJoin C.replayContext)
    have hin := hcfg.version_events_supported v s E hver
    have hc := hcfg.version_events_causal v s E hver
    obtain ⟨ops, hp, _, hf⟩ := replay v s E hver
    have hperm : listPermOf (chronological ops) E :=
      ⟨(chronological_perm ops).symm.nodup hp.1,
        fun a => (chronological_perm ops).mem_iff.trans (hp.2 a)⟩
    have hfold : applySeq MVR.toUpdateSig MVR.init (chronological ops) = s :=
      (applySeq_perm_of_all_comm (D' := MVR.toUpdateSig) MVR_all_comm
        (chronological_perm ops) MVR.init).trans hf
    have hrel := fold_refines (chronological ops) (chronological_sorted ops)
      (fun e he n hn => issued_overwrite_lt exec (hin e ((hperm.2 e).mp he)) hn)
    rw [hfold] at hrel
    refine ⟨chronological ops, hperm, chronological_respects C E ops,
      chronological_legal exec hin hc hp, hrel, ?_⟩
    intro q
    apply Set.ext
    intro value
    change (∃ n, s.1 (n, value) = true ∧ s.2 n = false) ↔
      queryValues (clientSpec.run (chronological ops)) value
    unfold queryValues
    exact exists_congr (fun n => (hrel (n, value)).symm)

noncomputable def verified : VerifiedMRDT MVR where
  issuance := generation
  replayOrder := replayOrder
  replayAdequacy := replayAdequacy
  Spec := clientSpec
  Rel := stateRel
  sequentialCorrectness := clientSequentialCorrectness

theorem mvr_correct {C : Configuration MVR} (exec : CertifiedExecution MVR generation C) :
    IsSpecLinearizable MVR replayOrder clientSpec stateRel C ∧
    (∀ v s E, C.ver v = some (s, E) → ∀ p : ℕ × ℕ,
      (s.1 p = true ∧ s.2 p.1 = false) ↔
        ∃ a ∈ E, a.1 = p.1 ∧ writeValue a = p.2 ∧ ∀ b ∈ E, ¬ C.vis a b) := by
  refine ⟨?_, fun _ _ _ hver p => version_maximal exec hver p⟩
  cases exec with
  | ordinary h => exact verified.correct h
  | virtual h => exact verified.correctV h

theorem linear_register {ops : List (Op MVROp)}
    (h : LinearMintHistory MVR generation.CanIssue ops) :
    MVR.query (applySeq MVR.toUpdateSig MVR.init ops) () =
      {v | mvrSpecFold ops = some v} := by
  apply Set.ext
  intro v
  apply mvr_seq_sound
  simpa [mvrOK, generation] using h.guarded

end LeanProofs.Implementations.MVRegister.MVR
