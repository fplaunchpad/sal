import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge

/-!
# Enable-wins flag — direct full-closure join and the conditioned capstone

Split out of the original monolithic `MRDT_Instances.lean`; declarations
verbatim, names unchanged.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §3. The Enable-wins flag mirror -/

/-- Enable-wins ops (production `app_op_t`). -/
inductive EWOp : Type where
  | enable
  | disable
deriving DecidableEq

/-- Production `merge_cf`: counter `a + b − l` (ℕ-truncated, as in
production), flag by the four-case enable-wins rule. -/
def ewMergeCF (l a b : ℕ × Bool) : ℕ × Bool :=
  (a.1 + b.1 - l.1,
    if a.2 && b.2 then true
    else if !a.2 && !b.2 then false
    else if a.2 then decide (a.1 > l.1)
    else decide (b.1 > l.1))

/-- Production `do_` through `mysel`: `Enable` bumps this replica's counter
and sets its flag; `Disable` clears every replica's flag. -/
def ewUpdate (s : ℕ → ℕ × Bool) (o : Op EWOp) : ℕ → ℕ × Bool :=
  match o.2.2 with
  | .enable => fun k => if k = o.2.1 then ((s o.2.1).1 + 1, true) else s k
  | .disable => fun k => ((s k).1, false)

/-- The Enable-wins flag MRDT (mirror of
`Sal/MRDTs/Enable_Wins_Flag/Enable_Wins_Flag_MRDT.lean`, `mysel`-semantics —
see the file header for the domain-tracking deviation). -/
noncomputable def EWFlag : ConditionedMRDTSig where
  State := ℕ → ℕ × Bool
  dec_state := fun _ _ => Classical.propDecidable _
  init := fun _ => (0, false)
  AppOp := EWOp
  dec_op := inferInstance
  Query := Unit
  Value := ℕ → ℕ × Bool
  update := ewUpdate
  merge := fun a b => fun k => ewMergeCF ((0 : ℕ), false) (a k) (b k)
  query := fun s _ => s
  rc := fun o₁ o₂ =>
    match o₁.2.2, o₂.2.2 with
    | .enable, .disable => RcRes.Snd_then_fst
    | .disable, .enable => RcRes.Fst_then_snd
    | _, _ => RcRes.Either
  mergeL := fun l a b => fun k => ewMergeCF (l k) (a k) (b k)
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem EWFlag_update_eq (s : EWFlag.State) (o : Op EWFlag.AppOp) :
    EWFlag.update s o = ewUpdate s o := rfl

theorem EWFlag_mergeL_eq (l a b : EWFlag.State) :
    EWFlag.mergeL l a b = fun k => ewMergeCF (l k) (a k) (b k) := rfl

theorem EWFlag_init_eq : EWFlag.init = fun _ => ((0 : ℕ), false) := rfl

/-- Enable-wins `mergeL` is commutative in its branch arguments. -/
theorem EWFlag_mergeL_comm (l a b : EWFlag.State) :
    EWFlag.mergeL l a b = EWFlag.mergeL l b a := by
  funext k
  show ewMergeCF (l k) (a k) (b k) = ewMergeCF (l k) (b k) (a k)
  unfold ewMergeCF
  cases h_a : (a k).2 <;> cases h_b : (b k).2 <;>
    simp [h_a, h_b] <;> omega

/-! ## The Enable-wins flag discharge -/

/-! ## §1. Pointwise value lemmas -/

theorem ewUpdate_en (s : EWFlag.State) (ts r : ℕ) (k : ℕ) :
    EWFlag.update s (ts, r, EWOp.enable) k
      = if k = r then ((s r).1 + 1, true) else s k := rfl

theorem ewUpdate_dis (s : EWFlag.State) (ts r : ℕ) (k : ℕ) :
    EWFlag.update s (ts, r, EWOp.disable) k = ((s k).1, false) := rfl

/-! ## §2. Commutation classification and the update layer -/

theorem EWFlag_commutes_symm {o₁ o₂ : Op EWFlag.AppOp}
    (h : EWFlag.toCRDTSig.commutes o₁ o₂) :
    EWFlag.toCRDTSig.commutes o₂ o₁ :=
  fun s => (h s).symm

theorem EWFlag_comm_en_en (ts₁ r₁ ts₂ r₂ : ℕ) :
    EWFlag.toCRDTSig.commutes (ts₁, r₁, EWOp.enable)
      (ts₂, r₂, EWOp.enable) := by
  intro s
  funext k
  show EWFlag.update (EWFlag.update s (ts₁, r₁, EWOp.enable))
      (ts₂, r₂, EWOp.enable) k
    = EWFlag.update (EWFlag.update s (ts₂, r₂, EWOp.enable))
      (ts₁, r₁, EWOp.enable) k
  rw [ewUpdate_en, ewUpdate_en, ewUpdate_en, ewUpdate_en, ewUpdate_en,
    ewUpdate_en]
  by_cases h12 : r₁ = r₂
  · subst h12
    by_cases hk : k = r₁ <;> simp [hk]
  · by_cases hk2 : k = r₂
    · subst hk2
      rw [if_pos rfl, if_neg (fun h => h12 h.symm), if_pos rfl,
        if_neg (fun h => h12 h.symm)]
    · rw [if_neg hk2]
      by_cases hk1 : k = r₁
      · subst hk1
        rw [if_pos rfl, if_pos rfl, if_neg h12]
      · rw [if_neg hk1, if_neg hk1, if_neg hk2]

theorem EWFlag_comm_dis_dis (ts₁ r₁ ts₂ r₂ : ℕ) :
    EWFlag.toCRDTSig.commutes (ts₁, r₁, EWOp.disable)
      (ts₂, r₂, EWOp.disable) :=
  fun s => rfl

theorem EWFlag_ncomm_en_dis (ts₁ r₁ ts₂ r₂ : ℕ) :
    ¬ EWFlag.toCRDTSig.commutes (ts₁, r₁, EWOp.enable)
      (ts₂, r₂, EWOp.disable) := by
  intro h
  have h0 := congrFun (h EWFlag.init) r₁
  simp [EWFlag_update_eq, ewUpdate, EWFlag_init_eq] at h0

/-- An Enable fails to commute only with a Disable. -/
theorem EWFlag_ncomm_en_dest {ts r : ℕ} {o : Op EWFlag.AppOp}
    (h : ¬ EWFlag.toCRDTSig.commutes (ts, r, EWOp.enable) o) :
    o.2.2 = EWOp.disable := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | enable => exact absurd (EWFlag_comm_en_en ts r ts' r') h
  | disable => rfl

/-- A Disable fails to commute only with an Enable. -/
theorem EWFlag_ncomm_dis_dest {ts r : ℕ} {o : Op EWFlag.AppOp}
    (h : ¬ EWFlag.toCRDTSig.commutes (ts, r, EWOp.disable) o) :
    o.2.2 = EWOp.enable := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | enable => rfl
  | disable => exact absurd (EWFlag_comm_dis_dis ts r ts' r') h

theorem EWFlag_no_rc_chain :
    ∀ o₁ o₂ o₃ : Op EWFlag.AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ (EWFlag.toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∧
         EWFlag.toCRDTSig.rc o₂ o₃ = RcRes.Fst_then_snd) := by
  rintro ⟨ts₁, r₁, op₁⟩ ⟨ts₂, r₂, op₂⟩ ⟨ts₃, r₃, op₃⟩ _ _ ⟨h1, h2⟩
  cases op₂ with
  | enable =>
    cases op₃ with
    | enable => exact RcRes.noConfusion (show RcRes.Either = _ from h2)
    | disable =>
      exact RcRes.noConfusion (show RcRes.Snd_then_fst = _ from h2)
  | disable =>
    cases op₁ with
    | enable =>
      exact RcRes.noConfusion (show RcRes.Snd_then_fst = _ from h1)
    | disable => exact RcRes.noConfusion (show RcRes.Either = _ from h1)

/-- The guarded field. NOTE (T10.7): the `differentReplicas` guard is NOT
load-bearing for the Enable-wins flag — it has no `rc = Either`
non-commuting pairs (same-replica Enables commute; Enable/Disable is
rc-ordered at any replica pair). -/
theorem EWFlag_rc_non_comm_directional :
    ∀ o₁ o₂ : Op EWFlag.AppOp,
      distinctOps o₁ o₂ → differentReplicas o₁ o₂ →
      (¬ EWFlag.toCRDTSig.commutes o₁ o₂ ↔
       (EWFlag.toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∨
        EWFlag.toCRDTSig.rc o₂ o₁ = RcRes.Fst_then_snd)) := by
  intro o₁ o₂ _ _
  constructor
  · intro hnc
    rcases o₁ with ⟨ts₁, r₁, op₁⟩
    cases op₁ with
    | enable =>
      have h2 := EWFlag_ncomm_en_dest hnc
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      have h2' : op₂ = EWOp.disable := h2
      subst h2'
      right
      rfl
    | disable =>
      have h2 := EWFlag_ncomm_dis_dest hnc
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      have h2' : op₂ = EWOp.enable := h2
      subst h2'
      left
      rfl
  · rintro (h | h)
    · rcases o₁ with ⟨ts₁, r₁, op₁⟩
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      cases op₁ with
      | enable =>
        exfalso
        cases op₂ with
        | enable => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | disable =>
          exact RcRes.noConfusion (show RcRes.Snd_then_fst = _ from h)
      | disable =>
        cases op₂ with
        | enable =>
          intro hc
          exact EWFlag_ncomm_en_dis ts₂ r₂ ts₁ r₁
            (EWFlag_commutes_symm hc)
        | disable =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)
    · rcases o₁ with ⟨ts₁, r₁, op₁⟩
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      cases op₂ with
      | enable =>
        exfalso
        cases op₁ with
        | enable => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | disable =>
          exact RcRes.noConfusion (show RcRes.Snd_then_fst = _ from h)
      | disable =>
        cases op₁ with
        | enable => exact EWFlag_ncomm_en_dis ts₁ r₁ ts₂ r₂
        | disable =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)

/-- Agreement invariant for `cond_comm_lift`: equal counters everywhere,
equal values off the perturbed key. -/
private noncomputable def ewAgree (r : ℕ) (a b : EWFlag.State) : Prop :=
  (∀ k, (a k).1 = (b k).1) ∧ ∀ k, k ≠ r → a k = b k

private theorem ewAgree_update {r : ℕ} {a b : EWFlag.State}
    (h : ewAgree r a b) (o : Op EWFlag.AppOp) :
    ewAgree r (EWFlag.update a o) (EWFlag.update b o) := by
  rcases o with ⟨ts, r', op⟩
  cases op with
  | enable =>
    constructor
    · intro k
      rw [ewUpdate_en, ewUpdate_en]
      by_cases hk : k = r'
      · rw [if_pos hk, if_pos hk]
        simp [h.1 r']
      · rw [if_neg hk, if_neg hk]
        exact h.1 k
    · intro k hk
      rw [ewUpdate_en, ewUpdate_en]
      by_cases hkr : k = r'
      · rw [if_pos hkr, if_pos hkr, h.1 r']
      · rw [if_neg hkr, if_neg hkr]
        exact h.2 k hk
  | disable =>
    constructor
    · intro k
      rw [ewUpdate_dis, ewUpdate_dis]
      simp [h.1 k]
    · intro k hk
      rw [ewUpdate_dis, ewUpdate_dis, h.1 k]

private theorem ewAgree_fold {r : ℕ} {a b : EWFlag.State}
    (h : ewAgree r a b) (π : List (Op EWFlag.AppOp)) :
    ewAgree r (applySeq EWFlag.toCRDTSig a π)
      (applySeq EWFlag.toCRDTSig b π) := by
  induction π generalizing a b with
  | nil => exact h
  | cons o π ih => exact ih (ewAgree_update h o)

theorem EWFlag_cond_comm_lift :
    ∀ (s : EWFlag.State) (e e' e'' : Op EWFlag.AppOp)
      (π : List (Op EWFlag.AppOp)),
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      EWFlag.toCRDTSig.rc e e' = RcRes.Fst_then_snd →
      ¬ EWFlag.toCRDTSig.commutes e' e'' →
      EWFlag.update (applySeq EWFlag.toCRDTSig
          (EWFlag.update (EWFlag.update s e') e) π) e''
        = EWFlag.update (applySeq EWFlag.toCRDTSig
            (EWFlag.update (EWFlag.update s e) e') π) e'' := by
  intro s e e' e'' π _ _ _ hrc hnc
  rcases e with ⟨ts₁, r₁, op₁⟩
  rcases e' with ⟨ts₂, r₂, op₂⟩
  cases op₁ with
  | enable =>
    exfalso
    cases op₂ with
    | enable => exact RcRes.noConfusion (show RcRes.Either = _ from hrc)
    | disable =>
      exact RcRes.noConfusion (show RcRes.Snd_then_fst = _ from hrc)
  | disable =>
    cases op₂ with
    | disable =>
      exact absurd (show RcRes.Either = _ from hrc)
        (fun hh => RcRes.noConfusion hh)
    | enable =>
      have hdest := EWFlag_ncomm_en_dest hnc
      rcases e'' with ⟨ts₃, r₃, op₃⟩
      have hdest' : op₃ = EWOp.disable := hdest
      subst hdest'
      -- prefixes agree on counters everywhere and off r₂ entirely
      have hpre : ewAgree r₂
          (EWFlag.update (EWFlag.update s (ts₂, r₂, EWOp.enable))
            (ts₁, r₁, EWOp.disable))
          (EWFlag.update (EWFlag.update s (ts₁, r₁, EWOp.disable))
            (ts₂, r₂, EWOp.enable)) := by
        constructor
        · intro k
          simp only [ewUpdate_dis, ewUpdate_en]
          by_cases hk : k = r₂ <;> simp [hk]
        · intro k hk
          simp only [ewUpdate_dis, ewUpdate_en]
          simp [hk]
      have hagree := ewAgree_fold hpre π
      funext k
      rw [ewUpdate_dis, ewUpdate_dis, hagree.1 k]

/-! ## §3. The counting layer -/

/-- Bool predicate: an Enable by replica `k`. -/
noncomputable def ewEnK (k : ℕ) (o : Op EWFlag.AppOp) : Bool :=
  decide (o.2.1 = k ∧ o.2.2 = EWOp.enable)

/-- The Enables-by-`k` of an event set. -/
def ewEnSet (k : ℕ) (F : Set (Op EWFlag.AppOp)) : Set (Op EWFlag.AppOp) :=
  {o | o ∈ F ∧ o.2.1 = k ∧ o.2.2 = EWOp.enable}

/-- The filtered enumeration enumerates the Enables-by-`k`. -/
theorem ew_filter_perm {ρ : List (Op EWFlag.AppOp)}
    {F : Set (Op EWFlag.AppOp)} (h : listPermOf ρ F) (k : ℕ) :
    listPermOf (ρ.filter (ewEnK k)) (ewEnSet k F) := by
  refine ⟨h.1.filter _, fun o => ?_⟩
  rw [List.mem_filter]
  constructor
  · rintro ⟨ho, hd⟩
    exact ⟨(h.2 o).mp ho, of_decide_eq_true hd⟩
  · rintro ⟨ho, hd⟩
    exact ⟨(h.2 o).mpr ho, decide_eq_true hd⟩

/-- Counts across nodup enumerations: same set, same count. -/
theorem ew_count_eq {l l' : List (Op EWFlag.AppOp)}
    {S : Set (Op EWFlag.AppOp)}
    (h : listPermOf l S) (h' : listPermOf l' S) : l.length = l'.length :=
  listPermOf_length_eq h h'

/-- Monotone counts along set inclusion. -/
theorem ew_count_le {l l' : List (Op EWFlag.AppOp)}
    {S S' : Set (Op EWFlag.AppOp)}
    (h : listPermOf l S) (h' : listPermOf l' S') (hsub : S ⊆ S') :
    l.length ≤ l'.length := by
  have hsp : List.Subperm l l' := by
    refine List.subperm_of_subset h.1 ?_
    intro a ha
    exact (h'.2 a).mpr (hsub ((h.2 a).mp ha))
  exact hsp.length_le

/-- Strict counts from a witness outside the smaller set. -/
theorem ew_count_lt {l l' : List (Op EWFlag.AppOp)}
    {S S' : Set (Op EWFlag.AppOp)} {x : Op EWFlag.AppOp}
    (h : listPermOf l S) (h' : listPermOf l' S') (hsub : S ⊆ S')
    (hx : x ∈ S') (hxn : x ∉ S) :
    l.length < l'.length := by
  have hnd : (x :: l).Nodup := by
    rw [List.nodup_cons]
    exact ⟨fun hmem => hxn ((h.2 x).mp hmem), h.1⟩
  have hsp : List.Subperm (x :: l) l' := by
    refine List.subperm_of_subset hnd ?_
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact (h'.2 a).mpr hx
    · exact (h'.2 a).mpr (hsub ((h.2 a).mp ha'))
  have hle := hsp.length_le
  simp only [List.length_cons] at hle
  omega

/-- Length splits along any Bool predicate. -/
theorem ew_filter_split {α : Type} (l : List α) (q : α → Bool) :
    l.length = (l.filter q).length
      + (l.filter (fun a => !(q a))).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hq : q a <;>
      simp [List.filter_cons, hq, ih] <;> omega

/-- The fold's counter at `k` counts the Enables-by-`k`. -/
theorem ew_fold_cnt (ρ : List (Op EWFlag.AppOp)) (k : ℕ) :
    (applySeq EWFlag.toCRDTSig EWFlag.init ρ k).1
      = (ρ.filter (ewEnK k)).length := by
  induction ρ using List.reverseRecOn with
  | nil => rfl
  | append_singleton ρ o ih =>
    rw [applySeq_append_single, List.filter_append, List.length_append]
    rcases o with ⟨ts, r, op⟩
    cases op with
    | enable =>
      rw [ewUpdate_en]
      by_cases hk : k = r
      · subst hk
        rw [if_pos rfl]
        have : ewEnK k (ts, k, EWOp.enable) = true :=
          decide_eq_true ⟨rfl, rfl⟩
        simp [List.filter_cons, this, ih]
      · rw [if_neg hk]
        have : ewEnK k (ts, r, EWOp.enable) = false :=
          decide_eq_false (fun ⟨hr, _⟩ => hk hr.symm)
        simp [List.filter_cons, this, ih]
    | disable =>
      rw [ewUpdate_dis]
      have : ewEnK k (ts, r, EWOp.disable) = false :=
        decide_eq_false (fun ⟨_, hop⟩ => EWOp.noConfusion hop)
      simp [List.filter_cons, this, ih]

/-! ## §4. The flag σ-facts -/

/-- List-level (K): a set flag has an Enable-by-`k` with no later Disable. -/
theorem ew_flag_split {ρ : List (Op EWFlag.AppOp)} {k : ℕ}
    (h : (applySeq EWFlag.toCRDTSig EWFlag.init ρ k).2 = true) :
    ∃ α w β, ρ = α ++ w :: β ∧ (w : Op EWFlag.AppOp).2.1 = k
      ∧ w.2.2 = EWOp.enable
      ∧ ∀ d ∈ β, (d : Op EWFlag.AppOp).2.2 ≠ EWOp.disable := by
  induction ρ using List.reverseRecOn with
  | nil => exact absurd (show (false : Bool) = true from h) Bool.noConfusion
  | append_singleton ρ o ih =>
    rw [applySeq_append_single] at h
    rcases o with ⟨ts, r, op⟩
    cases op with
    | enable =>
      rw [ewUpdate_en] at h
      by_cases hk : k = r
      · exact ⟨ρ, ((ts, r, EWOp.enable) : Op EWFlag.AppOp), [], rfl,
          hk.symm, rfl, fun d hd => absurd hd List.not_mem_nil⟩
      · rw [if_neg hk] at h
        obtain ⟨α, w, β, heq, hw1, hw2, hβ⟩ := ih h
        refine ⟨α, w, β ++ [((ts, r, EWOp.enable) : Op EWFlag.AppOp)],
          ?_, hw1, hw2, ?_⟩
        · rw [heq, List.append_assoc]
          rfl
        · intro d hd
          rcases List.mem_append.mp hd with hd | hd
          · exact hβ d hd
          · rw [List.mem_singleton] at hd
            subst hd
            exact fun hh => EWOp.noConfusion hh
    | disable =>
      rw [ewUpdate_dis] at h
      exact absurd h Bool.noConfusion

/-- The flag stays set if no Disable follows. -/
theorem ew_flag_stays {k : ℕ} :
    ∀ (β : List (Op EWFlag.AppOp)) (s : EWFlag.State),
      (s k).2 = true →
      (∀ d ∈ β, (d : Op EWFlag.AppOp).2.2 ≠ EWOp.disable) →
      (applySeq EWFlag.toCRDTSig s β k).2 = true := by
  intro β
  induction β with
  | nil => intro s hs _; exact hs
  | cons o β ih =>
    intro s hs hβ
    have hupd : (EWFlag.update s o k).2 = true := by
      rcases o with ⟨ts, r, op⟩
      cases op with
      | enable =>
        rw [ewUpdate_en]
        by_cases hk : k = r
        · rw [if_pos hk]
        · rw [if_neg hk]
          exact hs
      | disable =>
        exact absurd rfl (hβ _ List.mem_cons_self)
    exact ih (EWFlag.update s o) hupd
      (fun d hd => hβ d (List.mem_cons_of_mem _ hd))

/-- **(K)**: a set flag at `k` yields an Enable-by-`k` in the set with no
Disable of the set vis-after it. -/
theorem ew_flag_witness
    {C : Sal.Emulation.Configuration EWFlag.toCRDTSig}
    {F : Set (Op EWFlag.AppOp)} {s : EWFlag.State} {k : ℕ}
    (hs : IsCanonicalState C F s) (hf : (s k).2 = true) :
    ∃ w ∈ F, (w : Op EWFlag.AppOp).2.1 = k ∧ w.2.2 = EWOp.enable ∧
      ∀ d ∈ F, (d : Op EWFlag.AppOp).2.2 = EWOp.disable → ¬ C.vis w d := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  rw [← hfold] at hf
  obtain ⟨α, w, β, heq, hw1, hw2, hβ⟩ := ew_flag_split hf
  subst heq
  refine ⟨w, (hperm.2 w).mp (List.mem_append_right _ List.mem_cons_self),
    hw1, hw2, ?_⟩
  intro d hdF hdT hvis
  -- the edge w → d forces d after w; β has no disables; d ≠ w by shape
  have hnc : ¬ EWFlag.toCRDTSig.commutes w d := by
    rcases w with ⟨tsw, rw', opw⟩
    have hw2' : opw = EWOp.enable := hw2
    subst hw2'
    rcases d with ⟨tsd, rd, opd⟩
    have hdT' : opd = EWOp.disable := hdT
    subst hdT'
    exact EWFlag_ncomm_en_dis tsw rw' tsd rd
  have hedge : loOn C F w d := Or.inl ⟨hvis, hnc⟩
  have hdρ : d ∈ α ++ w :: β := (hperm.2 d).mpr hdF
  have hdw : d ≠ w := by
    intro h
    rw [h, hw2] at hdT
    exact EWOp.noConfusion hdT
  rcases List.mem_append.mp hdρ with hd | hd
  · -- d before w with a mandatory edge w → d: respects violation
    have hcross := (List.pairwise_append.mp hresp).2.2
    exact hcross d hd w List.mem_cons_self hedge
  · rcases List.mem_cons.mp hd with hd | hd
    · exact hdw hd
    · exact hβ d hd hdT

/-- **(L)**: an Enable-by-`k` with no Disable of the set vis-after it sets
the flag. -/
theorem ew_live_flag
    {C : Sal.Emulation.Configuration EWFlag.toCRDTSig}
    {F : Set (Op EWFlag.AppOp)} {s : EWFlag.State} {k tsw rw' : ℕ}
    (hs : IsCanonicalState C F s)
    (hwF : (tsw, rw', EWOp.enable) ∈ F) (hwk : rw' = k)
    (hno : ∀ d ∈ F, (d : Op EWFlag.AppOp).2.2 = EWOp.disable →
      ¬ C.vis (tsw, rw', EWOp.enable) d) :
    (s k).2 = true := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  rw [← hfold]
  have hwρ : ((tsw, rw', EWOp.enable) : Op EWFlag.AppOp) ∈ ρ :=
    (hperm.2 _).mpr hwF
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem hwρ
  subst hsplit
  have hcons := List.pairwise_cons.mp (List.pairwise_append.mp hresp).2.1
  have hnodis : ∀ d ∈ β, (d : Op EWFlag.AppOp).2.2 ≠ EWOp.disable := by
    intro d hd hdT
    have hdF : d ∈ F := (hperm.2 d).mp
      (List.mem_append_right _ (List.mem_cons_of_mem _ hd))
    have hnovis := hno d hdF hdT
    rcases d with ⟨tsd, rd, opd⟩
    have hdT' : opd = EWOp.disable := hdT
    subst hdT'
    have hnc_dw : ¬ EWFlag.toCRDTSig.commutes (tsd, rd, EWOp.disable)
        (tsw, rw', EWOp.enable) :=
      fun h => EWFlag_ncomm_en_dis tsw rw' tsd rd
        (EWFlag_commutes_symm h)
    by_cases hvd : C.vis (tsd, rd, EWOp.disable) (tsw, rw', EWOp.enable)
    · exact hcons.1 _ hd (Or.inl ⟨hvd, hnc_dw⟩)
    · refine hcons.1 _ hd (Or.inr ⟨hvd, hnovis, rfl, ?_⟩)
      rintro ⟨e₃, he₃F, hve₃, hnce₃⟩
      exact hno e₃ he₃F (EWFlag_ncomm_en_dest hnce₃) hve₃
  have hstep : applySeq EWFlag.toCRDTSig EWFlag.init
      (α ++ ((tsw, rw', EWOp.enable) : Op EWFlag.AppOp) :: β)
      = applySeq EWFlag.toCRDTSig
          (EWFlag.update (applySeq EWFlag.toCRDTSig EWFlag.init α)
            (tsw, rw', EWOp.enable)) β := by
    simp [applySeq, List.foldl_append]
  rw [hstep]
  refine ew_flag_stays β _ ?_ hnodis
  rw [ewUpdate_en, if_pos hwk.symm]

/-! ## §6. The direct join for the Enable-wins flag -/

/-- **The full-closure join lemma for the Enable-wins flag**, proved
directly per key: counters by inclusion–exclusion of enable-counts, flags by
the four-corner liveness analysis. The `fa ∧ ¬fb` corner is the
theorem-backed certification of the production `merge_flag` (see the file
header). -/
theorem EWFlag_joinLemma3F : JoinLemma3F EWFlag := by
  intro C F₁ F₂ l a b h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ hcl hca hcb
  classical
  have hU : UpdateVCs EWFlag.toCRDTSig :=
    ⟨EWFlag_rc_non_comm_directional, EWFlag_no_rc_chain,
     EWFlag_cond_comm_lift⟩
  have h_inU : ∀ o ∈ F₁ ∪ F₂, o ∈ C.events := by
    rintro o (h | h)
    · exact h_in₁ o h
    · exact h_in₂ o h
  obtain ⟨ρ₀, hp₀, -, hf₀⟩ := id hcl
  obtain ⟨ρ₁, hp₁, -, hf₁⟩ := id hca
  obtain ⟨ρ₂, hp₂, -, hf₂⟩ := id hcb
  have hpU := listPermOf_union (D := EWFlag.toCRDTSig) hp₁ hp₂
  obtain ⟨s, hcs⟩ : ∃ s, IsCanonicalState C (F₁ ∪ F₂) s :=
    isCanonicalState_exists_u hU h_tr h_ir hpU h_inU
  suffices hEq : EWFlag.mergeL l a b = s by
    rw [hEq]
    exact hcs
  obtain ⟨ρU, hpUU, -, hfU⟩ := id hcs
  -- pointwise values via the folds
  funext k
  -- counters
  have hcnt₀ : (l k).1 = (ρ₀.filter (ewEnK k)).length := by
    rw [← hf₀]; exact ew_fold_cnt ρ₀ k
  have hcnt₁ : (a k).1 = (ρ₁.filter (ewEnK k)).length := by
    rw [← hf₁]; exact ew_fold_cnt ρ₁ k
  have hcnt₂ : (b k).1 = (ρ₂.filter (ewEnK k)).length := by
    rw [← hf₂]; exact ew_fold_cnt ρ₂ k
  have hcntU : (s k).1 = (ρU.filter (ewEnK k)).length := by
    rw [← hfU]; exact ew_fold_cnt ρU k
  -- inclusion–exclusion of the enable counts
  have hpf₀ := ew_filter_perm hp₀ k
  have hpf₁ := ew_filter_perm hp₁ k
  have hpf₂ := ew_filter_perm hp₂ k
  have hpfU := ew_filter_perm hpUU k
  -- the explicit union enumeration splits the count
  have hIE : (ρU.filter (ewEnK k)).length + (ρ₀.filter (ewEnK k)).length
      = (ρ₁.filter (ewEnK k)).length + (ρ₂.filter (ewEnK k)).length := by
    -- X := enables of F₂ outside F₁, counted from ρ₂'s enumeration
    have hsplit := ew_filter_split (ρ₂.filter (ewEnK k))
      (fun o => decide (o ∈ F₁))
    -- the ∈F₁ part enumerates ewEnSet k (F₁ ∩ F₂)
    have hin_perm : listPermOf
        ((ρ₂.filter (ewEnK k)).filter (fun o => decide (o ∈ F₁)))
        (ewEnSet k (F₁ ∩ F₂)) := by
      refine ⟨hpf₂.1.filter _, fun o => ?_⟩
      rw [List.mem_filter]
      constructor
      · rintro ⟨ho, hd⟩
        have := (hpf₂.2 o).mp ho
        exact ⟨⟨of_decide_eq_true hd, this.1⟩, this.2⟩
      · rintro ⟨⟨ho₁, ho₂⟩, hok⟩
        exact ⟨(hpf₂.2 o).mpr ⟨ho₂, hok⟩, decide_eq_true ho₁⟩
    -- the ∉F₁ part enumerates ewEnSet k (F₂ \ F₁)
    have hout_perm : listPermOf
        ((ρ₂.filter (ewEnK k)).filter (fun o => !(decide (o ∈ F₁))))
        (ewEnSet k (F₂ \ F₁)) := by
      refine ⟨hpf₂.1.filter _, fun o => ?_⟩
      rw [List.mem_filter]
      constructor
      · rintro ⟨ho, hd⟩
        have hmem := (hpf₂.2 o).mp ho
        have hnot : o ∉ F₁ := by
          intro hin
          rw [decide_eq_true hin] at hd
          exact Bool.noConfusion hd
        exact ⟨⟨hmem.1, hnot⟩, hmem.2⟩
      · rintro ⟨⟨ho₂, hno₁⟩, hok⟩
        refine ⟨(hpf₂.2 o).mpr ⟨ho₂, hok⟩, ?_⟩
        rw [decide_eq_false hno₁]
        rfl
    -- the union enumeration's filter splits over ρ₁ and the fresh part
    have hUperm₂ : listPermOf
        ((ρ₂.filter (fun o => decide (o ∉ ρ₁))).filter (ewEnK k))
        (ewEnSet k (F₂ \ F₁)) := by
      refine ⟨(hp₂.1.filter _).filter _, fun o => ?_⟩
      rw [List.mem_filter, List.mem_filter]
      constructor
      · rintro ⟨⟨ho₂, hd₁⟩, hdk⟩
        have hno₁ : o ∉ F₁ := fun hin =>
          (of_decide_eq_true hd₁) ((hp₁.2 o).mpr hin)
        exact ⟨⟨(hp₂.2 o).mp ho₂, hno₁⟩, of_decide_eq_true hdk⟩
      · rintro ⟨⟨ho₂, hno₁⟩, hok⟩
        refine ⟨⟨(hp₂.2 o).mpr ho₂, ?_⟩, decide_eq_true hok⟩
        exact decide_eq_true (fun hmem => hno₁ ((hp₁.2 o).mp hmem))
    have hcU : (ρU.filter (ewEnK k)).length
        = ((ρ₁ ++ ρ₂.filter (fun o => decide (o ∉ ρ₁))).filter
            (ewEnK k)).length := by
      refine ew_count_eq hpfU (ew_filter_perm hpU k)
    rw [hcU, List.filter_append, List.length_append]
    have h1 : ((ρ₂.filter (fun o => decide (o ∉ ρ₁))).filter
        (ewEnK k)).length
        = ((ρ₂.filter (ewEnK k)).filter
            (fun o => !(decide (o ∈ F₁)))).length :=
      ew_count_eq hUperm₂ hout_perm
    have h2 : (ρ₀.filter (ewEnK k)).length
        = ((ρ₂.filter (ewEnK k)).filter
            (fun o => decide (o ∈ F₁))).length :=
      ew_count_eq hpf₀ hin_perm
    omega
  -- flags: (K)/(L) corner analysis
  -- the union-side liveness helper for a witness outside F₂
  have hliveU₁ : ∀ tsw rw', (tsw, rw', EWOp.enable) ∈ F₁ →
      ((tsw, rw', EWOp.enable) : Op EWFlag.AppOp) ∉ F₂ →
      (∀ d ∈ F₁, (d : Op EWFlag.AppOp).2.2 = EWOp.disable →
        ¬ C.vis (tsw, rw', EWOp.enable) d) →
      ∀ d ∈ F₁ ∪ F₂, (d : Op EWFlag.AppOp).2.2 = EWOp.disable →
        ¬ C.vis (tsw, rw', EWOp.enable) d := by
    intro tsw rw' hw hnF₂ hlive d hd hdT hvis
    rcases hd with hd | hd
    · exact hlive d hd hdT hvis
    · exact hnF₂ (h_cl₂ _ d hvis hd)
  -- the flag equation
  have hflag : (EWFlag.mergeL l a b k).2 = (s k).2 := by
    show (ewMergeCF (l k) (a k) (b k)).2 = (s k).2
    show (if (a k).2 && (b k).2 then true
        else if !(a k).2 && !(b k).2 then false
        else if (a k).2 then decide ((a k).1 > (l k).1)
        else decide ((b k).1 > (l k).1)) = (s k).2
    cases hfa : (a k).2 with
    | true =>
      cases hfb : (b k).2 with
      | true =>
        -- both live: the vis-later witness is union-live
        obtain ⟨wa, hwaF, hwak, hwaE, hwaL⟩ := ew_flag_witness hca hfa
        obtain ⟨wb, hwbF, hwbk, hwbE, hwbL⟩ := ew_flag_witness hcb hfb
        rcases wa with ⟨tsa, ra, opa⟩
        have : opa = EWOp.enable := hwaE
        subst this
        rcases wb with ⟨tsb, rb, opb⟩
        have : opb = EWOp.enable := hwbE
        subst this
        have hsU : (s k).2 = true := by
          by_cases hab : ((tsa, ra, EWOp.enable) : Op EWFlag.AppOp)
              = (tsb, rb, EWOp.enable)
          · refine ew_live_flag hcs (Or.inl hwaF) hwak ?_
            intro d hd hdT hvis
            rcases hd with hd | hd
            · exact hwaL d hd hdT hvis
            · rw [hab] at hvis
              exact hwbL d hd hdT hvis
          · obtain ⟨r1', s1', hL1, hs1⟩ := h_in₁ _ hwaF
            obtain ⟨r2', s2', hL2, hs2⟩ := h_in₂ _ hwbF
            have hrep : ra = rb := hwak.trans hwbk.symm
            rcases C.vis_total_same_replica hL1 hs1 hL2 hs2 hab hrep
              with hv | hv
            · -- wa before wb: wb is union-live
              refine ew_live_flag hcs (Or.inr hwbF) hwbk ?_
              intro d hd hdT hvis
              rcases hd with hd | hd
              · exact hwaL d hd hdT (h_tr hv hvis)
              · exact hwbL d hd hdT hvis
            · -- wb before wa: wa is union-live
              refine ew_live_flag hcs (Or.inl hwaF) hwak ?_
              intro d hd hdT hvis
              rcases hd with hd | hd
              · exact hwaL d hd hdT hvis
              · exact hwbL d hd hdT (h_tr hv hvis)
        rw [hsU]
        rfl
      | false =>
        -- fa ∧ ¬fb: the flag equals the counter comparison N₁ > N₀
        have hiff : (s k).2 = true ↔ (a k).1 > (l k).1 := by
          constructor
          · intro hsU
            obtain ⟨w, hwF, hwk, hwE, hwL⟩ := ew_flag_witness hcs hsU
            rcases w with ⟨tsw, rw', opw⟩
            have : opw = EWOp.enable := hwE
            subst this
            -- w is not in F₂ (else live there, contradicting ¬fb)
            have hwn₂ : ((tsw, rw', EWOp.enable) : Op EWFlag.AppOp)
                ∉ F₂ := by
              intro hw₂
              have : (b k).2 = true := by
                refine ew_live_flag hcb hw₂ hwk ?_
                intro d hd hdT hvis
                exact hwL d (Or.inr hd) hdT hvis
              rw [hfb] at this
              exact Bool.noConfusion this
            have hw₁ : ((tsw, rw', EWOp.enable) : Op EWFlag.AppOp)
                ∈ F₁ := by
              rcases hwF with h | h
              · exact h
              · exact absurd h hwn₂
            -- strict count via the witness
            rw [hcnt₁, hcnt₀]
            exact ew_count_lt hpf₀ hpf₁
              (fun o ho => ⟨ho.1.1, ho.2⟩)
              ⟨hw₁, hwk, rfl⟩ (fun ho => hwn₂ ho.1.2)
          · intro hgt
            rw [hcnt₁, hcnt₀] at hgt
            -- a witness enable in F₁ outside F₀ exists
            have hwit : ∃ g ∈ ewEnSet k F₁, g ∉ ewEnSet k (F₁ ∩ F₂) := by
              by_contra hno
              push_neg at hno
              have := ew_count_le hpf₁ hpf₀ hno
              omega
            obtain ⟨g, hg₁, hg₀⟩ := hwit
            have hgn₂ : g ∉ F₂ := fun h =>
              hg₀ ⟨⟨hg₁.1, h⟩, hg₁.2⟩
            rcases g with ⟨tsg, rg, opg⟩
            have hgE : opg = EWOp.enable := hg₁.2.2
            subst hgE
            have hgk : rg = k := hg₁.2.1
            -- the live witness of a
            obtain ⟨wa, hwaF, hwak, hwaE, hwaL⟩ := ew_flag_witness hca hfa
            rcases wa with ⟨tsa, ra, opa⟩
            have : opa = EWOp.enable := hwaE
            subst this
            by_cases hwan₂ : ((tsa, ra, EWOp.enable) : Op EWFlag.AppOp)
                ∈ F₂
            · -- wa ∈ F₂: then g is after wa (full closure), and union-live
              have hgne : ((tsg, rg, EWOp.enable) : Op EWFlag.AppOp)
                  ≠ (tsa, ra, EWOp.enable) := by
                intro h
                rw [h] at hgn₂
                exact hgn₂ hwan₂
              obtain ⟨rg', sg', hLg, hsg⟩ := h_in₁ _ hg₁.1
              obtain ⟨ra', sa', hLa, hsa⟩ := h_in₁ _ hwaF
              have hrep : rg = ra := hgk.trans hwak.symm
              rcases C.vis_total_same_replica hLg hsg hLa hsa hgne hrep
                with hv | hv
              · -- vis g wa with wa ∈ F₂: full closure drags g into F₂ ✗
                exact absurd (h_cl₂ _ _ hv hwan₂) hgn₂
              · -- vis wa g: g is union-live
                refine ew_live_flag hcs (Or.inl hg₁.1) hgk ?_
                intro d hd hdT hvis
                rcases hd with hd | hd
                · exact hwaL d hd hdT (h_tr hv hvis)
                · exact hgn₂ (h_cl₂ _ d hvis hd)
            · -- wa ∉ F₂: wa itself is union-live
              refine ew_live_flag hcs (Or.inl hwaF) hwak
                (hliveU₁ tsa ra hwaF hwan₂ hwaL)
        by_cases hgt : (a k).1 > (l k).1
        · rw [decide_eq_true hgt, (hiff.mpr hgt)]
          rfl
        · have hsf : (s k).2 = false := by
            cases hsf : (s k).2 with
            | false => rfl
            | true => exact absurd (hiff.mp hsf) hgt
          rw [decide_eq_false hgt, hsf]
          rfl
    | false =>
      cases hfb : (b k).2 with
      | true =>
        -- ¬fa ∧ fb: mirror with N₂ > N₀
        have hiff : (s k).2 = true ↔ (b k).1 > (l k).1 := by
          constructor
          · intro hsU
            obtain ⟨w, hwF, hwk, hwE, hwL⟩ := ew_flag_witness hcs hsU
            rcases w with ⟨tsw, rw', opw⟩
            have : opw = EWOp.enable := hwE
            subst this
            have hwn₁ : ((tsw, rw', EWOp.enable) : Op EWFlag.AppOp)
                ∉ F₁ := by
              intro hw₁
              have : (a k).2 = true := by
                refine ew_live_flag hca hw₁ hwk ?_
                intro d hd hdT hvis
                exact hwL d (Or.inl hd) hdT hvis
              rw [hfa] at this
              exact Bool.noConfusion this
            have hw₂ : ((tsw, rw', EWOp.enable) : Op EWFlag.AppOp)
                ∈ F₂ := by
              rcases hwF with h | h
              · exact absurd h hwn₁
              · exact h
            rw [hcnt₂, hcnt₀]
            exact ew_count_lt hpf₀ hpf₂
              (fun o ho => ⟨ho.1.2, ho.2⟩)
              ⟨hw₂, hwk, rfl⟩ (fun ho => hwn₁ ho.1.1)
          · intro hgt
            rw [hcnt₂, hcnt₀] at hgt
            have hwit : ∃ g ∈ ewEnSet k F₂, g ∉ ewEnSet k (F₁ ∩ F₂) := by
              by_contra hno
              push_neg at hno
              have := ew_count_le hpf₂ hpf₀ hno
              omega
            obtain ⟨g, hg₂, hg₀⟩ := hwit
            have hgn₁ : g ∉ F₁ := fun h =>
              hg₀ ⟨⟨h, hg₂.1⟩, hg₂.2⟩
            rcases g with ⟨tsg, rg, opg⟩
            have hgE : opg = EWOp.enable := hg₂.2.2
            subst hgE
            have hgk : rg = k := hg₂.2.1
            obtain ⟨wb, hwbF, hwbk, hwbE, hwbL⟩ := ew_flag_witness hcb hfb
            rcases wb with ⟨tsb, rb, opb⟩
            have : opb = EWOp.enable := hwbE
            subst this
            by_cases hwbn₁ : ((tsb, rb, EWOp.enable) : Op EWFlag.AppOp)
                ∈ F₁
            · have hgne : ((tsg, rg, EWOp.enable) : Op EWFlag.AppOp)
                  ≠ (tsb, rb, EWOp.enable) := by
                intro h
                rw [h] at hgn₁
                exact hgn₁ hwbn₁
              obtain ⟨rg', sg', hLg, hsg⟩ := h_in₂ _ hg₂.1
              obtain ⟨rb', sb', hLb, hsb⟩ := h_in₂ _ hwbF
              have hrep : rg = rb := hgk.trans hwbk.symm
              rcases C.vis_total_same_replica hLg hsg hLb hsb hgne hrep
                with hv | hv
              · exact absurd (h_cl₁ _ _ hv hwbn₁) hgn₁
              · refine ew_live_flag hcs (Or.inr hg₂.1) hgk ?_
                intro d hd hdT hvis
                rcases hd with hd | hd
                · exact hgn₁ (h_cl₁ _ d hvis hd)
                · exact hwbL d hd hdT (h_tr hv hvis)
            · refine ew_live_flag hcs (Or.inr hwbF) hwbk ?_
              intro d hd hdT hvis
              rcases hd with hd | hd
              · exact hwbn₁ (h_cl₁ _ d hvis hd)
              · exact hwbL d hd hdT hvis
        by_cases hgt : (b k).1 > (l k).1
        · rw [decide_eq_true hgt, (hiff.mpr hgt)]
          rfl
        · have hsf : (s k).2 = false := by
            cases hsf : (s k).2 with
            | false => rfl
            | true => exact absurd (hiff.mp hsf) hgt
          rw [decide_eq_false hgt, hsf]
          rfl
      | false =>
        -- neither side live: the union flag is unset
        have hsf : (s k).2 = false := by
          cases hsf : (s k).2 with
          | false => rfl
          | true =>
            exfalso
            obtain ⟨w, hwF, hwk, hwE, hwL⟩ := ew_flag_witness hcs hsf
            rcases w with ⟨tsw, rw', opw⟩
            have : opw = EWOp.enable := hwE
            subst this
            rcases hwF with hw | hw
            · have : (a k).2 = true := by
                refine ew_live_flag hca hw hwk ?_
                intro d hd hdT hvis
                exact hwL d (Or.inl hd) hdT hvis
              rw [hfa] at this
              exact Bool.noConfusion this
            · have : (b k).2 = true := by
                refine ew_live_flag hcb hw hwk ?_
                intro d hd hdT hvis
                exact hwL d (Or.inr hd) hdT hvis
              rw [hfb] at this
              exact Bool.noConfusion this
        rw [hsf]
        rfl
  -- assemble the pair
  show ewMergeCF (l k) (a k) (b k) = s k
  have hcnt : (ewMergeCF (l k) (a k) (b k)).1 = (s k).1 := by
    show (a k).1 + (b k).1 - (l k).1 = (s k).1
    rw [hcnt₁, hcnt₂, hcnt₀, hcntU]
    have hle := ew_count_le hpf₀ hpf₂
      (fun o ho => ⟨ho.1.2, ho.2⟩)
    omega
  exact Prod.ext hcnt hflag

/-! ## §7. End-to-end -/

open LabeledTS in
/-- **End-to-end RA-linearizability for the production Enable-wins flag.** -/
theorem EWFlag_ra_linearizable3
    (C : Configuration EWFlag)
    (hReach : (labeledTS3 EWFlag).ReachableFrom
      (initConfig EWFlag trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_joinF EWFlag_joinLemma3F C hReach


/-! ## The conditioned capstone — identity instantiation of the generic framework -/

section
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.FlatGeneric

/-- **Enable-wins flag over the generic framework** (full-closure corner). -/
theorem EWFlag_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.ConditionedMRDTs.EWFlag) (WTop Sal.ConditionedMRDTs.EWFlag)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.EWFlag)
      (invInvVCTop Sal.ConditionedMRDTs.EWFlag)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.ConditionedMRDTs.EWFlag) (WTop Sal.ConditionedMRDTs.EWFlag)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.EWFlag)
      (invInvVCTop Sal.ConditionedMRDTs.EWFlag) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofJoinF Sal.ConditionedMRDTs.EWFlag
      Sal.ConditionedMRDTs.EWFlag_joinLemma3F trivial)) C hReach

#print axioms EWFlag_ra_linearizable3_eq

end


/-! ## Adequacy through the contract spine -/

/-- **(full, ⊤) corner recovered — the production Enable-wins flag.** Counter-
comparison merges need full causal closure, so its contract sits at
`𝒞 = fullClosure`. Adequacy is recovered by routing `EWFlag_joinLemma3F` through
`ConditionedContract.ofJoinF` — the flag's own `EWFlag_ra_linearizable3` is
untouched. -/
theorem EWFlag_adequate_viaContract
    (C : Configuration EWFlag)
    (hReach : (labeledTS3 EWFlag).ReachableFrom (initConfig EWFlag trivial) C) :
    IsRALinearizable3 C :=
  (ConditionedContract.ofJoinF EWFlag EWFlag_joinLemma3F trivial).adequate C hReach

end Sal.ConditionedMRDTs
