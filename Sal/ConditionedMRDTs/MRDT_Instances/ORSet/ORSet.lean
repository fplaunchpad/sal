import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge

/-!
# OR-Set — flat VC discharge and the conditioned capstone

Split out of the original monolithic `MRDT_Instances.lean`; declarations
verbatim, names unchanged.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §1. The OR-Set mirror -/

/-- OR-Set ops (production `app_op_t`). -/
inductive ORSetOp : Type where
  | add : ℕ → ORSetOp
  | rem : ℕ → ORSetOp
deriving DecidableEq

/-- Production `do_`: `Add e` at ts stakes the tag `(ts, e)`; `Rem e` filters
every tag of `e`. -/
def orUpdate (s : (ℕ × ℕ) → Bool) (o : Op ORSetOp) : (ℕ × ℕ) → Bool :=
  match o.2.2 with
  | .add e => fun t => s t || decide (t = (o.1, e))
  | .rem e => fun t => s t && !(decide (t.2 = e))

/-- Production three-way merge: `(l ∩ a ∩ b) ∪ (a ∖ l) ∪ (b ∖ l)` — the
T8.6 shape, on tagged elements. -/
def orMergeL (l a b : (ℕ × ℕ) → Bool) : (ℕ × ℕ) → Bool :=
  fun t => (l t && (a t && b t)) || ((a t && !(l t)) || (b t && !(l t)))

/-- Production `rc`: Add-vs-Rem on the same element is ordered rem-first
(add-wins); all other pairs `Either`. -/
def orRc (o₁ o₂ : Op ORSetOp) : RcRes :=
  match o₁.2.2, o₂.2.2 with
  | .add e₁, .rem e₂ => if e₁ = e₂ then RcRes.Snd_then_fst else RcRes.Either
  | .rem e₁, .add e₂ => if e₁ = e₂ then RcRes.Fst_then_snd else RcRes.Either
  | _, _ => RcRes.Either

/-- The OR-Set MRDT (mirror of `Sal/MRDTs/OR_Set/OR_Set_MRDT.lean`). -/
noncomputable def ORSet : ConditionedMRDTSig where
  State := (ℕ × ℕ) → Bool
  dec_state := fun _ _ => Classical.propDecidable _
  init := fun _ => false
  AppOp := ORSetOp
  dec_op := inferInstance
  Query := Unit
  Value := (ℕ × ℕ) → Bool
  update := orUpdate
  merge := fun a b => orMergeL (fun _ => false) a b
  query := fun s _ => s
  rc := orRc
  mergeL := orMergeL
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem ORSet_update_eq (s : ORSet.State) (o : Op ORSet.AppOp) :
    ORSet.update s o = orUpdate s o := rfl

theorem ORSet_mergeL_eq (l a b : ORSet.State) :
    ORSet.mergeL l a b = orMergeL l a b := rfl

theorem ORSet_init_eq : ORSet.init = fun _ => false := rfl

/-- OR-Set `mergeL` is commutative in its branch arguments. -/
theorem ORSet_mergeL_comm (l a b : ORSet.State) :
    ORSet.mergeL l a b = ORSet.mergeL l b a := by
  funext t
  show orMergeL l a b t = orMergeL l b a t
  unfold orMergeL
  cases l t <;> cases a t <;> cases b t <;> rfl

/-! ## The OR-Set discharge -/

/-! ## §1. Pointwise infrastructure -/

/-- Updates are pointwise: agreement at a point is transported. -/
theorem orUpdate_pointwise (a b : ORSet.State) (o : Op ORSet.AppOp)
    (p : ℕ × ℕ) (h : a p = b p) :
    ORSet.update a o p = ORSet.update b o p := by
  rcases o with ⟨ts, rid, op⟩
  cases op with
  | add e =>
    show (a p || decide (p = (ts, e))) = (b p || decide (p = (ts, e)))
    rw [h]
  | rem e =>
    show (a p && !(decide (p.2 = e))) = (b p && !(decide (p.2 = e)))
    rw [h]

/-- Folds transport pointwise agreement (off any fixed point, in particular). -/
theorem orsApplySeq_agree {a b : ORSet.State}
    (π : List (Op ORSet.AppOp)) (p : ℕ × ℕ) (h : a p = b p) :
    applySeq ORSet.toCRDTSig a π p = applySeq ORSet.toCRDTSig b π p := by
  induction π generalizing a b with
  | nil => exact h
  | cons o π ih => exact ih (orUpdate_pointwise a b o p h)

/-! ## §2. Commutation classification -/

theorem ORSet_commutes_symm {o₁ o₂ : Op ORSet.AppOp}
    (h : ORSet.toCRDTSig.commutes o₁ o₂) :
    ORSet.toCRDTSig.commutes o₂ o₁ :=
  fun s => (h s).symm

theorem ORSet_comm_add_add (ts₁ r₁ x₁ ts₂ r₂ x₂ : ℕ) :
    ORSet.toCRDTSig.commutes (ts₁, r₁, ORSetOp.add x₁)
      (ts₂, r₂, ORSetOp.add x₂) := by
  intro s
  funext p
  show ((s p || decide (p = (ts₁, x₁))) || decide (p = (ts₂, x₂)))
     = ((s p || decide (p = (ts₂, x₂))) || decide (p = (ts₁, x₁)))
  cases hs : s p <;> cases h1 : decide (p = (ts₁, x₁)) <;>
    cases h2 : decide (p = (ts₂, x₂)) <;> rfl

theorem ORSet_comm_rem_rem (ts₁ r₁ x₁ ts₂ r₂ x₂ : ℕ) :
    ORSet.toCRDTSig.commutes (ts₁, r₁, ORSetOp.rem x₁)
      (ts₂, r₂, ORSetOp.rem x₂) := by
  intro s
  funext p
  show ((s p && !(decide (p.2 = x₁))) && !(decide (p.2 = x₂)))
     = ((s p && !(decide (p.2 = x₂))) && !(decide (p.2 = x₁)))
  cases hs : s p <;> cases h1 : decide (p.2 = x₁) <;>
    cases h2 : decide (p.2 = x₂) <;> rfl

theorem ORSet_comm_add_rem_ne (ts₁ r₁ x ts₂ r₂ y : ℕ) (hxy : x ≠ y) :
    ORSet.toCRDTSig.commutes (ts₁, r₁, ORSetOp.add x)
      (ts₂, r₂, ORSetOp.rem y) := by
  intro s
  funext p
  show ((s p || decide (p = (ts₁, x))) && !(decide (p.2 = y)))
     = ((s p && !(decide (p.2 = y))) || decide (p = (ts₁, x)))
  by_cases hp : p = (ts₁, x)
  · subst hp
    have hy : decide (((ts₁, x) : ℕ × ℕ).2 = y) = false :=
      decide_eq_false hxy
    rw [hy, decide_eq_true (show ((ts₁, x) : ℕ × ℕ) = (ts₁, x) from rfl)]
    cases s (ts₁, x) <;> rfl
  · rw [decide_eq_false hp]
    cases hs : s p <;> cases hd : decide (p.2 = y) <;> rfl

theorem ORSet_ncomm_add_rem (ts₁ r₁ ts₂ r₂ x : ℕ) :
    ¬ ORSet.toCRDTSig.commutes (ts₁, r₁, ORSetOp.add x)
      (ts₂, r₂, ORSetOp.rem x) := by
  intro h
  have h0 := congrFun (h ORSet.init) (ts₁, x)
  have h0' : ((false || decide (((ts₁, x) : ℕ × ℕ) = (ts₁, x)))
      && !(decide (((ts₁, x) : ℕ × ℕ).2 = x)))
      = ((false && !(decide (((ts₁, x) : ℕ × ℕ).2 = x)))
      || decide (((ts₁, x) : ℕ × ℕ) = (ts₁, x))) := h0
  simp at h0'

/-- The classification: an `Add x` fails to commute only with `Rem x`. -/
theorem ORSet_ncomm_add_dest {ts r x : ℕ} {o : Op ORSet.AppOp}
    (h : ¬ ORSet.toCRDTSig.commutes (ts, r, ORSetOp.add x) o) :
    o.2.2 = ORSetOp.rem x := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | add y => exact absurd (ORSet_comm_add_add ts r x ts' r' y) h
  | rem y =>
    by_cases hxy : x = y
    · subst hxy; rfl
    · exact absurd (ORSet_comm_add_rem_ne ts r x ts' r' y hxy) h

/-- The classification: a `Rem x` fails to commute only with `Add x`. -/
theorem ORSet_ncomm_rem_dest {ts r x : ℕ} {o : Op ORSet.AppOp}
    (h : ¬ ORSet.toCRDTSig.commutes (ts, r, ORSetOp.rem x) o) :
    o.2.2 = ORSetOp.add x := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | add y =>
    by_cases hxy : y = x
    · subst hxy; rfl
    · exact absurd
        (ORSet_commutes_symm (ORSet_comm_add_rem_ne ts' r' y ts r x hxy)) h
  | rem y => exact absurd (ORSet_comm_rem_rem ts r x ts' r' y) h

/-! ## §3. The update layer of `CoreVCs3CD` -/

theorem ORSet_no_rc_chain :
    ∀ o₁ o₂ o₃ : Op ORSet.AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ (ORSet.toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∧
         ORSet.toCRDTSig.rc o₂ o₃ = RcRes.Fst_then_snd) := by
  rintro ⟨ts₁, r₁, op₁⟩ ⟨ts₂, r₂, op₂⟩ ⟨ts₃, r₃, op₃⟩ _ _ ⟨h1, h2⟩
  cases op₂ with
  | add x₂ =>
    cases op₃ with
    | add x₃ => exact RcRes.noConfusion (show RcRes.Either = _ from h2)
    | rem x₃ =>
      have h2' : (if x₂ = x₃ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := h2
      by_cases hx : x₂ = x₃
      · rw [if_pos hx] at h2'; exact RcRes.noConfusion h2'
      · rw [if_neg hx] at h2'; exact RcRes.noConfusion h2'
  | rem x₂ =>
    cases op₁ with
    | add x₁ =>
      have h1' : (if x₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := h1
      by_cases hx : x₁ = x₂
      · rw [if_pos hx] at h1'; exact RcRes.noConfusion h1'
      · rw [if_neg hx] at h1'; exact RcRes.noConfusion h1'
    | rem x₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h1)

theorem ORSet_rc_non_comm_directional :
    ∀ o₁ o₂ : Op ORSet.AppOp,
      distinctOps o₁ o₂ → differentReplicas o₁ o₂ →
      (¬ ORSet.toCRDTSig.commutes o₁ o₂ ↔
       (ORSet.toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∨
        ORSet.toCRDTSig.rc o₂ o₁ = RcRes.Fst_then_snd)) := by
  intro o₁ o₂ _ _
  constructor
  · intro hnc
    rcases o₁ with ⟨ts₁, r₁, op₁⟩
    cases op₁ with
    | add x =>
      have h2 := ORSet_ncomm_add_dest hnc
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      have h2' : op₂ = ORSetOp.rem x := h2
      subst h2'
      right
      show (if x = x then RcRes.Fst_then_snd else RcRes.Either)
          = RcRes.Fst_then_snd
      rw [if_pos rfl]
    | rem x =>
      have h2 := ORSet_ncomm_rem_dest hnc
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      have h2' : op₂ = ORSetOp.add x := h2
      subst h2'
      left
      show (if x = x then RcRes.Fst_then_snd else RcRes.Either)
          = RcRes.Fst_then_snd
      rw [if_pos rfl]
  · rintro (h | h)
    · rcases o₁ with ⟨ts₁, r₁, op₁⟩
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      cases op₁ with
      | add x₁ =>
        exfalso
        cases op₂ with
        | add x₂ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | rem x₂ =>
          have h' : (if x₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₁ = x₂
          · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
          · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
      | rem x₁ =>
        cases op₂ with
        | add x₂ =>
          have h' : (if x₁ = x₂ then RcRes.Fst_then_snd else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₁ = x₂
          · subst hx
            intro hc
            exact ORSet_ncomm_add_rem ts₂ r₂ ts₁ r₁ x₁
              (ORSet_commutes_symm hc)
          · rw [if_neg hx] at h'
            exact absurd h' (fun hh => RcRes.noConfusion hh)
        | rem x₂ =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)
    · rcases o₁ with ⟨ts₁, r₁, op₁⟩
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      cases op₂ with
      | add x₂ =>
        exfalso
        cases op₁ with
        | add x₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | rem x₁ =>
          have h' : (if x₂ = x₁ then RcRes.Snd_then_fst else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₂ = x₁
          · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
          · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
      | rem x₂ =>
        cases op₁ with
        | add x₁ =>
          have h' : (if x₂ = x₁ then RcRes.Fst_then_snd else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₂ = x₁
          · subst hx
            exact ORSet_ncomm_add_rem ts₁ r₁ ts₂ r₂ x₂
          · rw [if_neg hx] at h'
            exact absurd h' (fun hh => RcRes.noConfusion hh)
        | rem x₁ =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)

/-- `cond_comm_lift`: the `Rem x`/`Add x` swap perturbs the state by at most
the fresh tag; the perturbation is pointwise-invisible off that tag, and the
final non-commuting `e''` (= `Rem x`) erases it. -/
theorem ORSet_cond_comm_lift :
    ∀ (s : ORSet.State) (e e' e'' : Op ORSet.AppOp)
      (π : List (Op ORSet.AppOp)),
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      ORSet.toCRDTSig.rc e e' = RcRes.Fst_then_snd →
      ¬ ORSet.toCRDTSig.commutes e' e'' →
      ORSet.update (applySeq ORSet.toCRDTSig
          (ORSet.update (ORSet.update s e') e) π) e''
        = ORSet.update (applySeq ORSet.toCRDTSig
            (ORSet.update (ORSet.update s e) e') π) e'' := by
  intro s e e' e'' π _ _ _ hrc hnc
  rcases e with ⟨ts₁, r₁, op₁⟩
  rcases e' with ⟨ts₂, r₂, op₂⟩
  -- rc = Fst forces (rem x, add x)
  cases op₁ with
  | add x₁ =>
    exfalso
    cases op₂ with
    | add x₂ => exact RcRes.noConfusion (show RcRes.Either = _ from hrc)
    | rem x₂ =>
      have h' : (if x₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := hrc
      by_cases hx : x₁ = x₂
      · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
      · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
  | rem x₁ =>
    cases op₂ with
    | rem x₂ =>
      exact absurd (show RcRes.Either = _ from hrc)
        (fun hh => RcRes.noConfusion hh)
    | add x₂ =>
      have h' : (if x₁ = x₂ then RcRes.Fst_then_snd else RcRes.Either)
          = RcRes.Fst_then_snd := hrc
      by_cases hx : x₁ = x₂
      swap
      · rw [if_neg hx] at h'; exact absurd h' (fun hh => RcRes.noConfusion hh)
      · subst hx
        -- e'' = rem x₁
        have hdest := ORSet_ncomm_add_dest hnc
        rcases e'' with ⟨ts₃, r₃, op₃⟩
        have hdest' : op₃ = ORSetOp.rem x₁ := hdest
        subst hdest'
        funext q
        show (applySeq ORSet.toCRDTSig
            (ORSet.update (ORSet.update s (ts₂, r₂, ORSetOp.add x₁))
              (ts₁, r₁, ORSetOp.rem x₁)) π q && !(decide (q.2 = x₁)))
          = (applySeq ORSet.toCRDTSig
              (ORSet.update (ORSet.update s (ts₁, r₁, ORSetOp.rem x₁))
                (ts₂, r₂, ORSetOp.add x₁)) π q && !(decide (q.2 = x₁)))
        by_cases hq2 : q.2 = x₁
        · rw [decide_eq_true hq2]
          simp
        · have hq : q ≠ (ts₂, x₁) := by
            intro h
            exact hq2 (by rw [h])
          have hagree :
              (ORSet.update (ORSet.update s (ts₂, r₂, ORSetOp.add x₁))
                (ts₁, r₁, ORSetOp.rem x₁)) q
              = (ORSet.update (ORSet.update s (ts₁, r₁, ORSetOp.rem x₁))
                  (ts₂, r₂, ORSetOp.add x₁)) q := by
            show ((s q || decide (q = (ts₂, x₁))) && !(decide (q.2 = x₁)))
              = ((s q && !(decide (q.2 = x₁))) || decide (q = (ts₂, x₁)))
            rw [decide_eq_false hq, decide_eq_false hq2]
            cases s q <;> rfl
          rw [orsApplySeq_agree π q hagree]

/-! ## §4. Fold facts -/

/-- **Bound**: a live tag has an adding event in the list. -/
theorem ORSet_fold_bound {ρ : List (Op ORSet.AppOp)} {p : ℕ × ℕ}
    (h : applySeq ORSet.toCRDTSig ORSet.init ρ p = true) :
    ∃ o ∈ ρ, o.2.2 = ORSetOp.add p.2 ∧ o.1 = p.1 := by
  induction ρ using List.reverseRecOn with
  | nil => exact absurd (show (false : Bool) = true from h) Bool.noConfusion
  | append_singleton ρ o ih =>
    rw [applySeq_append_single] at h
    rcases o with ⟨ts, rid, op⟩
    cases op with
    | add e =>
      have h' : (applySeq ORSet.toCRDTSig ORSet.init ρ p
          || decide (p = (ts, e))) = true := h
      cases hfa : applySeq ORSet.toCRDTSig ORSet.init ρ p with
      | true =>
        obtain ⟨o', ho', h1, h2⟩ := ih hfa
        exact ⟨o', List.mem_append_left _ ho', h1, h2⟩
      | false =>
        rw [hfa] at h'
        have hd : decide (p = (ts, e)) = true := by simpa using h'
        have hp' : p = (ts, e) := of_decide_eq_true hd
        refine ⟨(ts, rid, ORSetOp.add e),
          List.mem_append_right _ List.mem_cons_self, ?_, ?_⟩
        · show ORSetOp.add e = ORSetOp.add p.2
          rw [hp']
        · show ts = p.1
          rw [hp']
    | rem e =>
      have h' : (applySeq ORSet.toCRDTSig ORSet.init ρ p
          && !(decide (p.2 = e))) = true := h
      have h'' : applySeq ORSet.toCRDTSig ORSet.init ρ p = true :=
        (Bool.and_eq_true_iff.mp h').1
      obtain ⟨o', ho', h1, h2⟩ := ih h''
      exact ⟨o', List.mem_append_left _ ho', h1, h2⟩

/-- A dead tag stays dead if no event re-adds it. -/
theorem ORSet_fold_stays_false {p : ℕ × ℕ} :
    ∀ (β : List (Op ORSet.AppOp)) (s : ORSet.State),
      s p = false →
      (∀ o ∈ β, ¬(o.2.2 = ORSetOp.add p.2 ∧ o.1 = p.1)) →
      applySeq ORSet.toCRDTSig s β p = false := by
  intro β
  induction β with
  | nil => intro s hs _; exact hs
  | cons o β ih =>
    intro s hs hβ
    have hupd : ORSet.update s o p = false := by
      rcases o with ⟨ts, rid, op⟩
      cases op with
      | add e =>
        show (s p || decide (p = (ts, e))) = false
        rw [hs]
        cases hd : decide (p = (ts, e)) with
        | false => rfl
        | true =>
          exfalso
          have hp' : p = (ts, e) := of_decide_eq_true hd
          exact hβ _ List.mem_cons_self
            ⟨show ORSetOp.add e = ORSetOp.add p.2 by rw [hp'],
             show ts = p.1 by rw [hp']⟩
      | rem e =>
        show (s p && !(decide (p.2 = e))) = false
        rw [hs]
        rfl
    exact ih (ORSet.update s o) hupd
      (fun o' ho' => hβ o' (List.mem_cons_of_mem _ ho'))

/-- A live tag stays live if no same-element rem follows. -/
theorem ORSet_fold_stays_true {p : ℕ × ℕ} :
    ∀ (β : List (Op ORSet.AppOp)) (s : ORSet.State),
      s p = true →
      (∀ o ∈ β, o.2.2 ≠ ORSetOp.rem p.2) →
      applySeq ORSet.toCRDTSig s β p = true := by
  intro β
  induction β with
  | nil => intro s hs _; exact hs
  | cons o β ih =>
    intro s hs hβ
    have hupd : ORSet.update s o p = true := by
      rcases o with ⟨ts, rid, op⟩
      cases op with
      | add e =>
        show (s p || decide (p = (ts, e))) = true
        rw [hs]
        rfl
      | rem e =>
        show (s p && !(decide (p.2 = e))) = true
        rw [hs]
        have hne : p.2 ≠ e := by
          intro h
          exact hβ _ List.mem_cons_self (by rw [h])
        rw [decide_eq_false hne]
        rfl
    exact ih (ORSet.update s o) hupd
      (fun o' ho' => hβ o' (List.mem_cons_of_mem _ ho'))

/-! ## §5. The canonical-state σ-facts -/

/-- Live tags come from adds of the set. -/
theorem ORSet_canonical_bound
    {C : Sal.Emulation.Configuration ORSet.toCRDTSig}
    {F : Set (Op ORSet.AppOp)} {s : ORSet.State} {p : ℕ × ℕ}
    (hs : IsCanonicalState C F s) (hp : s p = true) :
    ∃ o ∈ F, o.2.2 = ORSetOp.add p.2 ∧ o.1 = p.1 := by
  obtain ⟨ρ, hperm, -, hfold⟩ := hs
  rw [← hfold] at hp
  obtain ⟨o, ho, h1, h2⟩ := ORSet_fold_bound hp
  exact ⟨o, (hperm.2 o).mp ho, h1, h2⟩

/-- **Kill**: a live tag admits no same-element rem vis-after its add. -/
theorem ORSet_live_no_later_rem
    {C : Sal.Emulation.Configuration ORSet.toCRDTSig}
    {F : Set (Op ORSet.AppOp)} {s : ORSet.State} {p : ℕ × ℕ}
    (h_in : ∀ o ∈ F, o ∈ C.events)
    (hs : IsCanonicalState C F s)
    (hp : s p = true)
    {tsa rda tsr rdr : ℕ}
    (haF : (tsa, rda, ORSetOp.add p.2) ∈ F) (haTs : tsa = p.1)
    (hrF : (tsr, rdr, ORSetOp.rem p.2) ∈ F)
    (hvis : C.vis (tsa, rda, ORSetOp.add p.2) (tsr, rdr, ORSetOp.rem p.2)) :
    False := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  rw [← hfold] at hp
  have hne_ar : (tsa, rda, ORSetOp.add p.2) ≠ (tsr, rdr, ORSetOp.rem p.2) := by
    intro h
    have := congrArg (fun o : Op ORSet.AppOp => o.2.2) h
    exact ORSetOp.noConfusion this
  have hnc : ¬ ORSet.toCRDTSig.commutes (tsa, rda, ORSetOp.add p.2)
      (tsr, rdr, ORSetOp.rem p.2) :=
    ORSet_ncomm_add_rem tsa rda tsr rdr p.2
  have hedge : loOn C F (tsa, rda, ORSetOp.add p.2)
      (tsr, rdr, ORSetOp.rem p.2) := Or.inl ⟨hvis, hnc⟩
  have hrρ : (tsr, rdr, ORSetOp.rem p.2) ∈ ρ := (hperm.2 _).mpr hrF
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem hrρ
  subst hsplit
  have haρ : (tsa, rda, ORSetOp.add p.2)
      ∈ α ++ (tsr, rdr, ORSetOp.rem p.2) :: β := (hperm.2 _).mpr haF
  have hmid := List.pairwise_cons.mp (List.pairwise_append.mp hresp).2.1
  have haα : (tsa, rda, ORSetOp.add p.2) ∈ α := by
    rcases List.mem_append.mp haρ with h | h
    · exact h
    · rcases List.mem_cons.mp h with h | h
      · exact absurd h hne_ar
      · exact absurd hedge (hmid.1 _ h)
  have hstep : applySeq ORSet.toCRDTSig ORSet.init
      (α ++ (tsr, rdr, ORSetOp.rem p.2) :: β)
      = applySeq ORSet.toCRDTSig
          (ORSet.update (applySeq ORSet.toCRDTSig ORSet.init α)
            (tsr, rdr, ORSetOp.rem p.2)) β := by
    simp [applySeq, List.foldl_append]
  rw [hstep] at hp
  have hkill : ORSet.update (applySeq ORSet.toCRDTSig ORSet.init α)
      (tsr, rdr, ORSetOp.rem p.2) p = false := by
    show (applySeq ORSet.toCRDTSig ORSet.init α p
        && !(decide (p.2 = p.2))) = false
    rw [decide_eq_true rfl]
    cases applySeq ORSet.toCRDTSig ORSet.init α p <;> rfl
  have hnoadd : ∀ o ∈ β, ¬(o.2.2 = ORSetOp.add p.2 ∧ o.1 = p.1) := by
    rintro o ho ⟨hoT, hoTs⟩
    have hoρ : o ∈ α ++ (tsr, rdr, ORSetOp.rem p.2) :: β :=
      List.mem_append_right _ (List.mem_cons_of_mem _ ho)
    have hoF : o ∈ F := (hperm.2 o).mp hoρ
    have hoa : o = (tsa, rda, ORSetOp.add p.2) := by
      by_contra hne
      exact distinctOps_of_events (h_in o hoF)
        (h_in _ haF) hne (hoTs.trans haTs.symm)
    rw [hoa] at ho
    have hnd := hperm.1
    rw [List.nodup_append] at hnd
    exact hnd.2.2 _ haα _ (List.mem_cons_of_mem _ ho) rfl
  rw [ORSet_fold_stays_false β _ hkill hnoadd] at hp
  exact Bool.noConfusion hp

/-- **Live**: an add with no same-element rem vis-after it yields a live
tag. -/
theorem ORSet_no_later_kill_live
    {C : Sal.Emulation.Configuration ORSet.toCRDTSig}
    {F : Set (Op ORSet.AppOp)} {s : ORSet.State} {p : ℕ × ℕ}
    (h_in : ∀ o ∈ F, o ∈ C.events)
    (hs : IsCanonicalState C F s)
    {rda : ℕ}
    (haF : (p.1, rda, ORSetOp.add p.2) ∈ F)
    (hno : ∀ r ∈ F, (r : Op ORSet.AppOp).2.2 = ORSetOp.rem p.2 →
      ¬ C.vis (p.1, rda, ORSetOp.add p.2) r) :
    s p = true := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  rw [← hfold]
  have haρ : (p.1, rda, ORSetOp.add p.2) ∈ ρ := (hperm.2 _).mpr haF
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem haρ
  subst hsplit
  have hcons := List.pairwise_cons.mp (List.pairwise_append.mp hresp).2.1
  -- no same-element rem in β
  have hnorem : ∀ o ∈ β, (o : Op ORSet.AppOp).2.2 ≠ ORSetOp.rem p.2 := by
    intro o ho hoT
    have hoF : o ∈ F := (hperm.2 o).mp
      (List.mem_append_right _ (List.mem_cons_of_mem _ ho))
    have hnovis : ¬ C.vis (p.1, rda, ORSetOp.add p.2) o := hno o hoF hoT
    rcases o with ⟨tso, rdo, opo⟩
    have hoT' : opo = ORSetOp.rem p.2 := hoT
    subst hoT'
    have hnc_oa : ¬ ORSet.toCRDTSig.commutes (tso, rdo, ORSetOp.rem p.2)
        (p.1, rda, ORSetOp.add p.2) :=
      fun h => ORSet_ncomm_add_rem p.1 rda tso rdo p.2
        (ORSet_commutes_symm h)
    have hedge : loOn C F (tso, rdo, ORSetOp.rem p.2)
        (p.1, rda, ORSetOp.add p.2) := by
      by_cases hvo : C.vis (tso, rdo, ORSetOp.rem p.2)
          (p.1, rda, ORSetOp.add p.2)
      · exact Or.inl ⟨hvo, hnc_oa⟩
      · refine Or.inr ⟨hvo, hnovis, ?_, ?_⟩
        · show (if p.2 = p.2 then RcRes.Fst_then_snd else RcRes.Either)
            = RcRes.Fst_then_snd
          rw [if_pos rfl]
        · rintro ⟨e₃, he₃F, hve₃, hnce₃⟩
          have h₃T := ORSet_ncomm_add_dest hnce₃
          exact hno e₃ he₃F h₃T hve₃
    exact hcons.1 _ ho hedge
  have hstep : applySeq ORSet.toCRDTSig ORSet.init
      (α ++ (p.1, rda, ORSetOp.add p.2) :: β)
      = applySeq ORSet.toCRDTSig
          (ORSet.update (applySeq ORSet.toCRDTSig ORSet.init α)
            (p.1, rda, ORSetOp.add p.2)) β := by
    simp [applySeq, List.foldl_append]
  rw [hstep]
  refine ORSet_fold_stays_true β _ ?_ hnorem
  show (applySeq ORSet.toCRDTSig ORSet.init α p
      || decide (p = (p.1, p.2))) = true
  have : decide (p = (p.1, p.2)) = true := decide_eq_true (by
    exact Prod.ext rfl rfl)
  rw [this]
  cases applySeq ORSet.toCRDTSig ORSet.init α p <;> rfl

/-! ## §6. The maximal-Rem trichotomy and `CDVC3` -/

/-- For a maximal `Rem x`, every live `x`-tag of `σ(U∖e)` is live in the
punctured downset. -/
theorem ORSet_rem_max_trichotomy
    {C : Sal.Emulation.Configuration ORSet.toCRDTSig}
    {U : Set (Op ORSet.AppOp)} {A B : ORSet.State}
    {ts rid x : ℕ}
    (h_in : ∀ o ∈ U, o ∈ C.events)
    (h_cl : ∀ a b, C.vis a b → ¬ ORSet.toCRDTSig.commutes a b →
      b ∈ U → a ∈ U)
    (h_e : (ts, rid, ORSetOp.rem x) ∈ U)
    (h_max : ∀ y ∈ U, y ≠ (ts, rid, ORSetOp.rem x) →
      ¬ loOn C U (ts, rid, ORSetOp.rem x) y)
    (hA : IsCanonicalState C (U \ {(ts, rid, ORSetOp.rem x)}) A)
    (hB : IsCanonicalState C
      (downset C (ts, rid, ORSetOp.rem x) \ {(ts, rid, ORSetOp.rem x)}) B)
    {p : ℕ × ℕ} (hpx : p.2 = x) (hpA : A p = true) :
    B p = true := by
  have h_inA : ∀ o ∈ U \ {(ts, rid, ORSetOp.rem x)}, o ∈ C.events :=
    fun o ho => h_in o ho.1
  have h_dsub : downset C (ts, rid, ORSetOp.rem x) ⊆ U :=
    downset_subset h_cl h_e
  have h_inB : ∀ o ∈ downset C (ts, rid, ORSetOp.rem x)
      \ {(ts, rid, ORSetOp.rem x)}, o ∈ C.events :=
    fun o ho => h_in o (h_dsub ho.1)
  -- the (unique) add of the live tag
  obtain ⟨a, haU', haT, haTs⟩ := ORSet_canonical_bound hA hpA
  rcases a with ⟨tsa, rda, opa⟩
  have haT' : opa = ORSetOp.add p.2 := haT
  subst haT'
  have haTs' : tsa = p.1 := haTs
  subst haTs'
  have hane : ((p.1, rda, ORSetOp.add p.2) : Op ORSet.AppOp)
      ≠ (ts, rid, ORSetOp.rem x) := haU'.2
  have hnc_ae : ¬ ORSet.toCRDTSig.commutes (p.1, rda, ORSetOp.add p.2)
      (ts, rid, ORSetOp.rem x) := by
    rw [← hpx]
    exact ORSet_ncomm_add_rem p.1 rda ts rid p.2
  by_cases hva : C.vis (p.1, rda, ORSetOp.add p.2) (ts, rid, ORSetOp.rem x)
  · -- vis-before: the add is in the punctured downset and live there
    have haD : (p.1, rda, ORSetOp.add p.2)
        ∈ downset C (ts, rid, ORSetOp.rem x) \ {(ts, rid, ORSetOp.rem x)} :=
      ⟨Or.inr (Relation.TransGen.single ⟨hva, hnc_ae⟩), hane⟩
    refine ORSet_no_later_kill_live h_inB hB haD ?_
    intro r hrD hrT hvar
    have hrU' : r ∈ U \ {(ts, rid, ORSetOp.rem x)} :=
      ⟨h_dsub hrD.1, hrD.2⟩
    rcases r with ⟨tsr, rdr, opr⟩
    have hrT' : opr = ORSetOp.rem p.2 := hrT
    subst hrT'
    exact ORSet_live_no_later_rem h_inA hA hpA haU' rfl hrU' hvar
  · by_cases hvea : C.vis (ts, rid, ORSetOp.rem x) (p.1, rda, ORSetOp.add p.2)
    · -- vis-after the maximal rem: a vis-edge out of e — contradiction
      exfalso
      have hnc_ea : ¬ ORSet.toCRDTSig.commutes (ts, rid, ORSetOp.rem x)
          (p.1, rda, ORSetOp.add p.2) :=
        fun h => hnc_ae (ORSet_commutes_symm h)
      exact h_max _ haU'.1 hane (Or.inl ⟨hvea, hnc_ea⟩)
    · -- concurrent: the rc-edge is unabsorbed — contradiction
      exfalso
      refine h_max _ haU'.1 hane (Or.inr ⟨hvea, hva, ?_, ?_⟩)
      · show (if x = p.2 then RcRes.Fst_then_snd else RcRes.Either)
            = RcRes.Fst_then_snd
        rw [hpx, if_pos rfl]
      · rintro ⟨e₃, he₃U, hve₃, hnce₃⟩
        have h₃T := ORSet_ncomm_add_dest hnce₃
        have h₃ne : e₃ ≠ (ts, rid, ORSetOp.rem x) := by
          intro h
          rw [h] at hve₃
          exact hva hve₃
        rcases e₃ with ⟨ts₃, rd₃, op₃⟩
        have h₃T' : op₃ = ORSetOp.rem p.2 := h₃T
        subst h₃T'
        exact ORSet_live_no_later_rem h_inA hA hpA haU' rfl
          ⟨he₃U, h₃ne⟩ hve₃

/-- **`CDVC3` for the OR-Set.** `Add`-maximal: pure set algebra plus tag
freshness. `Rem`-maximal: the trichotomy. -/
theorem ORSet_cdVC3 : CDVC3 ORSet := by
  intro C U A B e h_tr h_ir h_in h_cl h_e h_max hA hB
  rcases e with ⟨ts, rid, op⟩
  cases op with
  | add x =>
    have hBt : B (ts, x) = false := by
      cases hBt : B (ts, x) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨o, hoB, hoT, hoTs⟩ := ORSet_canonical_bound hB hBt
        have hoU : o ∈ U := downset_subset h_cl h_e hoB.1
        exact distinctOps_of_events (h_in o hoU) (h_in _ h_e) hoB.2 hoTs
    funext p
    show ((B p && (A p && ORSet.update B (ts, rid, ORSetOp.add x) p))
        || ((A p && !(B p))
        || (ORSet.update B (ts, rid, ORSetOp.add x) p && !(B p))))
      = (A p || decide (p = (ts, x)))
    show ((B p && (A p && (B p || decide (p = (ts, x)))))
        || ((A p && !(B p))
        || ((B p || decide (p = (ts, x))) && !(B p))))
      = (A p || decide (p = (ts, x)))
    by_cases hp : p = (ts, x)
    · subst hp
      rw [hBt, decide_eq_true rfl]
      cases A (ts, x) <;> rfl
    · rw [decide_eq_false hp]
      cases B p <;> cases A p <;> rfl
  | rem x =>
    have himp : ∀ q : ℕ × ℕ, q.2 = x → A q = true → B q = true :=
      fun q hqx hqA =>
        ORSet_rem_max_trichotomy h_in h_cl h_e h_max hA hB hqx hqA
    funext p
    show ((B p && (A p && ORSet.update B (ts, rid, ORSetOp.rem x) p))
        || ((A p && !(B p))
        || (ORSet.update B (ts, rid, ORSetOp.rem x) p && !(B p))))
      = (A p && !(decide (p.2 = x)))
    show ((B p && (A p && (B p && !(decide (p.2 = x)))))
        || ((A p && !(B p))
        || ((B p && !(decide (p.2 = x))) && !(B p))))
      = (A p && !(decide (p.2 = x)))
    by_cases hx : p.2 = x
    · rw [decide_eq_true hx]
      cases hBp : B p with
      | true => cases A p <;> rfl
      | false =>
        cases hAp : A p with
        | false => rfl
        | true => exact Bool.noConfusion (hBp.symm.trans (himp p hx hAp))
    · rw [decide_eq_false hx]
      cases B p <;> cases A p <;> rfl

/-! ## §7. The feasible delta laws -/

/-- The redistribution law is a Boolean tautology for the OR-Set merge —
**unconditional**, all five states arbitrary. -/
theorem orMergeL_redistribute (B t₀ t₁ t₂ u : ORSet.State) :
    orMergeL (orMergeL B t₀ u) (orMergeL B t₁ u) (orMergeL B t₂ u)
      = orMergeL B (orMergeL t₀ t₁ t₂) u := by
  funext p
  show ((orMergeL B t₀ u p && (orMergeL B t₁ u p && orMergeL B t₂ u p))
      || ((orMergeL B t₁ u p && !(orMergeL B t₀ u p))
      || (orMergeL B t₂ u p && !(orMergeL B t₀ u p))))
    = ((B p && (orMergeL t₀ t₁ t₂ p && u p))
      || ((orMergeL t₀ t₁ t₂ p && !(B p)) || (u p && !(B p))))
  show ((((B p && (t₀ p && u p)) || ((t₀ p && !(B p)) || (u p && !(B p))))
      && (((B p && (t₁ p && u p)) || ((t₁ p && !(B p)) || (u p && !(B p))))
      && ((B p && (t₂ p && u p)) || ((t₂ p && !(B p)) || (u p && !(B p))))))
      || ((((B p && (t₁ p && u p)) || ((t₁ p && !(B p)) || (u p && !(B p))))
      && !(((B p && (t₀ p && u p)) || ((t₀ p && !(B p)) || (u p && !(B p))))))
      || (((B p && (t₂ p && u p)) || ((t₂ p && !(B p)) || (u p && !(B p))))
      && !(((B p && (t₀ p && u p)) || ((t₀ p && !(B p)) || (u p && !(B p))))))))
    = ((B p && (((t₀ p && (t₁ p && t₂ p)) || ((t₁ p && !(t₀ p))
      || (t₂ p && !(t₀ p)))) && u p))
      || ((((t₀ p && (t₁ p && t₂ p)) || ((t₁ p && !(t₀ p))
      || (t₂ p && !(t₀ p)))) && !(B p)) || (u p && !(B p))))
  cases B p <;> cases t₀ p <;> cases t₁ p <;> cases t₂ p <;>
    cases u p <;> rfl

/-- **The feasible delta contract for the OR-Set.** -/
theorem ORSet_feasibleDeltaVCs3 : FeasibleDeltaVCs3 ORSet := by
  refine ⟨?_, ?_, ?_⟩
  · -- feasible_init (holds unconditionally for the OR-Set)
    intro C ev s _ _
    funext p
    show ((false && (false && s p)) || ((false && !false)
        || (s p && !false))) = s p
    cases s p <;> rfl
  · -- feasible_local_redistribute
    intro C ev₁ ev₂ s₀ B t₁ s₂ e _ _ h_in₁ h_in₂ h_cl₁ h_cl₂ he₁ he₂
      h_max hc₀ hB ht₁ hc₂
    rcases e with ⟨ts, rid, op⟩
    cases op with
    | add x =>
      -- tag freshness against B and s₀
      have hBt : B (ts, x) = false := by
        cases hBt : B (ts, x) with
        | false => rfl
        | true =>
          exfalso
          obtain ⟨o, hoB, hoT, hoTs⟩ := ORSet_canonical_bound hB hBt
          have hoU : o ∈ ev₁ := downset_subset h_cl₁ he₁ hoB.1
          exact distinctOps_of_events (h_in₁ o hoU) (h_in₁ _ he₁)
            hoB.2 hoTs
      have hs₀t : s₀ (ts, x) = false := by
        cases hs₀t : s₀ (ts, x) with
        | false => rfl
        | true =>
          exfalso
          obtain ⟨o, ho₀, hoT, hoTs⟩ := ORSet_canonical_bound hc₀ hs₀t
          have hone : o ≠ (ts, rid, ORSetOp.add x) := by
            intro h
            rw [h] at ho₀
            exact he₂ ho₀.2
          exact distinctOps_of_events (h_in₁ o ho₀.1) (h_in₁ _ he₁)
            hone hoTs
      funext p
      show ((s₀ p && ((orMergeL B t₁ (ORSet.update B (ts, rid, ORSetOp.add x)) p) && s₂ p))
          || (((orMergeL B t₁ (ORSet.update B (ts, rid, ORSetOp.add x)) p) && !(s₀ p))
          || (s₂ p && !(s₀ p))))
        = ((B p && ((orMergeL s₀ t₁ s₂ p) && ORSet.update B (ts, rid, ORSetOp.add x) p))
          || (((orMergeL s₀ t₁ s₂ p) && !(B p))
          || (ORSet.update B (ts, rid, ORSetOp.add x) p && !(B p))))
      show ((s₀ p && (((B p && (t₁ p && (B p || decide (p = (ts, x)))))
          || ((t₁ p && !(B p)) || ((B p || decide (p = (ts, x))) && !(B p)))) && s₂ p))
          || ((((B p && (t₁ p && (B p || decide (p = (ts, x)))))
          || ((t₁ p && !(B p)) || ((B p || decide (p = (ts, x))) && !(B p)))) && !(s₀ p))
          || (s₂ p && !(s₀ p))))
        = ((B p && (((s₀ p && (t₁ p && s₂ p)) || ((t₁ p && !(s₀ p))
          || (s₂ p && !(s₀ p)))) && (B p || decide (p = (ts, x)))))
          || ((((s₀ p && (t₁ p && s₂ p)) || ((t₁ p && !(s₀ p))
          || (s₂ p && !(s₀ p)))) && !(B p))
          || ((B p || decide (p = (ts, x))) && !(B p))))
      by_cases hp : p = (ts, x)
      · subst hp
        rw [hBt, hs₀t, decide_eq_true rfl]
        cases t₁ (ts, x) <;> cases s₂ (ts, x) <;> rfl
      · rw [decide_eq_false hp]
        cases s₀ p <;> cases B p <;> cases t₁ p <;> cases s₂ p <;> rfl
    | rem x =>
      -- the X2 exclusion via the σ-facts
      have himp : ∀ q : ℕ × ℕ, q.2 = x → B q = true → s₂ q = true →
          s₀ q = true := by
        intro q hqx hqB hqs₂
        obtain ⟨a', ha'B, ha'T, ha'Ts⟩ := ORSet_canonical_bound hB hqB
        obtain ⟨a'', ha''₂, ha''T, ha''Ts⟩ := ORSet_canonical_bound hc₂ hqs₂
        have ha'U : a' ∈ ev₁ := downset_subset h_cl₁ he₁ ha'B.1
        have heq : a'' = a' := by
          by_contra hne
          exact distinctOps_of_events (h_in₂ a'' ha''₂) (h_in₁ a' ha'U)
            hne (ha''Ts.trans ha'Ts.symm)
        rcases a' with ⟨tsa, rda, opa⟩
        have ha'T' : opa = ORSetOp.add q.2 := ha'T
        subst ha'T'
        have ha'Ts' : tsa = q.1 := ha'Ts
        subst ha'Ts'
        have ha₀ : ((q.1, rda, ORSetOp.add q.2) : Op ORSet.AppOp)
            ∈ ev₁ ∩ ev₂ := ⟨ha'U, heq ▸ ha''₂⟩
        refine ORSet_no_later_kill_live (fun o ho => h_in₁ o ho.1)
          hc₀ ha₀ ?_
        intro r hr₀ hrT hvar
        rcases r with ⟨tsr, rdr, opr⟩
        have hrT' : opr = ORSetOp.rem q.2 := hrT
        subst hrT'
        exact ORSet_live_no_later_rem h_in₂ hc₂ hqs₂
          (heq ▸ ha''₂) rfl hr₀.2 hvar
      funext p
      show ((s₀ p && ((orMergeL B t₁ (ORSet.update B (ts, rid, ORSetOp.rem x)) p) && s₂ p))
          || (((orMergeL B t₁ (ORSet.update B (ts, rid, ORSetOp.rem x)) p) && !(s₀ p))
          || (s₂ p && !(s₀ p))))
        = ((B p && ((orMergeL s₀ t₁ s₂ p) && ORSet.update B (ts, rid, ORSetOp.rem x) p))
          || (((orMergeL s₀ t₁ s₂ p) && !(B p))
          || (ORSet.update B (ts, rid, ORSetOp.rem x) p && !(B p))))
      show ((s₀ p && (((B p && (t₁ p && (B p && !(decide (p.2 = x)))))
          || ((t₁ p && !(B p)) || ((B p && !(decide (p.2 = x))) && !(B p)))) && s₂ p))
          || ((((B p && (t₁ p && (B p && !(decide (p.2 = x)))))
          || ((t₁ p && !(B p)) || ((B p && !(decide (p.2 = x))) && !(B p)))) && !(s₀ p))
          || (s₂ p && !(s₀ p))))
        = ((B p && (((s₀ p && (t₁ p && s₂ p)) || ((t₁ p && !(s₀ p))
          || (s₂ p && !(s₀ p)))) && (B p && !(decide (p.2 = x)))))
          || ((((s₀ p && (t₁ p && s₂ p)) || ((t₁ p && !(s₀ p))
          || (s₂ p && !(s₀ p)))) && !(B p))
          || ((B p && !(decide (p.2 = x))) && !(B p))))
      by_cases hx : p.2 = x
      · rw [decide_eq_true hx]
        cases hBp : B p with
        | false =>
          cases s₀ p <;> cases t₁ p <;> cases s₂ p <;> rfl
        | true =>
          cases hs₀p : s₀ p with
          | true => cases t₁ p <;> cases s₂ p <;> rfl
          | false =>
            cases hs₂p : s₂ p with
            | false => cases t₁ p <;> rfl
            | true =>
              exact Bool.noConfusion
                (hs₀p.symm.trans (himp p hx hBp hs₂p))
      · rw [decide_eq_false hx]
        cases s₀ p <;> cases B p <;> cases t₁ p <;> cases s₂ p <;> rfl
  · -- feasible_redistribute: the unconditional tautology
    intro C ev₁ ev₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _ _
    exact orMergeL_redistribute B t₀ t₁ t₂ (ORSet.update B e)

/-! ## §8. The bundles and the end-to-end theorem -/

theorem ORSet_updateVCs : UpdateVCs ORSet.toCRDTSig :=
  ⟨ORSet_rc_non_comm_directional, ORSet_no_rc_chain, ORSet_cond_comm_lift⟩

theorem ORSet_coreVCs3CD : CoreVCs3CD ORSet :=
  ⟨ORSet_updateVCs, ORSet_mergeL_comm⟩

/-- The ternary Join Lemma for the production OR-Set. -/
theorem ORSet_joinLemma3 : JoinLemma3 ORSet :=
  join_lemma3_of_cd_feasible ORSet_coreVCs3CD ORSet_feasibleDeltaVCs3
    ORSet_cdVC3

open LabeledTS in
/-- **End-to-end RA-linearizability for the production OR-Set** — the first
LCA-sensitive, non-commuting real MRDT through the metatheory. -/
theorem ORSet_ra_linearizable3
    (C : Configuration ORSet)
    (hReach : (labeledTS3 ORSet).ReachableFrom
      (initConfig ORSet trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_join ORSet_joinLemma3 C hReach


/-! ## The conditioned capstone — identity instantiation of the generic framework -/

section
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.FlatGeneric

/-- **OR-Set over the generic framework.** -/
theorem ORSet_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.ConditionedMRDTs.ORSet) (WTop Sal.ConditionedMRDTs.ORSet)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.ORSet)
      (invInvVCTop Sal.ConditionedMRDTs.ORSet)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.ConditionedMRDTs.ORSet) (WTop Sal.ConditionedMRDTs.ORSet)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.ORSet)
      (invInvVCTop Sal.ConditionedMRDTs.ORSet) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.ConditionedMRDTs.ORSet
      Sal.ConditionedMRDTs.ORSet_coreVCs3CD Sal.ConditionedMRDTs.ORSet_feasibleDeltaVCs3
      Sal.ConditionedMRDTs.ORSet_cdVC3 trivial)) C hReach

#print axioms ORSet_ra_linearizable3_eq

end


/-! ## Adequacy through the contract spine -/

/-- **(weak, ⊤) corner recovered — the production OR-Set.** Its `Inv`/`applicable`
are `⊤` and its discharge is the set-shaped VC bundle, so its contract sits at
`𝒞 = weakClosure`. Adequacy is recovered by routing `ORSet_coreVCs3CD`,
`ORSet_feasibleDeltaVCs3`, `ORSet_cdVC3` through `ConditionedContract.ofVCs` —
the OR-Set's own `ORSet_ra_linearizable3` is untouched. -/
theorem ORSet_adequate_viaContract
    (C : Configuration ORSet)
    (hReach : (labeledTS3 ORSet).ReachableFrom (initConfig ORSet trivial) C) :
    IsRALinearizable3 C :=
  (ConditionedContract.ofVCs ORSet ORSet_coreVCs3CD ORSet_feasibleDeltaVCs3
    ORSet_cdVC3 trivial).adequate C hReach

end Sal.ConditionedMRDTs
