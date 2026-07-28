import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.ArbAdequacyReach
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge

/-!
# Add-Wins Priority Queue: flat VC discharge and the conditioned capstone

The production Add-Wins Priority Queue as a `ConditionedMRDTSig`, its
RA-linearizability VC discharge, and the conditioned capstone over the generic
framework.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## The Add-Wins Priority Queue discharge (feasible class)

Mirror of `Sal/MRDTs/Add_Win_Priority_Queue/Add_Win_Priority_Queue_MRDT.lean`:
the A-component (tagged `(ts, elem, value)` records; `Rmv` filter-kills by
element; `Add`-wins `rc` on the same element) is literally the OR-Set
pattern with a value payload, and the I-component (tagged `(ts, elem, amount)`
increments) is a grow-only accumulator that commutes with everything.  The
discharge is the OR-Set template on A with a second component that is either
inert (for `Add`/`Rmv` reasoning) or MVR-style grow-only (for `Inc`). -/

inductive AWPQOp : Type where
  | add : ℕ → ℕ → AWPQOp   -- elem, innate value
  | inc : ℕ → ℤ → AWPQOp   -- elem, amount
  | rmv : ℕ → AWPQOp        -- elem
deriving DecidableEq

/-- Production `do_`: `Add` records `(ts, e, v)` in A; `Inc` records
`(ts, e, a)` in I; `Rmv e` filter-kills A by element. -/
def awpqUpdate (s : ((ℕ × ℕ × ℕ) → Bool) × ((ℕ × ℕ × ℤ) → Bool))
    (o : Op AWPQOp) : ((ℕ × ℕ × ℕ) → Bool) × ((ℕ × ℕ × ℤ) → Bool) :=
  match o.2.2 with
  | .add e v => (fun t => s.1 t || decide (t = (o.1, e, v)), s.2)
  | .inc e a => (s.1, fun u => s.2 u || decide (u = (o.1, e, a)))
  | .rmv e   => (fun t => s.1 t && !(decide (t.2.1 = e)), s.2)

/-- Three-way merge: the OR-shape per component. -/
def awpqMergeL (l a b : ((ℕ × ℕ × ℕ) → Bool) × ((ℕ × ℕ × ℤ) → Bool)) :
    ((ℕ × ℕ × ℕ) → Bool) × ((ℕ × ℕ × ℤ) → Bool) :=
  (fun t => (l.1 t && (a.1 t && b.1 t))
      || ((a.1 t && !l.1 t) || (b.1 t && !l.1 t)),
   fun u => (l.2 u && (a.2 u && b.2 u))
      || ((a.2 u && !l.2 u) || (b.2 u && !l.2 u)))

/-- The Add-Wins Priority Queue MRDT. -/
noncomputable def AWPQ : ConditionedMRDTSig where
  State := ((ℕ × ℕ × ℕ) → Bool) × ((ℕ × ℕ × ℤ) → Bool)
  dec_state := fun _ _ => Classical.propDecidable _
  init := (fun _ => false, fun _ => false)
  AppOp := AWPQOp
  dec_op := inferInstance
  Query := Unit
  Value := ((ℕ × ℕ × ℕ) → Bool) × ((ℕ × ℕ × ℤ) → Bool)
  update := awpqUpdate
  merge := fun a b => awpqMergeL (fun _ => false, fun _ => false) a b
  query := fun s _ => s
  rc := fun o₁ o₂ =>
    match o₁.2.2, o₂.2.2 with
    | .add e₁ _, .rmv e₂ => if e₁ = e₂ then RcRes.Snd_then_fst else RcRes.Either
    | .rmv e₁, .add e₂ _ => if e₁ = e₂ then RcRes.Fst_then_snd else RcRes.Either
    | _, _ => RcRes.Either
  mergeL := awpqMergeL
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem AWPQ_update_eq (st : AWPQ.State) (o : Op AWPQ.AppOp) :
    AWPQ.update st o = awpqUpdate st o := rfl

theorem AWPQ_mergeL_eq (l a b : AWPQ.State) :
    AWPQ.mergeL l a b = awpqMergeL l a b := rfl

theorem AWPQ_init_eq :
    AWPQ.init = ((fun _ => false, fun _ => false) : AWPQ.State) := rfl

/-! ### §1. Pointwise infrastructure -/

/-- A-component of the fold depends only on the A-component of the start,
pointwise. -/
theorem awpqFold_fst_agree {a b : AWPQ.State}
    (π : List (Op AWPQ.AppOp)) (t : ℕ × ℕ × ℕ) (h : a.1 t = b.1 t) :
    (applySeq AWPQ.toCRDTSig a π).1 t = (applySeq AWPQ.toCRDTSig b π).1 t := by
  induction π generalizing a b with
  | nil => exact h
  | cons o π ih =>
    refine ih ?_
    rcases o with ⟨ts, rid, op⟩
    cases op with
    | add e v =>
      show (a.1 t || decide (t = (ts, e, v)))
          = (b.1 t || decide (t = (ts, e, v)))
      rw [h]
    | inc e am => exact h
    | rmv e =>
      show (a.1 t && !(decide (t.2.1 = e)))
          = (b.1 t && !(decide (t.2.1 = e)))
      rw [h]

/-- I-component of the fold depends only on the I-component of the start. -/
theorem awpqFold_snd_congr {a b : AWPQ.State}
    (π : List (Op AWPQ.AppOp)) (h : a.2 = b.2) :
    (applySeq AWPQ.toCRDTSig a π).2 = (applySeq AWPQ.toCRDTSig b π).2 := by
  induction π generalizing a b with
  | nil => exact h
  | cons o π ih =>
    refine ih ?_
    rcases o with ⟨ts, rid, op⟩
    cases op with
    | add e v => exact h
    | inc e am =>
      funext u
      show (a.2 u || decide (u = (ts, e, am)))
          = (b.2 u || decide (u = (ts, e, am)))
      rw [h]
    | rmv e => exact h

/-! ### §2. Commutation classification -/

theorem AWPQ_commutes_symm {o₁ o₂ : Op AWPQ.AppOp}
    (h : AWPQ.toCRDTSig.commutes o₁ o₂) :
    AWPQ.toCRDTSig.commutes o₂ o₁ :=
  fun s => (h s).symm

/-- `Inc` commutes with everything (it touches only the I-component; other
I-writers commute by or-reordering). -/
theorem AWPQ_comm_inc_left (ts r e : ℕ) (am : ℤ) (o : Op AWPQ.AppOp) :
    AWPQ.toCRDTSig.commutes (ts, r, AWPQOp.inc e am) o := by
  intro s
  rcases o with ⟨ts', r', op⟩
  cases op with
  | add e' v' =>
    refine Prod.ext (funext fun t => rfl) (funext fun u => rfl)
  | rmv e' =>
    refine Prod.ext (funext fun t => rfl) (funext fun u => rfl)
  | inc e' am' =>
    refine Prod.ext (funext fun t => rfl) (funext fun u => ?_)
    show ((s.2 u || decide (u = (ts, e, am))) || decide (u = (ts', e', am')))
        = ((s.2 u || decide (u = (ts', e', am'))) || decide (u = (ts, e, am)))
    cases s.2 u <;> cases hd₁ : decide (u = (ts, e, am)) <;>
      cases hd₂ : decide (u = (ts', e', am')) <;> rfl

theorem AWPQ_comm_add_add (ts₁ r₁ x₁ v₁ ts₂ r₂ x₂ v₂ : ℕ) :
    AWPQ.toCRDTSig.commutes (ts₁, r₁, AWPQOp.add x₁ v₁)
      (ts₂, r₂, AWPQOp.add x₂ v₂) := by
  intro s
  refine Prod.ext (funext fun t => ?_) (funext fun u => rfl)
  show ((s.1 t || decide (t = (ts₁, x₁, v₁))) || decide (t = (ts₂, x₂, v₂)))
      = ((s.1 t || decide (t = (ts₂, x₂, v₂))) || decide (t = (ts₁, x₁, v₁)))
  cases s.1 t <;> cases h1 : decide (t = (ts₁, x₁, v₁)) <;>
    cases h2 : decide (t = (ts₂, x₂, v₂)) <;> rfl

theorem AWPQ_comm_rmv_rmv (ts₁ r₁ x₁ ts₂ r₂ x₂ : ℕ) :
    AWPQ.toCRDTSig.commutes (ts₁, r₁, AWPQOp.rmv x₁)
      (ts₂, r₂, AWPQOp.rmv x₂) := by
  intro s
  refine Prod.ext (funext fun t => ?_) (funext fun u => rfl)
  show ((s.1 t && !(decide (t.2.1 = x₁))) && !(decide (t.2.1 = x₂)))
      = ((s.1 t && !(decide (t.2.1 = x₂))) && !(decide (t.2.1 = x₁)))
  cases s.1 t <;> cases h1 : decide (t.2.1 = x₁) <;>
    cases h2 : decide (t.2.1 = x₂) <;> rfl

theorem AWPQ_comm_add_rmv_ne (ts₁ r₁ x v ts₂ r₂ y : ℕ) (hxy : x ≠ y) :
    AWPQ.toCRDTSig.commutes (ts₁, r₁, AWPQOp.add x v)
      (ts₂, r₂, AWPQOp.rmv y) := by
  intro s
  refine Prod.ext (funext fun t => ?_) (funext fun u => rfl)
  show ((s.1 t || decide (t = (ts₁, x, v))) && !(decide (t.2.1 = y)))
      = ((s.1 t && !(decide (t.2.1 = y))) || decide (t = (ts₁, x, v)))
  by_cases ht : t = (ts₁, x, v)
  · subst ht
    have hy : decide (((ts₁, x, v) : ℕ × ℕ × ℕ).2.1 = y) = false :=
      decide_eq_false hxy
    rw [hy, decide_eq_true (show ((ts₁, x, v) : ℕ × ℕ × ℕ) = (ts₁, x, v)
      from rfl)]
    cases s.1 (ts₁, x, v) <;> rfl
  · rw [decide_eq_false ht]
    cases s.1 t <;> cases hd : decide (t.2.1 = y) <;> rfl

theorem AWPQ_ncomm_add_rmv (ts₁ r₁ ts₂ r₂ x v : ℕ) :
    ¬ AWPQ.toCRDTSig.commutes (ts₁, r₁, AWPQOp.add x v)
      (ts₂, r₂, AWPQOp.rmv x) := by
  intro h
  have h0 := congrArg Prod.fst (h AWPQ.init)
  have h0' := congrFun h0 (ts₁, x, v)
  have h0'' : ((false || decide (((ts₁, x, v) : ℕ × ℕ × ℕ) = (ts₁, x, v)))
      && !(decide (((ts₁, x, v) : ℕ × ℕ × ℕ).2.1 = x)))
      = ((false && !(decide (((ts₁, x, v) : ℕ × ℕ × ℕ).2.1 = x)))
      || decide (((ts₁, x, v) : ℕ × ℕ × ℕ) = (ts₁, x, v))) := h0'
  simp at h0''

/-- An `Add x v` fails to commute only with `Rmv x`. -/
theorem AWPQ_ncomm_add_dest {ts r x v : ℕ} {o : Op AWPQ.AppOp}
    (h : ¬ AWPQ.toCRDTSig.commutes (ts, r, AWPQOp.add x v) o) :
    o.2.2 = AWPQOp.rmv x := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | add y w => exact absurd (AWPQ_comm_add_add ts r x v ts' r' y w) h
  | inc y am =>
    exact absurd (AWPQ_commutes_symm (AWPQ_comm_inc_left ts' r' y am _)) h
  | rmv y =>
    by_cases hxy : x = y
    · subst hxy; rfl
    · exact absurd (AWPQ_comm_add_rmv_ne ts r x v ts' r' y hxy) h

/-- A `Rmv x` fails to commute only with an `Add x _`. -/
theorem AWPQ_ncomm_rmv_dest {ts r x : ℕ} {o : Op AWPQ.AppOp}
    (h : ¬ AWPQ.toCRDTSig.commutes (ts, r, AWPQOp.rmv x) o) :
    ∃ v, o.2.2 = AWPQOp.add x v := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | add y w =>
    by_cases hxy : y = x
    · subst hxy; exact ⟨w, rfl⟩
    · exact absurd
        (AWPQ_commutes_symm (AWPQ_comm_add_rmv_ne ts' r' y w ts r x hxy)) h
  | inc y am =>
    exact absurd (AWPQ_commutes_symm (AWPQ_comm_inc_left ts' r' y am _)) h
  | rmv y => exact absurd (AWPQ_comm_rmv_rmv ts r x ts' r' y) h

/-! ### §3. The update layer of `CoreVCs3CD` -/

theorem AWPQ_no_rc_chain :
    ∀ o₁ o₂ o₃ : Op AWPQ.AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ (AWPQ.toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∧
         AWPQ.toCRDTSig.rc o₂ o₃ = RcRes.Fst_then_snd) := by
  rintro ⟨ts₁, r₁, op₁⟩ ⟨ts₂, r₂, op₂⟩ ⟨ts₃, r₃, op₃⟩ _ _ ⟨h1, h2⟩
  cases op₂ with
  | add x₂ v₂ =>
    cases op₃ with
    | add x₃ v₃ => exact RcRes.noConfusion (show RcRes.Either = _ from h2)
    | inc x₃ a₃ => exact RcRes.noConfusion (show RcRes.Either = _ from h2)
    | rmv x₃ =>
      have h2' : (if x₂ = x₃ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := h2
      by_cases hx : x₂ = x₃
      · rw [if_pos hx] at h2'; exact RcRes.noConfusion h2'
      · rw [if_neg hx] at h2'; exact RcRes.noConfusion h2'
  | inc x₂ a₂ =>
    cases op₁ with
    | add x₁ v₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h1)
    | inc x₁ a₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h1)
    | rmv x₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h1)
  | rmv x₂ =>
    cases op₁ with
    | add x₁ v₁ =>
      have h1' : (if x₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := h1
      by_cases hx : x₁ = x₂
      · rw [if_pos hx] at h1'; exact RcRes.noConfusion h1'
      · rw [if_neg hx] at h1'; exact RcRes.noConfusion h1'
    | inc x₁ a₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h1)
    | rmv x₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h1)

theorem AWPQ_rc_non_comm_directional :
    ∀ o₁ o₂ : Op AWPQ.AppOp,
      distinctOps o₁ o₂ → differentReplicas o₁ o₂ →
      (¬ AWPQ.toCRDTSig.commutes o₁ o₂ ↔
       (AWPQ.toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∨
        AWPQ.toCRDTSig.rc o₂ o₁ = RcRes.Fst_then_snd)) := by
  intro o₁ o₂ _ _
  constructor
  · intro hnc
    rcases o₁ with ⟨ts₁, r₁, op₁⟩
    cases op₁ with
    | add x v =>
      have h2 := AWPQ_ncomm_add_dest hnc
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      have h2' : op₂ = AWPQOp.rmv x := h2
      subst h2'
      right
      show (if x = x then RcRes.Fst_then_snd else RcRes.Either)
          = RcRes.Fst_then_snd
      rw [if_pos rfl]
    | inc x am =>
      exact absurd (AWPQ_comm_inc_left ts₁ r₁ x am o₂) hnc
    | rmv x =>
      obtain ⟨v, h2⟩ := AWPQ_ncomm_rmv_dest hnc
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      have h2' : op₂ = AWPQOp.add x v := h2
      subst h2'
      left
      show (if x = x then RcRes.Fst_then_snd else RcRes.Either)
          = RcRes.Fst_then_snd
      rw [if_pos rfl]
  · rintro (h | h)
    · rcases o₁ with ⟨ts₁, r₁, op₁⟩
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      cases op₁ with
      | add x₁ v₁ =>
        exfalso
        cases op₂ with
        | add x₂ v₂ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | inc x₂ a₂ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | rmv x₂ =>
          have h' : (if x₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₁ = x₂
          · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
          · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
      | inc x₁ a₁ =>
        exfalso
        cases op₂ with
        | add x₂ v₂ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | inc x₂ a₂ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | rmv x₂ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
      | rmv x₁ =>
        cases op₂ with
        | add x₂ v₂ =>
          have h' : (if x₁ = x₂ then RcRes.Fst_then_snd else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₁ = x₂
          · subst hx
            intro hc
            exact AWPQ_ncomm_add_rmv ts₂ r₂ ts₁ r₁ x₁ v₂
              (AWPQ_commutes_symm hc)
          · rw [if_neg hx] at h'
            exact absurd h' (fun hh => RcRes.noConfusion hh)
        | inc x₂ a₂ =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)
        | rmv x₂ =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)
    · rcases o₁ with ⟨ts₁, r₁, op₁⟩
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      cases op₂ with
      | add x₂ v₂ =>
        exfalso
        cases op₁ with
        | add x₁ v₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | inc x₁ a₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | rmv x₁ =>
          have h' : (if x₂ = x₁ then RcRes.Snd_then_fst else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₂ = x₁
          · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
          · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
      | inc x₂ a₂ =>
        exfalso
        cases op₁ with
        | add x₁ v₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | inc x₁ a₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | rmv x₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
      | rmv x₂ =>
        cases op₁ with
        | add x₁ v₁ =>
          have h' : (if x₂ = x₁ then RcRes.Fst_then_snd else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₂ = x₁
          · subst hx
            exact AWPQ_ncomm_add_rmv ts₁ r₁ ts₂ r₂ x₂ v₁
          · rw [if_neg hx] at h'
            exact absurd h' (fun hh => RcRes.noConfusion hh)
        | inc x₁ a₁ =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)
        | rmv x₁ =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)

/-- `cond_comm_lift`: the `Rmv x`/`Add x v` swap perturbs only the fresh
A-record; the perturbation is pointwise-invisible off that record, and the
final non-commuting `e''` (an `Rmv x`) erases it. -/
theorem AWPQ_cond_comm_lift :
    ∀ (s : AWPQ.State) (e e' e'' : Op AWPQ.AppOp)
      (π : List (Op AWPQ.AppOp)),
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      AWPQ.toCRDTSig.rc e e' = RcRes.Fst_then_snd →
      ¬ AWPQ.toCRDTSig.commutes e' e'' →
      AWPQ.update (applySeq AWPQ.toCRDTSig
          (AWPQ.update (AWPQ.update s e') e) π) e''
        = AWPQ.update (applySeq AWPQ.toCRDTSig
            (AWPQ.update (AWPQ.update s e) e') π) e'' := by
  intro s e e' e'' π _ _ _ hrc hnc
  rcases e with ⟨ts₁, r₁, op₁⟩
  rcases e' with ⟨ts₂, r₂, op₂⟩
  cases op₁ with
  | add x₁ v₁ =>
    exfalso
    cases op₂ with
    | add x₂ v₂ => exact RcRes.noConfusion (show RcRes.Either = _ from hrc)
    | inc x₂ a₂ => exact RcRes.noConfusion (show RcRes.Either = _ from hrc)
    | rmv x₂ =>
      have h' : (if x₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := hrc
      by_cases hx : x₁ = x₂
      · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
      · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
  | inc x₁ a₁ =>
    exfalso
    cases op₂ with
    | add x₂ v₂ => exact RcRes.noConfusion (show RcRes.Either = _ from hrc)
    | inc x₂ a₂ => exact RcRes.noConfusion (show RcRes.Either = _ from hrc)
    | rmv x₂ => exact RcRes.noConfusion (show RcRes.Either = _ from hrc)
  | rmv x₁ =>
    cases op₂ with
    | inc x₂ a₂ =>
      exact absurd (show RcRes.Either = _ from hrc)
        (fun hh => RcRes.noConfusion hh)
    | rmv x₂ =>
      exact absurd (show RcRes.Either = _ from hrc)
        (fun hh => RcRes.noConfusion hh)
    | add x₂ v₂ =>
      have h' : (if x₁ = x₂ then RcRes.Fst_then_snd else RcRes.Either)
          = RcRes.Fst_then_snd := hrc
      by_cases hx : x₁ = x₂
      swap
      · rw [if_neg hx] at h'; exact absurd h' (fun hh => RcRes.noConfusion hh)
      · subst hx
        -- e'' is an Rmv x₁ (the only non-commuter of the Add)
        have hdest := AWPQ_ncomm_add_dest hnc
        rcases e'' with ⟨ts₃, r₃, op₃⟩
        have hdest' : op₃ = AWPQOp.rmv x₁ := hdest
        subst hdest'
        -- the two start states agree at every A-point off the fresh record,
        -- and have equal I-components
        have hsnd : (AWPQ.update (AWPQ.update s (ts₂, r₂, AWPQOp.add x₁ v₂))
            (ts₁, r₁, AWPQOp.rmv x₁)).2
            = (AWPQ.update (AWPQ.update s (ts₁, r₁, AWPQOp.rmv x₁))
                (ts₂, r₂, AWPQOp.add x₁ v₂)).2 := rfl
        refine Prod.ext (funext fun q => ?_) ?_
        · show ((applySeq AWPQ.toCRDTSig
              (AWPQ.update (AWPQ.update s (ts₂, r₂, AWPQOp.add x₁ v₂))
                (ts₁, r₁, AWPQOp.rmv x₁)) π).1 q && !(decide (q.2.1 = x₁)))
            = ((applySeq AWPQ.toCRDTSig
                (AWPQ.update (AWPQ.update s (ts₁, r₁, AWPQOp.rmv x₁))
                  (ts₂, r₂, AWPQOp.add x₁ v₂)) π).1 q
              && !(decide (q.2.1 = x₁)))
          by_cases hq2 : q.2.1 = x₁
          · rw [decide_eq_true hq2]
            simp
          · have hq : q ≠ (ts₂, x₁, v₂) := by
              intro h
              exact hq2 (by rw [h])
            have hagree :
                (AWPQ.update (AWPQ.update s (ts₂, r₂, AWPQOp.add x₁ v₂))
                  (ts₁, r₁, AWPQOp.rmv x₁)).1 q
                = (AWPQ.update (AWPQ.update s (ts₁, r₁, AWPQOp.rmv x₁))
                    (ts₂, r₂, AWPQOp.add x₁ v₂)).1 q := by
              show ((s.1 q || decide (q = (ts₂, x₁, v₂)))
                  && !(decide (q.2.1 = x₁)))
                = ((s.1 q && !(decide (q.2.1 = x₁)))
                  || decide (q = (ts₂, x₁, v₂)))
              rw [decide_eq_false hq, decide_eq_false hq2]
              cases s.1 q <;> rfl
            rw [awpqFold_fst_agree π q hagree]
        · show (applySeq AWPQ.toCRDTSig
              (AWPQ.update (AWPQ.update s (ts₂, r₂, AWPQOp.add x₁ v₂))
                (ts₁, r₁, AWPQOp.rmv x₁)) π).2
            = (applySeq AWPQ.toCRDTSig
                (AWPQ.update (AWPQ.update s (ts₁, r₁, AWPQOp.rmv x₁))
                  (ts₂, r₂, AWPQOp.add x₁ v₂)) π).2
          exact awpqFold_snd_congr π hsnd

theorem AWPQ_mergeL_comm (l a b : AWPQ.State) :
    AWPQ.mergeL l a b = AWPQ.mergeL l b a := by
  refine Prod.ext (funext fun t => ?_) (funext fun u => ?_) <;>
    simp only [AWPQ_mergeL_eq, awpqMergeL]
  · cases l.1 t <;> cases a.1 t <;> cases b.1 t <;> rfl
  · cases l.2 u <;> cases a.2 u <;> cases b.2 u <;> rfl

theorem AWPQ_updateVCs : UpdateVCs AWPQ.toCRDTSig :=
  ⟨AWPQ_rc_non_comm_directional, AWPQ_no_rc_chain, AWPQ_cond_comm_lift⟩

theorem AWPQ_coreVCs3CD : CoreVCs3CD AWPQ :=
  ⟨AWPQ_updateVCs, AWPQ_mergeL_comm⟩


/-! ### §4. Fold facts (A-component: the OR-Set pattern; I: grow-only) -/

/-- A live A-record has its adding event in the list. -/
theorem AWPQ_fold_bound₁ {ρ : List (Op AWPQ.AppOp)} {t : ℕ × ℕ × ℕ}
    (h : (applySeq AWPQ.toCRDTSig AWPQ.init ρ).1 t = true) :
    ∃ o ∈ ρ, o.2.2 = AWPQOp.add t.2.1 t.2.2 ∧ o.1 = t.1 := by
  induction ρ using List.reverseRecOn with
  | nil => exact absurd (show (false : Bool) = true from h) Bool.noConfusion
  | append_singleton ρ o ih =>
    rw [applySeq_append_single] at h
    rcases o with ⟨ts, rid, op⟩
    cases op with
    | add e v =>
      have h' : ((applySeq AWPQ.toCRDTSig AWPQ.init ρ).1 t
          || decide (t = (ts, e, v))) = true := h
      cases hfa : (applySeq AWPQ.toCRDTSig AWPQ.init ρ).1 t with
      | true =>
        obtain ⟨o', ho', h1, h2⟩ := ih hfa
        exact ⟨o', List.mem_append_left _ ho', h1, h2⟩
      | false =>
        rw [hfa] at h'
        have ht' : t = (ts, e, v) := of_decide_eq_true (by simpa using h')
        refine ⟨(ts, rid, AWPQOp.add e v),
          List.mem_append_right _ List.mem_cons_self, ?_, ?_⟩
        · show AWPQOp.add e v = AWPQOp.add t.2.1 t.2.2
          rw [ht']
        · show ts = t.1
          rw [ht']
    | inc e am =>
      have h' : (applySeq AWPQ.toCRDTSig AWPQ.init ρ).1 t = true := h
      obtain ⟨o', ho', h1, h2⟩ := ih h'
      exact ⟨o', List.mem_append_left _ ho', h1, h2⟩
    | rmv e =>
      have h' : ((applySeq AWPQ.toCRDTSig AWPQ.init ρ).1 t
          && !(decide (t.2.1 = e))) = true := h
      obtain ⟨o', ho', h1, h2⟩ := ih (Bool.and_eq_true_iff.mp h').1
      exact ⟨o', List.mem_append_left _ ho', h1, h2⟩

/-- A dead A-record stays dead if nothing re-adds it. -/
theorem AWPQ_fold_stays_false₁ {t : ℕ × ℕ × ℕ} :
    ∀ (β : List (Op AWPQ.AppOp)) (s : AWPQ.State),
      s.1 t = false →
      (∀ o ∈ β, ¬(o.2.2 = AWPQOp.add t.2.1 t.2.2 ∧ o.1 = t.1)) →
      (applySeq AWPQ.toCRDTSig s β).1 t = false := by
  intro β
  induction β with
  | nil => intro s hs _; exact hs
  | cons o β ih =>
    intro s hs hβ
    have hupd : (AWPQ.update s o).1 t = false := by
      rcases o with ⟨ts, rid, op⟩
      cases op with
      | add e v =>
        show (s.1 t || decide (t = (ts, e, v))) = false
        rw [hs]
        cases hd : decide (t = (ts, e, v)) with
        | false => rfl
        | true =>
          exfalso
          have ht' : t = (ts, e, v) := of_decide_eq_true hd
          exact hβ _ List.mem_cons_self
            ⟨show AWPQOp.add e v = AWPQOp.add t.2.1 t.2.2 by rw [ht'],
             show ts = t.1 by rw [ht']⟩
      | inc e am => exact hs
      | rmv e =>
        show (s.1 t && !(decide (t.2.1 = e))) = false
        rw [hs]
        rfl
    exact ih (AWPQ.update s o) hupd
      (fun o' ho' => hβ o' (List.mem_cons_of_mem _ ho'))

/-- A live A-record stays live if no same-element `Rmv` follows. -/
theorem AWPQ_fold_stays_true₁ {t : ℕ × ℕ × ℕ} :
    ∀ (β : List (Op AWPQ.AppOp)) (s : AWPQ.State),
      s.1 t = true →
      (∀ o ∈ β, o.2.2 ≠ AWPQOp.rmv t.2.1) →
      (applySeq AWPQ.toCRDTSig s β).1 t = true := by
  intro β
  induction β with
  | nil => intro s hs _; exact hs
  | cons o β ih =>
    intro s hs hβ
    have hupd : (AWPQ.update s o).1 t = true := by
      rcases o with ⟨ts, rid, op⟩
      cases op with
      | add e v =>
        show (s.1 t || decide (t = (ts, e, v))) = true
        rw [hs]
        rfl
      | inc e am => exact hs
      | rmv e =>
        show (s.1 t && !(decide (t.2.1 = e))) = true
        rw [hs]
        have hne : t.2.1 ≠ e := by
          intro h
          exact hβ _ List.mem_cons_self (by rw [h])
        rw [decide_eq_false hne]
        rfl
    exact ih (AWPQ.update s o) hupd
      (fun o' ho' => hβ o' (List.mem_cons_of_mem _ ho'))

/-- A live I-record has its `Inc` in the list. -/
theorem AWPQ_fold_bound₂ {ρ : List (Op AWPQ.AppOp)} {u : ℕ × ℕ × ℤ}
    (h : (applySeq AWPQ.toCRDTSig AWPQ.init ρ).2 u = true) :
    ∃ o ∈ ρ, o.2.2 = AWPQOp.inc u.2.1 u.2.2 ∧ o.1 = u.1 := by
  induction ρ using List.reverseRecOn with
  | nil => exact absurd (show (false : Bool) = true from h) Bool.noConfusion
  | append_singleton ρ o ih =>
    rw [applySeq_append_single] at h
    rcases o with ⟨ts, rid, op⟩
    cases op with
    | add e v =>
      obtain ⟨o', ho', h1, h2⟩ := ih h
      exact ⟨o', List.mem_append_left _ ho', h1, h2⟩
    | rmv e =>
      obtain ⟨o', ho', h1, h2⟩ := ih h
      exact ⟨o', List.mem_append_left _ ho', h1, h2⟩
    | inc e am =>
      have h' : ((applySeq AWPQ.toCRDTSig AWPQ.init ρ).2 u
          || decide (u = (ts, e, am))) = true := h
      cases hfa : (applySeq AWPQ.toCRDTSig AWPQ.init ρ).2 u with
      | true =>
        obtain ⟨o', ho', h1, h2⟩ := ih hfa
        exact ⟨o', List.mem_append_left _ ho', h1, h2⟩
      | false =>
        rw [hfa] at h'
        have hu' : u = (ts, e, am) := of_decide_eq_true (by simpa using h')
        refine ⟨(ts, rid, AWPQOp.inc e am),
          List.mem_append_right _ List.mem_cons_self, ?_, ?_⟩
        · show AWPQOp.inc e am = AWPQOp.inc u.2.1 u.2.2
          rw [hu']
        · show ts = u.1
          rw [hu']

/-- The I-component is grow-only. -/
theorem AWPQ_fold_stays_true₂ {u : ℕ × ℕ × ℤ} :
    ∀ (β : List (Op AWPQ.AppOp)) (s : AWPQ.State),
      s.2 u = true → (applySeq AWPQ.toCRDTSig s β).2 u = true := by
  intro β
  induction β with
  | nil => intro s hs; exact hs
  | cons o β ih =>
    intro s hs
    refine ih (AWPQ.update s o) ?_
    rcases o with ⟨ts, rid, op⟩
    cases op with
    | add e v => exact hs
    | rmv e => exact hs
    | inc e am =>
      show (s.2 u || decide (u = (ts, e, am))) = true
      rw [hs]
      rfl

/-- A member `Inc` contributes its I-record. -/
theorem AWPQ_contrib₂ {ρ : List (Op AWPQ.AppOp)} {ts rid e : ℕ} {am : ℤ}
    (h : (ts, rid, AWPQOp.inc e am) ∈ ρ) :
    (applySeq AWPQ.toCRDTSig AWPQ.init ρ).2 (ts, e, am) = true := by
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem h
  subst hsplit
  have hstep : applySeq AWPQ.toCRDTSig AWPQ.init
      (α ++ (ts, rid, AWPQOp.inc e am) :: β)
      = applySeq AWPQ.toCRDTSig
          (AWPQ.update (applySeq AWPQ.toCRDTSig AWPQ.init α)
            (ts, rid, AWPQOp.inc e am)) β := by
    simp [applySeq, List.foldl_append]
  rw [hstep]
  refine AWPQ_fold_stays_true₂ β _ ?_
  show ((applySeq AWPQ.toCRDTSig AWPQ.init α).2 (ts, e, am)
      || decide (((ts, e, am) : ℕ × ℕ × ℤ) = (ts, e, am))) = true
  rw [decide_eq_true rfl]
  cases (applySeq AWPQ.toCRDTSig AWPQ.init α).2 (ts, e, am) <;> rfl

/-- I-component σ-monotonicity across nested event sets. -/
theorem AWPQ_canonical_mono₂
    {C : Sal.Emulation.Configuration AWPQ.toCRDTSig}
    {F G : Set (Op AWPQ.AppOp)} {s t : AWPQ.State}
    (hFG : ∀ o ∈ F, o ∈ G)
    (hs : IsCanonicalState C F s) (ht : IsCanonicalState C G t) :
    ∀ u, s.2 u = true → t.2 u = true := by
  obtain ⟨ρ, hρp, -, hρf⟩ := hs
  obtain ⟨π, hπp, -, hπf⟩ := ht
  intro u hu
  rw [← hρf] at hu
  obtain ⟨o, ho, hoT, hoTs⟩ := AWPQ_fold_bound₂ hu
  rcases o with ⟨ts, rid, op⟩
  have hoT' : op = AWPQOp.inc u.2.1 u.2.2 := hoT
  have hoTs' : ts = u.1 := hoTs
  subst hoT'
  subst hoTs'
  have hπm : (u.1, rid, AWPQOp.inc u.2.1 u.2.2) ∈ π :=
    (hπp.2 _).mpr (hFG _ ((hρp.2 _).mp ho))
  rw [← hπf]
  have := AWPQ_contrib₂ (ρ := π) hπm
  simpa using this

/-! ### §5. The canonical-state σ-facts (A-component) -/

theorem AWPQ_canonical_bound₁
    {C : Sal.Emulation.Configuration AWPQ.toCRDTSig}
    {F : Set (Op AWPQ.AppOp)} {s : AWPQ.State} {t : ℕ × ℕ × ℕ}
    (hs : IsCanonicalState C F s) (ht : s.1 t = true) :
    ∃ o ∈ F, o.2.2 = AWPQOp.add t.2.1 t.2.2 ∧ o.1 = t.1 := by
  obtain ⟨ρ, hperm, -, hfold⟩ := hs
  rw [← hfold] at ht
  obtain ⟨o, ho, h1, h2⟩ := AWPQ_fold_bound₁ ht
  exact ⟨o, (hperm.2 o).mp ho, h1, h2⟩

/-- **Kill**: a live A-record admits no same-element `Rmv` vis-after its add. -/
theorem AWPQ_live_no_later_rmv
    {C : Sal.Emulation.Configuration AWPQ.toCRDTSig}
    {F : Set (Op AWPQ.AppOp)} {s : AWPQ.State} {t : ℕ × ℕ × ℕ}
    (h_in : ∀ o ∈ F, o ∈ C.events)
    (hs : IsCanonicalState C F s)
    (ht : s.1 t = true)
    {rda tsr rdr : ℕ}
    (haF : (t.1, rda, AWPQOp.add t.2.1 t.2.2) ∈ F)
    (hrF : (tsr, rdr, AWPQOp.rmv t.2.1) ∈ F)
    (hvis : C.vis (t.1, rda, AWPQOp.add t.2.1 t.2.2)
      (tsr, rdr, AWPQOp.rmv t.2.1)) :
    False := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  rw [← hfold] at ht
  have hne_ar : ((t.1, rda, AWPQOp.add t.2.1 t.2.2) : Op AWPQ.AppOp)
      ≠ (tsr, rdr, AWPQOp.rmv t.2.1) := by
    intro h
    have := congrArg (fun o : Op AWPQ.AppOp => o.2.2) h
    exact AWPQOp.noConfusion this
  have hnc : ¬ AWPQ.toCRDTSig.commutes (t.1, rda, AWPQOp.add t.2.1 t.2.2)
      (tsr, rdr, AWPQOp.rmv t.2.1) :=
    AWPQ_ncomm_add_rmv t.1 rda tsr rdr t.2.1 t.2.2
  have hedge : loOn C F (t.1, rda, AWPQOp.add t.2.1 t.2.2)
      (tsr, rdr, AWPQOp.rmv t.2.1) := Or.inl ⟨hvis, hnc⟩
  have hrρ : (tsr, rdr, AWPQOp.rmv t.2.1) ∈ ρ := (hperm.2 _).mpr hrF
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem hrρ
  subst hsplit
  have haρ : (t.1, rda, AWPQOp.add t.2.1 t.2.2)
      ∈ α ++ (tsr, rdr, AWPQOp.rmv t.2.1) :: β := (hperm.2 _).mpr haF
  have hmid := List.pairwise_cons.mp (List.pairwise_append.mp hresp).2.1
  have haα : (t.1, rda, AWPQOp.add t.2.1 t.2.2) ∈ α := by
    rcases List.mem_append.mp haρ with h | h
    · exact h
    · rcases List.mem_cons.mp h with h | h
      · exact absurd h hne_ar
      · exact absurd hedge (hmid.1 _ h)
  have hstep : applySeq AWPQ.toCRDTSig AWPQ.init
      (α ++ (tsr, rdr, AWPQOp.rmv t.2.1) :: β)
      = applySeq AWPQ.toCRDTSig
          (AWPQ.update (applySeq AWPQ.toCRDTSig AWPQ.init α)
            (tsr, rdr, AWPQOp.rmv t.2.1)) β := by
    simp [applySeq, List.foldl_append]
  rw [hstep] at ht
  have hkill : (AWPQ.update (applySeq AWPQ.toCRDTSig AWPQ.init α)
      (tsr, rdr, AWPQOp.rmv t.2.1)).1 t = false := by
    show ((applySeq AWPQ.toCRDTSig AWPQ.init α).1 t
        && !(decide (t.2.1 = t.2.1))) = false
    rw [decide_eq_true rfl]
    cases (applySeq AWPQ.toCRDTSig AWPQ.init α).1 t <;> rfl
  have hnoadd : ∀ o ∈ β, ¬(o.2.2 = AWPQOp.add t.2.1 t.2.2 ∧ o.1 = t.1) := by
    rintro o ho ⟨hoT, hoTs⟩
    have hoρ : o ∈ α ++ (tsr, rdr, AWPQOp.rmv t.2.1) :: β :=
      List.mem_append_right _ (List.mem_cons_of_mem _ ho)
    have hoF : o ∈ F := (hperm.2 o).mp hoρ
    have hoa : o = (t.1, rda, AWPQOp.add t.2.1 t.2.2) := by
      by_contra hne
      exact distinctOps_of_events (h_in o hoF)
        (h_in _ haF) hne hoTs
    rw [hoa] at ho
    have hnd := hperm.1
    rw [List.nodup_append] at hnd
    exact hnd.2.2 _ haα _ (List.mem_cons_of_mem _ ho) rfl
  rw [AWPQ_fold_stays_false₁ β _ hkill hnoadd] at ht
  exact Bool.noConfusion ht

/-- **Live**: an add with no same-element `Rmv` vis-after it yields a live
A-record. -/
theorem AWPQ_no_later_kill_live
    {C : Sal.Emulation.Configuration AWPQ.toCRDTSig}
    {F : Set (Op AWPQ.AppOp)} {s : AWPQ.State} {t : ℕ × ℕ × ℕ}
    (h_in : ∀ o ∈ F, o ∈ C.events)
    (hs : IsCanonicalState C F s)
    {rda : ℕ}
    (haF : (t.1, rda, AWPQOp.add t.2.1 t.2.2) ∈ F)
    (hno : ∀ r ∈ F, (r : Op AWPQ.AppOp).2.2 = AWPQOp.rmv t.2.1 →
      ¬ C.vis (t.1, rda, AWPQOp.add t.2.1 t.2.2) r) :
    s.1 t = true := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  rw [← hfold]
  have haρ : (t.1, rda, AWPQOp.add t.2.1 t.2.2) ∈ ρ := (hperm.2 _).mpr haF
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem haρ
  subst hsplit
  have hcons := List.pairwise_cons.mp (List.pairwise_append.mp hresp).2.1
  have hnorem : ∀ o ∈ β, (o : Op AWPQ.AppOp).2.2 ≠ AWPQOp.rmv t.2.1 := by
    intro o ho hoT
    have hoF : o ∈ F := (hperm.2 o).mp
      (List.mem_append_right _ (List.mem_cons_of_mem _ ho))
    have hnovis : ¬ C.vis (t.1, rda, AWPQOp.add t.2.1 t.2.2) o :=
      hno o hoF hoT
    rcases o with ⟨tso, rdo, opo⟩
    have hoT' : opo = AWPQOp.rmv t.2.1 := hoT
    subst hoT'
    have hnc_oa : ¬ AWPQ.toCRDTSig.commutes (tso, rdo, AWPQOp.rmv t.2.1)
        (t.1, rda, AWPQOp.add t.2.1 t.2.2) :=
      fun h => AWPQ_ncomm_add_rmv t.1 rda tso rdo t.2.1 t.2.2
        (AWPQ_commutes_symm h)
    have hedge : loOn C F (tso, rdo, AWPQOp.rmv t.2.1)
        (t.1, rda, AWPQOp.add t.2.1 t.2.2) := by
      by_cases hvo : C.vis (tso, rdo, AWPQOp.rmv t.2.1)
          (t.1, rda, AWPQOp.add t.2.1 t.2.2)
      · exact Or.inl ⟨hvo, hnc_oa⟩
      · refine Or.inr ⟨hvo, hnovis, ?_, ?_⟩
        · show (if t.2.1 = t.2.1 then RcRes.Fst_then_snd else RcRes.Either)
            = RcRes.Fst_then_snd
          rw [if_pos rfl]
        · rintro ⟨e₃, he₃F, hve₃, hnce₃⟩
          have h₃T := AWPQ_ncomm_add_dest hnce₃
          exact hno e₃ he₃F h₃T hve₃
    exact hcons.1 _ ho hedge
  have hstep : applySeq AWPQ.toCRDTSig AWPQ.init
      (α ++ (t.1, rda, AWPQOp.add t.2.1 t.2.2) :: β)
      = applySeq AWPQ.toCRDTSig
          (AWPQ.update (applySeq AWPQ.toCRDTSig AWPQ.init α)
            (t.1, rda, AWPQOp.add t.2.1 t.2.2)) β := by
    simp [applySeq, List.foldl_append]
  rw [hstep]
  refine AWPQ_fold_stays_true₁ β _ ?_ hnorem
  show ((applySeq AWPQ.toCRDTSig AWPQ.init α).1 t
      || decide (t = (t.1, t.2.1, t.2.2))) = true
  have : decide (t = (t.1, t.2.1, t.2.2)) = true := decide_eq_true (by
    exact Prod.ext rfl (Prod.ext rfl rfl))
  rw [this]
  cases (applySeq AWPQ.toCRDTSig AWPQ.init α).1 t <;> rfl


/-! ### §6. The maximal-`Rmv` trichotomy, the empty `Inc` downset, and `CDVC3` -/

theorem AWPQ_rmv_max_trichotomy
    {C : Sal.Emulation.Configuration AWPQ.toCRDTSig}
    {U : Set (Op AWPQ.AppOp)} {A B : AWPQ.State}
    {ts rid x : ℕ}
    (h_in : ∀ o ∈ U, o ∈ C.events)
    (h_cl : ∀ a b, C.vis a b → ¬ AWPQ.toCRDTSig.commutes a b →
      b ∈ U → a ∈ U)
    (h_e : (ts, rid, AWPQOp.rmv x) ∈ U)
    (h_max : ∀ y ∈ U, y ≠ (ts, rid, AWPQOp.rmv x) →
      ¬ loOn C U (ts, rid, AWPQOp.rmv x) y)
    (hA : IsCanonicalState C (U \ {(ts, rid, AWPQOp.rmv x)}) A)
    (hB : IsCanonicalState C
      (downset C (ts, rid, AWPQOp.rmv x) \ {(ts, rid, AWPQOp.rmv x)}) B)
    {t : ℕ × ℕ × ℕ} (htx : t.2.1 = x) (htA : A.1 t = true) :
    B.1 t = true := by
  have h_inA : ∀ o ∈ U \ {(ts, rid, AWPQOp.rmv x)}, o ∈ C.events :=
    fun o ho => h_in o ho.1
  have h_dsub : downset C (ts, rid, AWPQOp.rmv x) ⊆ U :=
    downset_subset h_cl h_e
  have h_inB : ∀ o ∈ downset C (ts, rid, AWPQOp.rmv x)
      \ {(ts, rid, AWPQOp.rmv x)}, o ∈ C.events :=
    fun o ho => h_in o (h_dsub ho.1)
  obtain ⟨a, haU', haT, haTs⟩ := AWPQ_canonical_bound₁ hA htA
  rcases a with ⟨tsa, rda, opa⟩
  have haT' : opa = AWPQOp.add t.2.1 t.2.2 := haT
  subst haT'
  have haTs' : tsa = t.1 := haTs
  subst haTs'
  have hane : ((t.1, rda, AWPQOp.add t.2.1 t.2.2) : Op AWPQ.AppOp)
      ≠ (ts, rid, AWPQOp.rmv x) := haU'.2
  have hnc_ae : ¬ AWPQ.toCRDTSig.commutes (t.1, rda, AWPQOp.add t.2.1 t.2.2)
      (ts, rid, AWPQOp.rmv x) := by
    rw [← htx]
    exact AWPQ_ncomm_add_rmv t.1 rda ts rid t.2.1 t.2.2
  by_cases hva : C.vis (t.1, rda, AWPQOp.add t.2.1 t.2.2)
      (ts, rid, AWPQOp.rmv x)
  · have haD : (t.1, rda, AWPQOp.add t.2.1 t.2.2)
        ∈ downset C (ts, rid, AWPQOp.rmv x) \ {(ts, rid, AWPQOp.rmv x)} :=
      ⟨Or.inr (Relation.TransGen.single ⟨hva, hnc_ae⟩), hane⟩
    refine AWPQ_no_later_kill_live h_inB hB haD ?_
    intro r hrD hrT hvar
    have hrU' : r ∈ U \ {(ts, rid, AWPQOp.rmv x)} :=
      ⟨h_dsub hrD.1, hrD.2⟩
    rcases r with ⟨tsr, rdr, opr⟩
    have hrT' : opr = AWPQOp.rmv t.2.1 := hrT
    subst hrT'
    exact AWPQ_live_no_later_rmv h_inA hA htA haU' hrU' hvar
  · by_cases hvea : C.vis (ts, rid, AWPQOp.rmv x)
        (t.1, rda, AWPQOp.add t.2.1 t.2.2)
    · exfalso
      have hnc_ea : ¬ AWPQ.toCRDTSig.commutes (ts, rid, AWPQOp.rmv x)
          (t.1, rda, AWPQOp.add t.2.1 t.2.2) :=
        fun h => hnc_ae (AWPQ_commutes_symm h)
      exact h_max _ haU'.1 hane (Or.inl ⟨hvea, hnc_ea⟩)
    · exfalso
      refine h_max _ haU'.1 hane (Or.inr ⟨hvea, hva, ?_, ?_⟩)
      · show (if x = t.2.1 then RcRes.Fst_then_snd else RcRes.Either)
            = RcRes.Fst_then_snd
        rw [if_pos htx.symm]
      · rintro ⟨e₃, he₃U, hve₃, hnce₃⟩
        have h₃T := AWPQ_ncomm_add_dest hnce₃
        have h₃ne : e₃ ≠ (ts, rid, AWPQOp.rmv x) := by
          intro h
          rw [h] at hve₃
          exact hva hve₃
        rcases e₃ with ⟨ts₃, rd₃, op₃⟩
        have h₃T' : op₃ = AWPQOp.rmv t.2.1 := h₃T
        subst h₃T'
        exact AWPQ_live_no_later_rmv h_inA hA htA haU'
          ⟨he₃U, h₃ne⟩ hve₃

/-- `Inc` has an empty punctured downset (it commutes with everything). -/
theorem AWPQ_downset_inc_empty (C : Sal.Emulation.Configuration AWPQ.toCRDTSig)
    (ts r e : ℕ) (am : ℤ) :
    downset C (ts, r, AWPQOp.inc e am) \ {(ts, r, AWPQOp.inc e am)} = ∅ := by
  ext x
  simp only [Set.mem_diff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  rintro (hx | hx)
  · exact fun hne => hne hx
  · intro _
    exfalso
    cases hx with
    | single h' =>
      exact h'.2 (AWPQ_commutes_symm (AWPQ_comm_inc_left ts r e am _))
    | tail _ h' =>
      exact h'.2 (AWPQ_commutes_symm (AWPQ_comm_inc_left ts r e am _))

theorem AWPQ_cdVC3 : CDVC3 AWPQ := by
  intro C U A B e h_tr h_ir h_in h_cl h_e h_max hA hB
  rcases e with ⟨ts, rid, op⟩
  cases op with
  | add x v =>
    have hBt : B.1 (ts, x, v) = false := by
      cases hBt : B.1 (ts, x, v) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨o, hoB, hoT, hoTs⟩ := AWPQ_canonical_bound₁ hB hBt
        have hoU : o ∈ U := downset_subset h_cl h_e hoB.1
        exact distinctOps_of_events (h_in o hoU) (h_in _ h_e) hoB.2 hoTs
    refine Prod.ext (funext fun t => ?_) (funext fun u => ?_) <;>
      simp only [AWPQ_mergeL_eq, AWPQ_update_eq, awpqMergeL, awpqUpdate]
    · by_cases ht : t = (ts, x, v)
      · subst ht
        rw [hBt, decide_eq_true rfl]
        cases A.1 (ts, x, v) <;> rfl
      · rw [decide_eq_false ht]
        cases B.1 t <;> cases A.1 t <;> rfl
    · cases B.2 u <;> cases A.2 u <;> rfl
  | inc x am =>
    have hBinit : B = AWPQ.init :=
      isCanonicalState_empty (AWPQ_downset_inc_empty C ts rid x am) hB
    subst hBinit
    refine Prod.ext (funext fun t => ?_) (funext fun u => ?_) <;>
      simp only [AWPQ_mergeL_eq, AWPQ_update_eq, awpqMergeL, awpqUpdate,
        AWPQ_init_eq]
    · cases A.1 t <;> rfl
    · cases A.2 u <;> cases decide (u = (ts, x, am)) <;> rfl
  | rmv x =>
    have himp : ∀ t : ℕ × ℕ × ℕ, t.2.1 = x → A.1 t = true → B.1 t = true :=
      fun t htx htA =>
        AWPQ_rmv_max_trichotomy h_in h_cl h_e h_max hA hB htx htA
    refine Prod.ext (funext fun t => ?_) (funext fun u => ?_) <;>
      simp only [AWPQ_mergeL_eq, AWPQ_update_eq, awpqMergeL, awpqUpdate]
    · by_cases hx : t.2.1 = x
      · rw [decide_eq_true hx]
        cases hBt : B.1 t with
        | true => cases A.1 t <;> rfl
        | false =>
          cases hAt : A.1 t with
          | false => rfl
          | true => exact Bool.noConfusion (hBt.symm.trans (himp t hx hAt))
      · rw [decide_eq_false hx]
        cases B.1 t <;> cases A.1 t <;> rfl
    · cases B.2 u <;> cases A.2 u <;> rfl

/-! ### §7. The feasible delta laws -/

/-- The redistribution law is a Boolean tautology per component —
unconditional, all five states arbitrary. -/
theorem awpqMergeL_redistribute (B t₀ t₁ t₂ u : AWPQ.State) :
    awpqMergeL (awpqMergeL B t₀ u) (awpqMergeL B t₁ u) (awpqMergeL B t₂ u)
      = awpqMergeL B (awpqMergeL t₀ t₁ t₂) u := by
  refine Prod.ext (funext fun t => ?_) (funext fun w => ?_) <;>
    simp only [awpqMergeL]
  · cases B.1 t <;> cases t₀.1 t <;> cases t₁.1 t <;> cases t₂.1 t <;>
      cases u.1 t <;> rfl
  · cases B.2 w <;> cases t₀.2 w <;> cases t₁.2 w <;> cases t₂.2 w <;>
      cases u.2 w <;> rfl

theorem AWPQ_feasibleDeltaVCs3 : FeasibleDeltaVCs3 AWPQ := by
  refine ⟨?_, ?_, ?_⟩
  · -- feasible_init (unconditional)
    intro C ev s _ _
    refine Prod.ext (funext fun t => ?_) (funext fun u => ?_) <;>
      simp only [AWPQ_mergeL_eq, awpqMergeL, AWPQ_init_eq]
    · cases s.1 t <;> rfl
    · cases s.2 u <;> rfl
  · -- feasible_local_redistribute
    intro C ev₁ ev₂ s₀ B t₁ s₂ e _ _ h_in₁ h_in₂ h_cl₁ h_cl₂ he₁ he₂
      h_max hc₀ hB ht₁ hc₂
    rcases e with ⟨ts, rid, op⟩
    cases op with
    | add x v =>
      have hBt : B.1 (ts, x, v) = false := by
        cases hBt : B.1 (ts, x, v) with
        | false => rfl
        | true =>
          exfalso
          obtain ⟨o, hoB, hoT, hoTs⟩ := AWPQ_canonical_bound₁ hB hBt
          have hoU : o ∈ ev₁ := downset_subset h_cl₁ he₁ hoB.1
          exact distinctOps_of_events (h_in₁ o hoU) (h_in₁ _ he₁)
            hoB.2 hoTs
      have hs₀t : s₀.1 (ts, x, v) = false := by
        cases hs₀t : s₀.1 (ts, x, v) with
        | false => rfl
        | true =>
          exfalso
          obtain ⟨o, ho₀, hoT, hoTs⟩ := AWPQ_canonical_bound₁ hc₀ hs₀t
          have hone : o ≠ (ts, rid, AWPQOp.add x v) := by
            intro h
            rw [h] at ho₀
            exact he₂ ho₀.2
          exact distinctOps_of_events (h_in₁ o ho₀.1) (h_in₁ _ he₁)
            hone hoTs
      refine Prod.ext (funext fun t => ?_) (funext fun u => ?_) <;>
        simp only [AWPQ_mergeL_eq, AWPQ_update_eq, awpqMergeL, awpqUpdate]
      · by_cases ht : t = (ts, x, v)
        · subst ht
          rw [hBt, hs₀t, decide_eq_true rfl]
          cases t₁.1 (ts, x, v) <;> cases s₂.1 (ts, x, v) <;> rfl
        · rw [decide_eq_false ht]
          cases s₀.1 t <;> cases B.1 t <;> cases t₁.1 t <;>
            cases s₂.1 t <;> rfl
      · cases s₀.2 u <;> cases B.2 u <;> cases t₁.2 u <;>
          cases s₂.2 u <;> rfl
    | inc x am =>
      have hBinit : B = AWPQ.init :=
        isCanonicalState_empty (AWPQ_downset_inc_empty C ts rid x am) hB
      subst hBinit
      have hsub : ∀ o ∈ ev₁ ∩ ev₂, o ∈ ev₂ := fun o ho => ho.2
      have hmono₂ := AWPQ_canonical_mono₂ hsub hc₀ hc₂
      refine Prod.ext (funext fun t => ?_) (funext fun u => ?_) <;>
        simp only [AWPQ_mergeL_eq, AWPQ_update_eq, awpqMergeL, awpqUpdate,
          AWPQ_init_eq]
      · cases s₀.1 t <;> cases t₁.1 t <;> cases s₂.1 t <;> rfl
      · cases hs₀ : s₀.2 u
        · cases t₁.2 u <;> cases decide (u = (ts, x, am)) <;>
            cases s₂.2 u <;> rfl
        · have hs₂ : s₂.2 u = true := hmono₂ u hs₀
          rw [hs₂]
          cases t₁.2 u <;> cases decide (u = (ts, x, am)) <;> rfl
    | rmv x =>
      have himp : ∀ t : ℕ × ℕ × ℕ, t.2.1 = x → B.1 t = true →
          s₂.1 t = true → s₀.1 t = true := by
        intro t htx htB hts₂
        obtain ⟨a', ha'B, ha'T, ha'Ts⟩ := AWPQ_canonical_bound₁ hB htB
        obtain ⟨a'', ha''₂, ha''T, ha''Ts⟩ := AWPQ_canonical_bound₁ hc₂ hts₂
        have ha'U : a' ∈ ev₁ := downset_subset h_cl₁ he₁ ha'B.1
        have heq : a'' = a' := by
          by_contra hne
          exact distinctOps_of_events (h_in₂ a'' ha''₂) (h_in₁ a' ha'U)
            hne (ha''Ts.trans ha'Ts.symm)
        rcases a' with ⟨tsa, rda, opa⟩
        have ha'T' : opa = AWPQOp.add t.2.1 t.2.2 := ha'T
        subst ha'T'
        have ha'Ts' : tsa = t.1 := ha'Ts
        subst ha'Ts'
        have ha₀ : ((t.1, rda, AWPQOp.add t.2.1 t.2.2) : Op AWPQ.AppOp)
            ∈ ev₁ ∩ ev₂ := ⟨ha'U, heq ▸ ha''₂⟩
        refine AWPQ_no_later_kill_live (fun o ho => h_in₁ o ho.1)
          hc₀ ha₀ ?_
        intro r hr₀ hrT hvar
        rcases r with ⟨tsr, rdr, opr⟩
        have hrT' : opr = AWPQOp.rmv t.2.1 := hrT
        subst hrT'
        exact AWPQ_live_no_later_rmv h_in₂ hc₂ hts₂
          (heq ▸ ha''₂) hr₀.2 hvar
      refine Prod.ext (funext fun t => ?_) (funext fun u => ?_) <;>
        simp only [AWPQ_mergeL_eq, AWPQ_update_eq, awpqMergeL, awpqUpdate]
      · by_cases hx : t.2.1 = x
        · rw [decide_eq_true hx]
          cases hBt : B.1 t with
          | false =>
            cases s₀.1 t <;> cases t₁.1 t <;> cases s₂.1 t <;> rfl
          | true =>
            cases hs₀t : s₀.1 t with
            | true => cases t₁.1 t <;> cases s₂.1 t <;> rfl
            | false =>
              cases hs₂t : s₂.1 t with
              | false => cases t₁.1 t <;> rfl
              | true =>
                exact Bool.noConfusion
                  (hs₀t.symm.trans (himp t hx hBt hs₂t))
        · rw [decide_eq_false hx]
          cases s₀.1 t <;> cases B.1 t <;> cases t₁.1 t <;>
            cases s₂.1 t <;> rfl
      · cases s₀.2 u <;> cases B.2 u <;> cases t₁.2 u <;>
          cases s₂.2 u <;> rfl
  · -- feasible_redistribute: the unconditional tautology
    intro C ev₁ ev₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _ _
    exact awpqMergeL_redistribute B t₀ t₁ t₂ (AWPQ.update B e)

open LabeledTS in
/-- End-to-end RA-linearizability for the Add-Wins Priority Queue. -/
theorem awpq_ra_linearizable3
    (C : Configuration AWPQ)
    (hReach : (labeledTS3 AWPQ).ReachableFrom (initConfig AWPQ trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_via_capstone AWPQ_coreVCs3CD AWPQ_coreVCs3CD.update_core
    AWPQ_feasibleDeltaVCs3 AWPQ_cdVC3 C hReach


/-! ## The conditioned capstone — identity instantiation of the generic framework -/

section
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.FlatGeneric

/-- **Add-Wins Priority Queue over the generic framework** (feasible class: the
OR-Set pattern on the add component, grow-only increments). -/
theorem AWPQ_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.ConditionedMRDTs.AWPQ) (WTop Sal.ConditionedMRDTs.AWPQ)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.AWPQ)
      (invInvVCTop Sal.ConditionedMRDTs.AWPQ)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.ConditionedMRDTs.AWPQ) (WTop Sal.ConditionedMRDTs.AWPQ)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.AWPQ)
      (invInvVCTop Sal.ConditionedMRDTs.AWPQ) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.ConditionedMRDTs.AWPQ
      Sal.ConditionedMRDTs.AWPQ_coreVCs3CD Sal.ConditionedMRDTs.AWPQ_feasibleDeltaVCs3
      Sal.ConditionedMRDTs.AWPQ_cdVC3 trivial)) C hReach

#print axioms AWPQ_ra_linearizable3_eq

end

end Sal.ConditionedMRDTs
