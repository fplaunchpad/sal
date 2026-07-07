import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.MRDT_Instances.ORSet.ORSet
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge

/-!
# OR-Set-efficient — flat VC discharge and the conditioned capstone

Split out of the original monolithic `MRDT_Instances.lean`; declarations
verbatim, names unchanged.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §2. The OR-Set-efficient mirror -/

/-- Production `do_`: `Add e` at (ts, rid) first filters the prior
`(rid, _, e)` tag, then stakes `(rid, ts, e)`; `Rem e` filters the element. -/
def orEUpdate (s : (ℕ × ℕ × ℕ) → Bool) (o : Op ORSetOp) :
    (ℕ × ℕ × ℕ) → Bool :=
  match o.2.2 with
  | .add e => fun t =>
      (s t && !(decide (o.2.1 = t.1 ∧ e = t.2.2)))
        || decide (t = (o.2.1, o.1, e))
  | .rem e => fun t => s t && !(decide (e = t.2.2))

/-- Same three-way merge formula over `(rid, ts, elem)` triples. -/
def orEMergeL (l a b : (ℕ × ℕ × ℕ) → Bool) : (ℕ × ℕ × ℕ) → Bool :=
  fun t => (l t && (a t && b t)) || ((a t && !(l t)) || (b t && !(l t)))

/-- The OR-Set-efficient MRDT (mirror of
`Sal/MRDTs/OR_Set_Efficient/OR_Set_Efficient_MRDT.lean`). -/
noncomputable def ORSetE : ConditionedMRDTSig where
  State := (ℕ × ℕ × ℕ) → Bool
  dec_state := fun _ _ => Classical.propDecidable _
  init := fun _ => false
  AppOp := ORSetOp
  dec_op := inferInstance
  Query := Unit
  Value := (ℕ × ℕ × ℕ) → Bool
  update := orEUpdate
  merge := fun a b => orEMergeL (fun _ => false) a b
  query := fun s _ => s
  rc := orRc
  mergeL := orEMergeL
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem ORSetE_update_eq (s : ORSetE.State) (o : Op ORSetE.AppOp) :
    ORSetE.update s o = orEUpdate s o := rfl

theorem ORSetE_mergeL_eq (l a b : ORSetE.State) :
    ORSetE.mergeL l a b = orEMergeL l a b := rfl

/-- OR-Set-efficient `mergeL` is commutative in its branch arguments. -/
theorem ORSetE_mergeL_comm (l a b : ORSetE.State) :
    ORSetE.mergeL l a b = ORSetE.mergeL l b a := by
  funext t
  show orEMergeL l a b t = orEMergeL l b a t
  unfold orEMergeL
  cases l t <;> cases a t <;> cases b t <;> rfl

/-! ## The OR-Set-efficient discharge -/

/-- Same-replica, same-element `Add`s with distinct timestamps do not commute
in the OR-Set-efficient: the later add evicts the earlier tag. -/
theorem ORSetE_ncomm_add_add_same (ts₁ ts₂ r x : ℕ) (hts : ts₁ ≠ ts₂) :
    ¬ ORSetE.toCRDTSig.commutes (ts₁, r, ORSetOp.add x)
      (ts₂, r, ORSetOp.add x) := by
  intro hc
  have h0 := congrFun (hc (fun _ => false)) (r, ts₁, x)
  simp [ORSetE_update_eq, orEUpdate] at h0
  exact absurd h0 hts

/-! ## §1. Pointwise infrastructure -/

theorem orEUpdate_pointwise (a b : ORSetE.State) (o : Op ORSetE.AppOp)
    (q : ℕ × ℕ × ℕ) (h : a q = b q) :
    ORSetE.update a o q = ORSetE.update b o q := by
  rcases o with ⟨ts, rid, op⟩
  cases op with
  | add e =>
    show ((a q && !(decide (rid = q.1 ∧ e = q.2.2)))
        || decide (q = (rid, ts, e)))
      = ((b q && !(decide (rid = q.1 ∧ e = q.2.2)))
        || decide (q = (rid, ts, e)))
    rw [h]
  | rem e =>
    show (a q && !(decide (e = q.2.2))) = (b q && !(decide (e = q.2.2)))
    rw [h]

theorem orEApplySeq_agree {a b : ORSetE.State}
    (π : List (Op ORSetE.AppOp)) (q : ℕ × ℕ × ℕ) (h : a q = b q) :
    applySeq ORSetE.toCRDTSig a π q = applySeq ORSetE.toCRDTSig b π q := by
  induction π generalizing a b with
  | nil => exact h
  | cons o π ih => exact ih (orEUpdate_pointwise a b o q h)

/-! ## §2. Commutation classification -/

theorem ORSetE_commutes_symm {o₁ o₂ : Op ORSetE.AppOp}
    (h : ORSetE.toCRDTSig.commutes o₁ o₂) :
    ORSetE.toCRDTSig.commutes o₂ o₁ :=
  fun s => (h s).symm

theorem ORSetE_comm_add_add (ts₁ r₁ x₁ ts₂ r₂ x₂ : ℕ)
    (hne : ¬(r₁ = r₂ ∧ x₁ = x₂)) :
    ORSetE.toCRDTSig.commutes (ts₁, r₁, ORSetOp.add x₁)
      (ts₂, r₂, ORSetOp.add x₂) := by
  intro s
  funext t
  show ((((s t && !(decide (r₁ = t.1 ∧ x₁ = t.2.2)))
      || decide (t = (r₁, ts₁, x₁))) && !(decide (r₂ = t.1 ∧ x₂ = t.2.2)))
      || decide (t = (r₂, ts₂, x₂)))
    = ((((s t && !(decide (r₂ = t.1 ∧ x₂ = t.2.2)))
      || decide (t = (r₂, ts₂, x₂))) && !(decide (r₁ = t.1 ∧ x₁ = t.2.2)))
      || decide (t = (r₁, ts₁, x₁)))
  by_cases h₁ : t = (r₁, ts₁, x₁)
  · subst h₁
    have hf₂ : ¬(r₂ = r₁ ∧ x₂ = x₁) := fun ⟨hr, hx⟩ => hne ⟨hr.symm, hx.symm⟩
    have hne₂ : ((r₁, ts₁, x₁) : ℕ × ℕ × ℕ) ≠ (r₂, ts₂, x₂) := by
      intro h
      exact hne ⟨congrArg Prod.fst h, congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) h⟩
    rw [decide_eq_true
        (show ((r₁, ts₁, x₁) : ℕ × ℕ × ℕ) = (r₁, ts₁, x₁) from rfl),
      decide_eq_false hne₂, decide_eq_false hf₂]
    cases s (r₁, ts₁, x₁) <;>
      cases hf1 : decide (r₁ = r₁ ∧ x₁ = x₁) <;> rfl
  · by_cases h₂ : t = (r₂, ts₂, x₂)
    · subst h₂
      have hf₁ : ¬(r₁ = r₂ ∧ x₁ = x₂) := hne
      rw [decide_eq_true
          (show ((r₂, ts₂, x₂) : ℕ × ℕ × ℕ) = (r₂, ts₂, x₂) from rfl),
        decide_eq_false h₁, decide_eq_false hf₁]
      cases s (r₂, ts₂, x₂) <;>
        cases hf2 : decide (r₂ = r₂ ∧ x₂ = x₂) <;> rfl
    · rw [decide_eq_false h₁, decide_eq_false h₂]
      cases s t <;> cases hf1 : decide (r₁ = t.1 ∧ x₁ = t.2.2) <;>
        cases hf2 : decide (r₂ = t.1 ∧ x₂ = t.2.2) <;> rfl

theorem ORSetE_comm_add_rem_ne (ts₁ r₁ x ts₂ r₂ y : ℕ) (hxy : x ≠ y) :
    ORSetE.toCRDTSig.commutes (ts₁, r₁, ORSetOp.add x)
      (ts₂, r₂, ORSetOp.rem y) := by
  intro s
  funext t
  show (((s t && !(decide (r₁ = t.1 ∧ x = t.2.2)))
      || decide (t = (r₁, ts₁, x))) && !(decide (y = t.2.2)))
    = (((s t && !(decide (y = t.2.2))) && !(decide (r₁ = t.1 ∧ x = t.2.2)))
      || decide (t = (r₁, ts₁, x)))
  by_cases h₁ : t = (r₁, ts₁, x)
  · subst h₁
    have hy : ¬(y = ((r₁, ts₁, x) : ℕ × ℕ × ℕ).2.2) := fun h => hxy h.symm
    rw [decide_eq_true
        (show ((r₁, ts₁, x) : ℕ × ℕ × ℕ) = (r₁, ts₁, x) from rfl),
      decide_eq_false hy]
    cases s (r₁, ts₁, x) <;>
      cases hf : decide (r₁ = r₁ ∧ x = x) <;> rfl
  · rw [decide_eq_false h₁]
    cases s t <;> cases hg : decide (y = t.2.2) <;>
      cases hf : decide (r₁ = t.1 ∧ x = t.2.2) <;> rfl

theorem ORSetE_comm_rem_rem (ts₁ r₁ x₁ ts₂ r₂ x₂ : ℕ) :
    ORSetE.toCRDTSig.commutes (ts₁, r₁, ORSetOp.rem x₁)
      (ts₂, r₂, ORSetOp.rem x₂) := by
  intro s
  funext t
  show ((s t && !(decide (x₁ = t.2.2))) && !(decide (x₂ = t.2.2)))
    = ((s t && !(decide (x₂ = t.2.2))) && !(decide (x₁ = t.2.2)))
  cases s t <;> cases h1 : decide (x₁ = t.2.2) <;>
    cases h2 : decide (x₂ = t.2.2) <;> rfl

theorem ORSetE_ncomm_add_rem (ts₁ r₁ ts₂ r₂ x : ℕ) :
    ¬ ORSetE.toCRDTSig.commutes (ts₁, r₁, ORSetOp.add x)
      (ts₂, r₂, ORSetOp.rem x) := by
  intro h
  have h0 := congrFun (h (fun _ => false)) (r₁, ts₁, x)
  simp [ORSetE_update_eq, orEUpdate] at h0

/-- Classification: an `Add x @ rid` fails to commute only with a `Rem x` or
a same-replica `Add x` — exactly the killers of its tag. -/
theorem ORSetE_ncomm_add_dest {ts r x : ℕ} {o : Op ORSetE.AppOp}
    (h : ¬ ORSetE.toCRDTSig.commutes (ts, r, ORSetOp.add x) o) :
    o.2.2 = ORSetOp.rem x ∨ (o.2.2 = ORSetOp.add x ∧ o.2.1 = r) := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | add y =>
    by_cases hry : r = r' ∧ x = y
    · right
      exact ⟨show ORSetOp.add y = ORSetOp.add x by rw [hry.2],
        show r' = r by rw [hry.1]⟩
    · exact absurd (ORSetE_comm_add_add ts r x ts' r' y hry) h
  | rem y =>
    by_cases hxy : x = y
    · left
      show ORSetOp.rem y = ORSetOp.rem x
      rw [hxy]
    · exact absurd (ORSetE_comm_add_rem_ne ts r x ts' r' y hxy) h

theorem ORSetE_ncomm_rem_dest {ts r x : ℕ} {o : Op ORSetE.AppOp}
    (h : ¬ ORSetE.toCRDTSig.commutes (ts, r, ORSetOp.rem x) o) :
    o.2.2 = ORSetOp.add x := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | add y =>
    by_cases hxy : y = x
    · subst hxy; rfl
    · exact absurd
        (ORSetE_commutes_symm (ORSetE_comm_add_rem_ne ts' r' y ts r x hxy)) h
  | rem y => exact absurd (ORSetE_comm_rem_rem ts r x ts' r' y) h

/-! ## §3. The update layer (guarded) -/

theorem ORSetE_no_rc_chain :
    ∀ o₁ o₂ o₃ : Op ORSetE.AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ (ORSetE.toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∧
         ORSetE.toCRDTSig.rc o₂ o₃ = RcRes.Fst_then_snd) := by
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

theorem ORSetE_rc_non_comm_directional :
    ∀ o₁ o₂ : Op ORSetE.AppOp,
      distinctOps o₁ o₂ → differentReplicas o₁ o₂ →
      (¬ ORSetE.toCRDTSig.commutes o₁ o₂ ↔
       (ORSetE.toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∨
        ORSetE.toCRDTSig.rc o₂ o₁ = RcRes.Fst_then_snd)) := by
  intro o₁ o₂ _ hrep
  constructor
  · intro hnc
    rcases o₁ with ⟨ts₁, r₁, op₁⟩
    cases op₁ with
    | add x =>
      rcases ORSetE_ncomm_add_dest hnc with h2 | ⟨h2, h2r⟩
      · rcases o₂ with ⟨ts₂, r₂, op₂⟩
        have h2' : op₂ = ORSetOp.rem x := h2
        subst h2'
        right
        show (if x = x then RcRes.Fst_then_snd else RcRes.Either)
            = RcRes.Fst_then_snd
        rw [if_pos rfl]
      · exact absurd h2r.symm hrep
    | rem x =>
      have h2 := ORSetE_ncomm_rem_dest hnc
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
            exact ORSetE_ncomm_add_rem ts₂ r₂ ts₁ r₁ x₁
              (ORSetE_commutes_symm hc)
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
            exact ORSetE_ncomm_add_rem ts₁ r₁ ts₂ r₂ x₂
          · rw [if_neg hx] at h'
            exact absurd h' (fun hh => RcRes.noConfusion hh)
        | rem x₁ =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)

/-- `cond_comm_lift`: the swap perturbs at most the fresh tag; a final `Rem x`
kills it, a final same-replica `Add x` evicts it (its own tag having a
distinct timestamp by `distinctOps`). -/
theorem ORSetE_cond_comm_lift :
    ∀ (s : ORSetE.State) (e e' e'' : Op ORSetE.AppOp)
      (π : List (Op ORSetE.AppOp)),
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      ORSetE.toCRDTSig.rc e e' = RcRes.Fst_then_snd →
      ¬ ORSetE.toCRDTSig.commutes e' e'' →
      ORSetE.update (applySeq ORSetE.toCRDTSig
          (ORSetE.update (ORSetE.update s e') e) π) e''
        = ORSetE.update (applySeq ORSetE.toCRDTSig
            (ORSetE.update (ORSetE.update s e) e') π) e'' := by
  intro s e e' e'' π _ _ hd₃ hrc hnc
  rcases e with ⟨ts₁, r₁, op₁⟩
  rcases e' with ⟨ts₂, r₂, op₂⟩
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
      · rw [if_neg hx] at h'
        exact absurd h' (fun hh => RcRes.noConfusion hh)
      · subst hx
        have hagree : ∀ q : ℕ × ℕ × ℕ, q ≠ (r₂, ts₂, x₁) →
            (ORSetE.update (ORSetE.update s (ts₂, r₂, ORSetOp.add x₁))
              (ts₁, r₁, ORSetOp.rem x₁)) q
            = (ORSetE.update (ORSetE.update s (ts₁, r₁, ORSetOp.rem x₁))
                (ts₂, r₂, ORSetOp.add x₁)) q := by
          intro q hq
          show (((s q && !(decide (r₂ = q.1 ∧ x₁ = q.2.2)))
              || decide (q = (r₂, ts₂, x₁))) && !(decide (x₁ = q.2.2)))
            = (((s q && !(decide (x₁ = q.2.2)))
              && !(decide (r₂ = q.1 ∧ x₁ = q.2.2)))
              || decide (q = (r₂, ts₂, x₁)))
          rw [decide_eq_false hq]
          cases s q <;> cases hf : decide (r₂ = q.1 ∧ x₁ = q.2.2) <;>
            cases hg : decide (x₁ = q.2.2) <;> rfl
        rcases ORSetE_ncomm_add_dest hnc with h3 | ⟨h3, h3r⟩
        · -- final op is Rem x₁
          rcases e'' with ⟨ts₃, r₃, op₃⟩
          have h3' : op₃ = ORSetOp.rem x₁ := h3
          subst h3'
          funext q
          show (applySeq ORSetE.toCRDTSig
              (ORSetE.update (ORSetE.update s (ts₂, r₂, ORSetOp.add x₁))
                (ts₁, r₁, ORSetOp.rem x₁)) π q && !(decide (x₁ = q.2.2)))
            = (applySeq ORSetE.toCRDTSig
                (ORSetE.update (ORSetE.update s (ts₁, r₁, ORSetOp.rem x₁))
                  (ts₂, r₂, ORSetOp.add x₁)) π q && !(decide (x₁ = q.2.2)))
          by_cases hq2 : x₁ = q.2.2
          · rw [decide_eq_true hq2]
            simp
          · have hq : q ≠ (r₂, ts₂, x₁) := by
              intro h
              exact hq2 (by rw [h])
            rw [orEApplySeq_agree π q (hagree q hq)]
        · -- final op is the evicting same-replica Add x₁
          rcases e'' with ⟨ts₃, r₃, op₃⟩
          have h3' : op₃ = ORSetOp.add x₁ := h3
          subst h3'
          have h3r' : r₂ = r₃ := (show r₃ = r₂ from h3r).symm
          subst h3r'
          have hts : ts₂ ≠ ts₃ := hd₃
          funext q
          show ((applySeq ORSetE.toCRDTSig
              (ORSetE.update (ORSetE.update s (ts₂, r₂, ORSetOp.add x₁))
                (ts₁, r₁, ORSetOp.rem x₁)) π q
              && !(decide (r₂ = q.1 ∧ x₁ = q.2.2)))
              || decide (q = (r₂, ts₃, x₁)))
            = ((applySeq ORSetE.toCRDTSig
                (ORSetE.update (ORSetE.update s (ts₁, r₁, ORSetOp.rem x₁))
                  (ts₂, r₂, ORSetOp.add x₁)) π q
                && !(decide (r₂ = q.1 ∧ x₁ = q.2.2)))
                || decide (q = (r₂, ts₃, x₁)))
          by_cases hq : q = (r₂, ts₂, x₁)
          · subst hq
            rw [decide_eq_true
                (show (r₂ = ((r₂, ts₂, x₁) : ℕ × ℕ × ℕ).1
                  ∧ x₁ = ((r₂, ts₂, x₁) : ℕ × ℕ × ℕ).2.2) from ⟨rfl, rfl⟩)]
            simp
          · rw [orEApplySeq_agree π q (hagree q hq)]

/-! ## §4. The two-killer fold facts -/

/-- The killers of tag `q = (rid, ts, x)`: a `Rem x`, or an `Add x` at the
same replica (eviction). Note this is exactly `ORSetE_ncomm_add_dest`'s
conclusion for `q`'s adder. -/
def orEKills (q : ℕ × ℕ × ℕ) (o : Op ORSetE.AppOp) : Prop :=
  o.2.2 = ORSetOp.rem q.2.2 ∨ (o.2.2 = ORSetOp.add q.2.2 ∧ o.2.1 = q.1)

/-- A live tag has *its* adding event (tag-determined) in the list. -/
theorem ORSetE_fold_bound {ρ : List (Op ORSetE.AppOp)} {q : ℕ × ℕ × ℕ}
    (h : applySeq ORSetE.toCRDTSig ORSetE.init ρ q = true) :
    (q.2.1, q.1, ORSetOp.add q.2.2) ∈ ρ := by
  induction ρ using List.reverseRecOn with
  | nil => exact absurd (show (false : Bool) = true from h) Bool.noConfusion
  | append_singleton ρ o ih =>
    rw [applySeq_append_single] at h
    rcases o with ⟨ts, rid, op⟩
    cases op with
    | add e =>
      have h' : ((applySeq ORSetE.toCRDTSig ORSetE.init ρ q
          && !(decide (rid = q.1 ∧ e = q.2.2)))
          || decide (q = (rid, ts, e))) = true := h
      cases hd : decide (q = (rid, ts, e)) with
      | true =>
        have hq : q = (rid, ts, e) := of_decide_eq_true hd
        refine List.mem_append_right _ ?_
        have hqe : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp)
            = (ts, rid, ORSetOp.add e) := by
          rw [hq]
        rw [hqe]
        exact List.mem_cons_self
      | false =>
        rw [hd] at h'
        have h'' : applySeq ORSetE.toCRDTSig ORSetE.init ρ q = true := by
          rcases Bool.or_eq_true_iff.mp h' with h1 | h1
          · exact (Bool.and_eq_true_iff.mp h1).1
          · exact absurd h1 Bool.noConfusion
        exact List.mem_append_left _ (ih h'')
    | rem e =>
      have h' : (applySeq ORSetE.toCRDTSig ORSetE.init ρ q
          && !(decide (e = q.2.2))) = true := h
      exact List.mem_append_left _ (ih (Bool.and_eq_true_iff.mp h').1)

/-- A dead tag stays dead if its (unique, tag-determined) adder is absent. -/
theorem ORSetE_fold_stays_false {q : ℕ × ℕ × ℕ} :
    ∀ (β : List (Op ORSetE.AppOp)) (s : ORSetE.State),
      s q = false →
      ((q.2.1, q.1, ORSetOp.add q.2.2) ∉ β) →
      applySeq ORSetE.toCRDTSig s β q = false := by
  intro β
  induction β with
  | nil => intro s hs _; exact hs
  | cons o β ih =>
    intro s hs hβ
    have hupd : ORSetE.update s o q = false := by
      rcases o with ⟨ts, rid, op⟩
      cases op with
      | add e =>
        show ((s q && !(decide (rid = q.1 ∧ e = q.2.2)))
            || decide (q = (rid, ts, e))) = false
        rw [hs]
        cases hd : decide (q = (rid, ts, e)) with
        | false => rfl
        | true =>
          exfalso
          have hq : q = (rid, ts, e) := of_decide_eq_true hd
          refine hβ ?_
          have hqe : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp)
              = (ts, rid, ORSetOp.add e) := by
            rw [hq]
          rw [hqe]
          exact List.mem_cons_self
      | rem e =>
        show (s q && !(decide (e = q.2.2))) = false
        rw [hs]
        rfl
    exact ih (ORSetE.update s o) hupd
      (fun hmem => hβ (List.mem_cons_of_mem _ hmem))

/-- A live tag stays live if no killer follows. -/
theorem ORSetE_fold_stays_true {q : ℕ × ℕ × ℕ} :
    ∀ (β : List (Op ORSetE.AppOp)) (s : ORSetE.State),
      s q = true →
      (∀ o ∈ β, ¬ orEKills q o) →
      applySeq ORSetE.toCRDTSig s β q = true := by
  intro β
  induction β with
  | nil => intro s hs _; exact hs
  | cons o β ih =>
    intro s hs hβ
    have hupd : ORSetE.update s o q = true := by
      rcases o with ⟨ts, rid, op⟩
      cases op with
      | add e =>
        show ((s q && !(decide (rid = q.1 ∧ e = q.2.2)))
            || decide (q = (rid, ts, e))) = true
        rw [hs]
        have hf : ¬(rid = q.1 ∧ e = q.2.2) := by
          rintro ⟨hr, he⟩
          exact hβ _ List.mem_cons_self
            (Or.inr ⟨show ORSetOp.add e = ORSetOp.add q.2.2 by rw [he], hr⟩)
        rw [decide_eq_false hf]
        rfl
      | rem e =>
        show (s q && !(decide (e = q.2.2))) = true
        rw [hs]
        have hne : ¬(e = q.2.2) := by
          intro h
          exact hβ _ List.mem_cons_self
            (Or.inl (show ORSetOp.rem e = ORSetOp.rem q.2.2 by rw [h]))
        rw [decide_eq_false hne]
        rfl
    exact ih (ORSetE.update s o) hupd
      (fun o' ho' => hβ o' (List.mem_cons_of_mem _ ho'))

/-! ## §5. The canonical-state σ-facts -/

theorem ORSetE_canonical_bound
    {C : Sal.Emulation.Configuration ORSetE.toCRDTSig}
    {F : Set (Op ORSetE.AppOp)} {s : ORSetE.State} {q : ℕ × ℕ × ℕ}
    (hs : IsCanonicalState C F s) (hq : s q = true) :
    (q.2.1, q.1, ORSetOp.add q.2.2) ∈ F := by
  obtain ⟨ρ, hperm, -, hfold⟩ := hs
  rw [← hfold] at hq
  exact (hperm.2 _).mp (ORSetE_fold_bound hq)

/-- **Kill**: a live tag admits no killer vis-after its add. -/
theorem ORSetE_live_no_later_kill
    {C : Sal.Emulation.Configuration ORSetE.toCRDTSig}
    {F : Set (Op ORSetE.AppOp)} {s : ORSetE.State} {q : ℕ × ℕ × ℕ}
    (hs : IsCanonicalState C F s)
    (hq : s q = true)
    {k : Op ORSetE.AppOp}
    (hkF : k ∈ F) (hkill : orEKills q k)
    (hkne : k ≠ (q.2.1, q.1, ORSetOp.add q.2.2))
    (hvis : C.vis (q.2.1, q.1, ORSetOp.add q.2.2) k) : False := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  rw [← hfold] at hq
  have hnc : ¬ ORSetE.toCRDTSig.commutes
      (q.2.1, q.1, ORSetOp.add q.2.2) k := by
    rcases hkill with hk | ⟨hk, hkr⟩
    · rcases k with ⟨tsk, rk, opk⟩
      have hk' : opk = ORSetOp.rem q.2.2 := hk
      subst hk'
      exact ORSetE_ncomm_add_rem q.2.1 q.1 tsk rk q.2.2
    · rcases k with ⟨tsk, rk, opk⟩
      have hk' : opk = ORSetOp.add q.2.2 := hk
      subst hk'
      have hkr' : rk = q.1 := hkr
      subst hkr'
      have hts : q.2.1 ≠ tsk := fun h => hkne (by rw [h])
      exact ORSetE_ncomm_add_add_same q.2.1 tsk q.1 q.2.2 hts
  have hedge : loOn C F (q.2.1, q.1, ORSetOp.add q.2.2) k :=
    Or.inl ⟨hvis, hnc⟩
  have hkρ : k ∈ ρ := (hperm.2 k).mpr hkF
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem hkρ
  subst hsplit
  have haρ : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp)
      ∈ α ++ k :: β := (hperm.2 _).mpr (by
        have : applySeq ORSetE.toCRDTSig ORSetE.init (α ++ k :: β) q
            = true := hq
        exact (hperm.2 _).mp (ORSetE_fold_bound this))
  have hmid := List.pairwise_cons.mp (List.pairwise_append.mp hresp).2.1
  have haα : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp) ∈ α := by
    rcases List.mem_append.mp haρ with h | h
    · exact h
    · rcases List.mem_cons.mp h with h | h
      · exact absurd h.symm hkne
      · exact absurd hedge (hmid.1 _ h)
  have hstep : applySeq ORSetE.toCRDTSig ORSetE.init (α ++ k :: β)
      = applySeq ORSetE.toCRDTSig
          (ORSetE.update (applySeq ORSetE.toCRDTSig ORSetE.init α) k) β := by
    simp [applySeq, List.foldl_append]
  rw [hstep] at hq
  have hkillq : ORSetE.update (applySeq ORSetE.toCRDTSig ORSetE.init α) k q
      = false := by
    rcases hkill with hk | ⟨hk, hkr⟩
    · rcases k with ⟨tsk, rk, opk⟩
      have hk' : opk = ORSetOp.rem q.2.2 := hk
      subst hk'
      show (applySeq ORSetE.toCRDTSig ORSetE.init α q
          && !(decide (q.2.2 = q.2.2))) = false
      rw [decide_eq_true rfl]
      cases applySeq ORSetE.toCRDTSig ORSetE.init α q <;> rfl
    · rcases k with ⟨tsk, rk, opk⟩
      have hk' : opk = ORSetOp.add q.2.2 := hk
      subst hk'
      have hkr' : rk = q.1 := hkr
      subst hkr'
      have hts : q.2.1 ≠ tsk := fun h => hkne (by rw [h])
      show ((applySeq ORSetE.toCRDTSig ORSetE.init α q
          && !(decide (q.1 = q.1 ∧ q.2.2 = q.2.2)))
          || decide (q = (q.1, tsk, q.2.2))) = false
      have hqt : q ≠ (q.1, tsk, q.2.2) := by
        intro h
        exact hts (congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) h)
      rw [decide_eq_true (show (q.1 = q.1 ∧ q.2.2 = q.2.2) from ⟨rfl, rfl⟩),
        decide_eq_false hqt]
      cases applySeq ORSetE.toCRDTSig ORSetE.init α q <;> rfl
  have hnoadd : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp) ∉ β := by
    intro ho
    have hnd := hperm.1
    rw [List.nodup_append] at hnd
    exact hnd.2.2 _ haα _ (List.mem_cons_of_mem _ ho) rfl
  rw [ORSetE_fold_stays_false β _ hkillq hnoadd] at hq
  exact Bool.noConfusion hq

/-- **Live**: an add with no killer vis-after it yields a live tag; the
concurrent eviction case is impossible by same-replica totality. -/
theorem ORSetE_no_later_kill_live
    {C : Sal.Emulation.Configuration ORSetE.toCRDTSig}
    {F : Set (Op ORSetE.AppOp)} {s : ORSetE.State} {q : ℕ × ℕ × ℕ}
    (h_in : ∀ o ∈ F, o ∈ C.events)
    (hs : IsCanonicalState C F s)
    (haF : (q.2.1, q.1, ORSetOp.add q.2.2) ∈ F)
    (hno : ∀ k ∈ F, orEKills q k →
      ¬ C.vis (q.2.1, q.1, ORSetOp.add q.2.2) k) :
    s q = true := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  rw [← hfold]
  have haρ : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp) ∈ ρ :=
    (hperm.2 _).mpr haF
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem haρ
  subst hsplit
  have hcons := List.pairwise_cons.mp (List.pairwise_append.mp hresp).2.1
  have hnokill : ∀ o ∈ β, ¬ orEKills q o := by
    intro k hk hkill
    have hkF : k ∈ F := (hperm.2 k).mp
      (List.mem_append_right _ (List.mem_cons_of_mem _ hk))
    have hkne : k ≠ (q.2.1, q.1, ORSetOp.add q.2.2) := by
      intro h
      have hnd := hperm.1
      rw [List.nodup_append, List.nodup_cons] at hnd
      exact hnd.2.1.1 (h ▸ hk)
    have hnovis : ¬ C.vis (q.2.1, q.1, ORSetOp.add q.2.2) k :=
      hno k hkF hkill
    -- the killer does not commute with the add
    have hnc_ak : ¬ ORSetE.toCRDTSig.commutes
        (q.2.1, q.1, ORSetOp.add q.2.2) k := by
      rcases hkill with hk' | ⟨hk', hkr⟩
      · rcases k with ⟨tsk, rk, opk⟩
        have h' : opk = ORSetOp.rem q.2.2 := hk'
        subst h'
        exact ORSetE_ncomm_add_rem q.2.1 q.1 tsk rk q.2.2
      · rcases k with ⟨tsk, rk, opk⟩
        have h' : opk = ORSetOp.add q.2.2 := hk'
        subst h'
        have hkr' : rk = q.1 := hkr
        subst hkr'
        have hts : q.2.1 ≠ tsk := fun h => hkne (by rw [h])
        exact ORSetE_ncomm_add_add_same q.2.1 tsk q.1 q.2.2 hts
    by_cases hvk : C.vis k (q.2.1, q.1, ORSetOp.add q.2.2)
    · exact absurd (Or.inl ⟨hvk, fun hc => hnc_ak (ORSetE_commutes_symm hc)⟩)
        (hcons.1 _ hk)
    · rcases hkill with hk' | ⟨hk', hkr⟩
      · -- concurrent rem-killer: the rc-edge is unabsorbed
        rcases k with ⟨tsk, rk, opk⟩
        have h' : opk = ORSetOp.rem q.2.2 := hk'
        subst h'
        refine absurd (Or.inr ⟨hvk, hnovis, ?_, ?_⟩) (hcons.1 _ hk)
        · show (if q.2.2 = q.2.2 then RcRes.Fst_then_snd else RcRes.Either)
              = RcRes.Fst_then_snd
          rw [if_pos rfl]
        · rintro ⟨e₃, he₃F, hve₃, hnce₃⟩
          exact hno e₃ he₃F (ORSetE_ncomm_add_dest hnce₃) hve₃
      · -- concurrent same-replica eviction: impossible by totality
        rcases k with ⟨tsk, rk, opk⟩
        have h' : opk = ORSetOp.add q.2.2 := hk'
        subst h'
        have hkr' : rk = q.1 := hkr
        subst hkr'
        obtain ⟨rK, sK, hLK, hsK⟩ := h_in _ hkF
        obtain ⟨rA, sA, hLA, hsA⟩ := h_in _ haF
        rcases C.vis_total_same_replica hLK hsK hLA hsA hkne rfl
          with hv | hv
        · exact hvk hv
        · exact hnovis hv
  have hstep : applySeq ORSetE.toCRDTSig ORSetE.init
      (α ++ ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp) :: β)
      = applySeq ORSetE.toCRDTSig
          (ORSetE.update (applySeq ORSetE.toCRDTSig ORSetE.init α)
            (q.2.1, q.1, ORSetOp.add q.2.2)) β := by
    simp [applySeq, List.foldl_append]
  rw [hstep]
  refine ORSetE_fold_stays_true β _ ?_ hnokill
  show ((applySeq ORSetE.toCRDTSig ORSetE.init α q
      && !(decide (q.1 = q.1 ∧ q.2.2 = q.2.2)))
      || decide (q = (q.1, q.2.1, q.2.2))) = true
  rw [decide_eq_true
      (show q = (q.1, q.2.1, q.2.2) from Prod.ext rfl (Prod.ext rfl rfl))]
  simp

/-! ## §6. The maximal-event trichotomies and `CDVC3` -/

/-- Maximal `Rem`: every live tag of the element in `σ(U∖e)` is live in the
punctured downset. -/
theorem ORSetE_rem_max_trichotomy
    {C : Sal.Emulation.Configuration ORSetE.toCRDTSig}
    {U : Set (Op ORSetE.AppOp)} {A B : ORSetE.State}
    {ts rid : ℕ} {q : ℕ × ℕ × ℕ}
    (h_ir : ∀ a : Op ORSetE.AppOp, ¬ C.vis a a)
    (h_in : ∀ o ∈ U, o ∈ C.events)
    (h_cl : ∀ a b, C.vis a b → ¬ ORSetE.toCRDTSig.commutes a b →
      b ∈ U → a ∈ U)
    (h_e : (ts, rid, ORSetOp.rem q.2.2) ∈ U)
    (h_max : ∀ y ∈ U, y ≠ (ts, rid, ORSetOp.rem q.2.2) →
      ¬ loOn C U (ts, rid, ORSetOp.rem q.2.2) y)
    (hA : IsCanonicalState C (U \ {(ts, rid, ORSetOp.rem q.2.2)}) A)
    (hB : IsCanonicalState C
      (downset C (ts, rid, ORSetOp.rem q.2.2)
        \ {(ts, rid, ORSetOp.rem q.2.2)}) B)
    (hqA : A q = true) : B q = true := by
  have h_dsub : downset C (ts, rid, ORSetOp.rem q.2.2) ⊆ U :=
    downset_subset h_cl h_e
  have haU' := ORSetE_canonical_bound hA hqA
  have hane : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp)
      ≠ (ts, rid, ORSetOp.rem q.2.2) := by
    intro h
    exact ORSetOp.noConfusion (congrArg (fun z : Op ORSetE.AppOp => z.2.2) h)
  have hnc_ae : ¬ ORSetE.toCRDTSig.commutes (q.2.1, q.1, ORSetOp.add q.2.2)
      (ts, rid, ORSetOp.rem q.2.2) :=
    ORSetE_ncomm_add_rem q.2.1 q.1 ts rid q.2.2
  by_cases hva : C.vis (q.2.1, q.1, ORSetOp.add q.2.2)
      (ts, rid, ORSetOp.rem q.2.2)
  · have haD : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp)
        ∈ downset C (ts, rid, ORSetOp.rem q.2.2)
          \ {(ts, rid, ORSetOp.rem q.2.2)} :=
      ⟨Or.inr (Relation.TransGen.single ⟨hva, hnc_ae⟩), hane⟩
    refine ORSetE_no_later_kill_live
      (fun o ho => h_in o (h_dsub ho.1)) hB haD ?_
    intro k hkD hkill hvak
    by_cases hka : k = (q.2.1, q.1, ORSetOp.add q.2.2)
    · rw [hka] at hvak
      exact h_ir _ hvak
    · exact ORSetE_live_no_later_kill hA hqA
        ⟨h_dsub hkD.1, hkD.2⟩ hkill hka hvak
  · by_cases hvea : C.vis (ts, rid, ORSetOp.rem q.2.2)
        (q.2.1, q.1, ORSetOp.add q.2.2)
    · exact absurd
        (Or.inl ⟨hvea, fun hc => hnc_ae (ORSetE_commutes_symm hc)⟩)
        (h_max _ haU'.1 hane)
    · exfalso
      refine h_max _ haU'.1 hane
        (Or.inr ⟨hvea, hva, ?_, ?_⟩)
      · show (if q.2.2 = q.2.2 then RcRes.Fst_then_snd else RcRes.Either)
            = RcRes.Fst_then_snd
        rw [if_pos rfl]
      · rintro ⟨e₃, he₃U, hve₃, hnce₃⟩
        by_cases he₃a : e₃ = (q.2.1, q.1, ORSetOp.add q.2.2)
        · rw [he₃a] at hve₃
          exact h_ir _ hve₃
        · have he₃ne : e₃ ≠ (ts, rid, ORSetOp.rem q.2.2) := by
            intro h
            rw [h] at hve₃
            exact hva hve₃
          exact ORSetE_live_no_later_kill hA hqA ⟨he₃U, he₃ne⟩
            (ORSetE_ncomm_add_dest hnce₃) he₃a hve₃

/-- Maximal `Add` at replica `q.1`: every live evicted-family tag of `σ(U∖e)`
is live in the punctured downset — by same-replica totality. -/
theorem ORSetE_add_max_trichotomy
    {C : Sal.Emulation.Configuration ORSetE.toCRDTSig}
    {U : Set (Op ORSetE.AppOp)} {A B : ORSetE.State}
    {ts : ℕ} {q : ℕ × ℕ × ℕ}
    (h_ir : ∀ a : Op ORSetE.AppOp, ¬ C.vis a a)
    (h_in : ∀ o ∈ U, o ∈ C.events)
    (h_cl : ∀ a b, C.vis a b → ¬ ORSetE.toCRDTSig.commutes a b →
      b ∈ U → a ∈ U)
    (h_e : (ts, q.1, ORSetOp.add q.2.2) ∈ U)
    (h_max : ∀ y ∈ U, y ≠ (ts, q.1, ORSetOp.add q.2.2) →
      ¬ loOn C U (ts, q.1, ORSetOp.add q.2.2) y)
    (hA : IsCanonicalState C (U \ {(ts, q.1, ORSetOp.add q.2.2)}) A)
    (hB : IsCanonicalState C
      (downset C (ts, q.1, ORSetOp.add q.2.2)
        \ {(ts, q.1, ORSetOp.add q.2.2)}) B)
    (hqts : q.2.1 ≠ ts)
    (hqA : A q = true) : B q = true := by
  have h_dsub : downset C (ts, q.1, ORSetOp.add q.2.2) ⊆ U :=
    downset_subset h_cl h_e
  have haU' := ORSetE_canonical_bound hA hqA
  have hane : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp)
      ≠ (ts, q.1, ORSetOp.add q.2.2) := by
    intro h
    exact hqts (congrArg (fun z : Op ORSetE.AppOp => z.1) h)
  have hnc_ae : ¬ ORSetE.toCRDTSig.commutes (q.2.1, q.1, ORSetOp.add q.2.2)
      (ts, q.1, ORSetOp.add q.2.2) :=
    ORSetE_ncomm_add_add_same q.2.1 ts q.1 q.2.2 hqts
  -- same replica: vis-comparable
  obtain ⟨rA, sA, hLA, hsA⟩ := h_in _ haU'.1
  obtain ⟨rE, sE, hLE, hsE⟩ := h_in _ h_e
  rcases C.vis_total_same_replica hLA hsA hLE hsE hane rfl with hva | hvea
  · have haD : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp)
        ∈ downset C (ts, q.1, ORSetOp.add q.2.2)
          \ {(ts, q.1, ORSetOp.add q.2.2)} :=
      ⟨Or.inr (Relation.TransGen.single ⟨hva, hnc_ae⟩), hane⟩
    refine ORSetE_no_later_kill_live
      (fun o ho => h_in o (h_dsub ho.1)) hB haD ?_
    intro k hkD hkill hvak
    by_cases hka : k = (q.2.1, q.1, ORSetOp.add q.2.2)
    · rw [hka] at hvak
      exact h_ir _ hvak
    · exact ORSetE_live_no_later_kill hA hqA
        ⟨h_dsub hkD.1, hkD.2⟩ hkill hka hvak
  · exact absurd
      (Or.inl ⟨hvea, fun hc => hnc_ae (ORSetE_commutes_symm hc)⟩)
      (h_max _ haU'.1 hane)

/-- **`CDVC3` for the OR-Set-efficient.** -/
theorem ORSetE_cdVC3 : CDVC3 ORSetE := by
  intro C U A B e h_tr h_ir h_in h_cl h_e h_max hA hB
  rcases e with ⟨ts, rid, op⟩
  cases op with
  | add x =>
    funext q
    show ((B q && (A q && ORSetE.update B (ts, rid, ORSetOp.add x) q))
        || ((A q && !(B q))
        || (ORSetE.update B (ts, rid, ORSetOp.add x) q && !(B q))))
      = ((A q && !(decide (rid = q.1 ∧ x = q.2.2)))
        || decide (q = (rid, ts, x)))
    show ((B q && (A q && ((B q && !(decide (rid = q.1 ∧ x = q.2.2)))
        || decide (q = (rid, ts, x)))))
        || ((A q && !(B q))
        || (((B q && !(decide (rid = q.1 ∧ x = q.2.2)))
        || decide (q = (rid, ts, x))) && !(B q))))
      = ((A q && !(decide (rid = q.1 ∧ x = q.2.2)))
        || decide (q = (rid, ts, x)))
    by_cases hq : q = (rid, ts, x)
    · subst hq
      have hBt : B (rid, ts, x) = false := by
        cases hBt : B (rid, ts, x) with
        | false => rfl
        | true =>
          have hmem := ORSetE_canonical_bound hB hBt
          exact absurd rfl hmem.2
      rw [hBt, decide_eq_true
        (show ((rid, ts, x) : ℕ × ℕ × ℕ) = (rid, ts, x) from rfl)]
      cases A (rid, ts, x) <;>
        cases hf : decide (rid = ((rid, ts, x) : ℕ × ℕ × ℕ).1
          ∧ x = ((rid, ts, x) : ℕ × ℕ × ℕ).2.2) <;> rfl
    · by_cases hev : rid = q.1 ∧ x = q.2.2
      · have hqts : q.2.1 ≠ ts := by
          intro h
          exact hq (Prod.ext hev.1.symm (Prod.ext h hev.2.symm))
        rw [hev.1, hev.2] at h_e h_max hA hB
        have himp := ORSetE_add_max_trichotomy h_ir h_in h_cl h_e h_max
          hA hB hqts
        rw [decide_eq_true hev, decide_eq_false hq]
        cases hBq : B q with
        | true => cases A q <;> rfl
        | false =>
          cases hAq : A q with
          | false => rfl
          | true => exact Bool.noConfusion (hBq.symm.trans (himp hAq))
      · rw [decide_eq_false hev, decide_eq_false hq]
        cases B q <;> cases A q <;> rfl
  | rem x =>
    funext q
    show ((B q && (A q && ORSetE.update B (ts, rid, ORSetOp.rem x) q))
        || ((A q && !(B q))
        || (ORSetE.update B (ts, rid, ORSetOp.rem x) q && !(B q))))
      = (A q && !(decide (x = q.2.2)))
    show ((B q && (A q && (B q && !(decide (x = q.2.2)))))
        || ((A q && !(B q))
        || ((B q && !(decide (x = q.2.2))) && !(B q))))
      = (A q && !(decide (x = q.2.2)))
    by_cases hx : x = q.2.2
    · rw [hx] at h_e h_max hA hB
      have himp := ORSetE_rem_max_trichotomy h_ir h_in h_cl h_e h_max hA hB
      rw [decide_eq_true hx]
      cases hBq : B q with
      | true => cases A q <;> rfl
      | false =>
        cases hAq : A q with
        | false => rfl
        | true => exact Bool.noConfusion (hBq.symm.trans (himp hAq))
    · rw [decide_eq_false hx]
      cases B q <;> cases A q <;> rfl

/-! ## §7. The feasible delta laws -/

/-- The redistribution law is a Boolean tautology for the ORSetE merge. -/
theorem orEMergeL_redistribute (B t₀ t₁ t₂ u : ORSetE.State) :
    orEMergeL (orEMergeL B t₀ u) (orEMergeL B t₁ u) (orEMergeL B t₂ u)
      = orEMergeL B (orEMergeL t₀ t₁ t₂) u := by
  funext q
  show ((orEMergeL B t₀ u q && (orEMergeL B t₁ u q && orEMergeL B t₂ u q))
      || ((orEMergeL B t₁ u q && !(orEMergeL B t₀ u q))
      || (orEMergeL B t₂ u q && !(orEMergeL B t₀ u q))))
    = ((B q && (orEMergeL t₀ t₁ t₂ q && u q))
      || ((orEMergeL t₀ t₁ t₂ q && !(B q)) || (u q && !(B q))))
  show ((((B q && (t₀ q && u q)) || ((t₀ q && !(B q)) || (u q && !(B q))))
      && (((B q && (t₁ q && u q)) || ((t₁ q && !(B q)) || (u q && !(B q))))
      && ((B q && (t₂ q && u q)) || ((t₂ q && !(B q)) || (u q && !(B q))))))
      || ((((B q && (t₁ q && u q)) || ((t₁ q && !(B q)) || (u q && !(B q))))
      && !(((B q && (t₀ q && u q)) || ((t₀ q && !(B q)) || (u q && !(B q))))))
      || (((B q && (t₂ q && u q)) || ((t₂ q && !(B q)) || (u q && !(B q))))
      && !(((B q && (t₀ q && u q))
      || ((t₀ q && !(B q)) || (u q && !(B q))))))))
    = ((B q && (((t₀ q && (t₁ q && t₂ q)) || ((t₁ q && !(t₀ q))
      || (t₂ q && !(t₀ q)))) && u q))
      || ((((t₀ q && (t₁ q && t₂ q)) || ((t₁ q && !(t₀ q))
      || (t₂ q && !(t₀ q)))) && !(B q)) || (u q && !(B q))))
  cases B q <;> cases t₀ q <;> cases t₁ q <;> cases t₂ q <;>
    cases u q <;> rfl

/-- **The feasible delta contract for the OR-Set-efficient.** -/
theorem ORSetE_feasibleDeltaVCs3 : FeasibleDeltaVCs3 ORSetE := by
  refine ⟨?_, ?_, ?_⟩
  · -- feasible_init (unconditional for ORSetE)
    intro C ev s _ _
    funext q
    show ((false && (false && s q)) || ((false && !false)
        || (s q && !false))) = s q
    cases s q <;> rfl
  · -- feasible_local_redistribute
    intro C ev₁ ev₂ s₀ B t₁ s₂ e h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ he₁ he₂
      h_max hc₀ hB ht₁ hc₂
    -- the e-agnostic exclusion: a tag live in the punctured downset and in
    -- ev₂ but dead in ev₁ ∩ ev₂ is impossible
    have himp2 : ∀ q : ℕ × ℕ × ℕ, B q = true → s₂ q = true →
        s₀ q = true := by
      intro q hqB hqs₂
      have haB := ORSetE_canonical_bound hB hqB
      have ha₂ := ORSetE_canonical_bound hc₂ hqs₂
      have ha₁ : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp)
          ∈ ev₁ := downset_subset h_cl₁ he₁ haB.1
      refine ORSetE_no_later_kill_live (fun o ho => h_in₁ o ho.1)
        hc₀ ⟨ha₁, ha₂⟩ ?_
      intro k hk₀ hkill hvak
      by_cases hka : k = (q.2.1, q.1, ORSetOp.add q.2.2)
      · rw [hka] at hvak
        exact h_ir _ hvak
      · exact ORSetE_live_no_later_kill hc₂ hqs₂ hk₀.2 hkill hka hvak
    rcases e with ⟨ts, rid, op⟩
    cases op with
    | add x =>
      have hBt : B (rid, ts, x) = false := by
        cases hBt : B (rid, ts, x) with
        | false => rfl
        | true =>
          have hmem := ORSetE_canonical_bound hB hBt
          exact absurd rfl hmem.2
      have hs₀t : s₀ (rid, ts, x) = false := by
        cases h : s₀ (rid, ts, x) with
        | false => rfl
        | true =>
          have hmem := ORSetE_canonical_bound hc₀ h
          exact absurd hmem.2 he₂
      funext q
      show ((s₀ q && ((orEMergeL B t₁
          (ORSetE.update B (ts, rid, ORSetOp.add x)) q) && s₂ q))
          || (((orEMergeL B t₁
          (ORSetE.update B (ts, rid, ORSetOp.add x)) q) && !(s₀ q))
          || (s₂ q && !(s₀ q))))
        = ((B q && ((orEMergeL s₀ t₁ s₂ q)
          && ORSetE.update B (ts, rid, ORSetOp.add x) q))
          || (((orEMergeL s₀ t₁ s₂ q) && !(B q))
          || (ORSetE.update B (ts, rid, ORSetOp.add x) q && !(B q))))
      show ((s₀ q && (((B q && (t₁ q && ((B q
          && !(decide (rid = q.1 ∧ x = q.2.2)))
          || decide (q = (rid, ts, x)))))
          || ((t₁ q && !(B q)) || (((B q
          && !(decide (rid = q.1 ∧ x = q.2.2)))
          || decide (q = (rid, ts, x))) && !(B q)))) && s₂ q))
          || ((((B q && (t₁ q && ((B q
          && !(decide (rid = q.1 ∧ x = q.2.2)))
          || decide (q = (rid, ts, x)))))
          || ((t₁ q && !(B q)) || (((B q
          && !(decide (rid = q.1 ∧ x = q.2.2)))
          || decide (q = (rid, ts, x))) && !(B q)))) && !(s₀ q))
          || (s₂ q && !(s₀ q))))
        = ((B q && (((s₀ q && (t₁ q && s₂ q)) || ((t₁ q && !(s₀ q))
          || (s₂ q && !(s₀ q)))) && ((B q
          && !(decide (rid = q.1 ∧ x = q.2.2)))
          || decide (q = (rid, ts, x)))))
          || ((((s₀ q && (t₁ q && s₂ q)) || ((t₁ q && !(s₀ q))
          || (s₂ q && !(s₀ q)))) && !(B q))
          || (((B q && !(decide (rid = q.1 ∧ x = q.2.2)))
          || decide (q = (rid, ts, x))) && !(B q))))
      by_cases hq : q = (rid, ts, x)
      · subst hq
        rw [hBt, hs₀t, decide_eq_true
          (show ((rid, ts, x) : ℕ × ℕ × ℕ) = (rid, ts, x) from rfl)]
        cases t₁ (rid, ts, x) <;> cases s₂ (rid, ts, x) <;>
          cases hf : decide (rid = ((rid, ts, x) : ℕ × ℕ × ℕ).1
            ∧ x = ((rid, ts, x) : ℕ × ℕ × ℕ).2.2) <;> rfl
      · by_cases hev : rid = q.1 ∧ x = q.2.2
        · rw [decide_eq_true hev, decide_eq_false hq]
          cases hBq : B q with
          | false => cases s₀ q <;> cases t₁ q <;> cases s₂ q <;> rfl
          | true =>
            cases hs₀q : s₀ q with
            | true => cases t₁ q <;> cases s₂ q <;> rfl
            | false =>
              cases hs₂q : s₂ q with
              | false => cases t₁ q <;> rfl
              | true =>
                exact Bool.noConfusion
                  (hs₀q.symm.trans (himp2 q hBq hs₂q))
        · rw [decide_eq_false hev, decide_eq_false hq]
          cases s₀ q <;> cases B q <;> cases t₁ q <;> cases s₂ q <;> rfl
    | rem x =>
      funext q
      show ((s₀ q && ((orEMergeL B t₁
          (ORSetE.update B (ts, rid, ORSetOp.rem x)) q) && s₂ q))
          || (((orEMergeL B t₁
          (ORSetE.update B (ts, rid, ORSetOp.rem x)) q) && !(s₀ q))
          || (s₂ q && !(s₀ q))))
        = ((B q && ((orEMergeL s₀ t₁ s₂ q)
          && ORSetE.update B (ts, rid, ORSetOp.rem x) q))
          || (((orEMergeL s₀ t₁ s₂ q) && !(B q))
          || (ORSetE.update B (ts, rid, ORSetOp.rem x) q && !(B q))))
      show ((s₀ q && (((B q && (t₁ q && (B q && !(decide (x = q.2.2)))))
          || ((t₁ q && !(B q)) || ((B q && !(decide (x = q.2.2)))
          && !(B q)))) && s₂ q))
          || ((((B q && (t₁ q && (B q && !(decide (x = q.2.2)))))
          || ((t₁ q && !(B q)) || ((B q && !(decide (x = q.2.2)))
          && !(B q)))) && !(s₀ q))
          || (s₂ q && !(s₀ q))))
        = ((B q && (((s₀ q && (t₁ q && s₂ q)) || ((t₁ q && !(s₀ q))
          || (s₂ q && !(s₀ q)))) && (B q && !(decide (x = q.2.2)))))
          || ((((s₀ q && (t₁ q && s₂ q)) || ((t₁ q && !(s₀ q))
          || (s₂ q && !(s₀ q)))) && !(B q))
          || ((B q && !(decide (x = q.2.2))) && !(B q))))
      by_cases hx : x = q.2.2
      · rw [decide_eq_true hx]
        cases hBq : B q with
        | false => cases s₀ q <;> cases t₁ q <;> cases s₂ q <;> rfl
        | true =>
          cases hs₀q : s₀ q with
          | true => cases t₁ q <;> cases s₂ q <;> rfl
          | false =>
            cases hs₂q : s₂ q with
            | false => cases t₁ q <;> rfl
            | true =>
              exact Bool.noConfusion
                (hs₀q.symm.trans (himp2 q hBq hs₂q))
      · rw [decide_eq_false hx]
        cases s₀ q <;> cases B q <;> cases t₁ q <;> cases s₂ q <;> rfl
  · -- feasible_redistribute: the unconditional tautology
    intro C ev₁ ev₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _ _
    exact orEMergeL_redistribute B t₀ t₁ t₂ (ORSetE.update B e)

/-! ## §8. The bundles and the end-to-end theorem -/

theorem ORSetE_updateVCs : UpdateVCs ORSetE.toCRDTSig :=
  ⟨ORSetE_rc_non_comm_directional, ORSetE_no_rc_chain,
   ORSetE_cond_comm_lift⟩

theorem ORSetE_coreVCs3CD : CoreVCs3CD ORSetE :=
  ⟨ORSetE_updateVCs, ORSetE_mergeL_comm⟩

/-- The ternary Join Lemma for the production OR-Set-efficient. -/
theorem ORSetE_joinLemma3 : JoinLemma3 ORSetE :=
  join_lemma3_of_cd_feasible ORSetE_coreVCs3CD ORSetE_feasibleDeltaVCs3
    ORSetE_cdVC3

open LabeledTS in
/-- **End-to-end RA-linearizability for the production OR-Set-efficient.** -/
theorem ORSetE_ra_linearizable3
    (C : Configuration ORSetE)
    (hReach : (labeledTS3 ORSetE).ReachableFrom
      (initConfig ORSetE trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_join ORSetE_joinLemma3 C hReach


/-! ## The conditioned capstone — identity instantiation of the generic framework -/

section
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.FlatGeneric

/-- **OR-Set-efficient over the generic framework.** -/
theorem ORSetE_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.ConditionedMRDTs.ORSetE) (WTop Sal.ConditionedMRDTs.ORSetE)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.ORSetE)
      (invInvVCTop Sal.ConditionedMRDTs.ORSetE)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.ConditionedMRDTs.ORSetE) (WTop Sal.ConditionedMRDTs.ORSetE)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.ORSetE)
      (invInvVCTop Sal.ConditionedMRDTs.ORSetE) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.ConditionedMRDTs.ORSetE
      Sal.ConditionedMRDTs.ORSetE_coreVCs3CD Sal.ConditionedMRDTs.ORSetE_feasibleDeltaVCs3
      Sal.ConditionedMRDTs.ORSetE_cdVC3 trivial)) C hReach

#print axioms ORSetE_ra_linearizable3_eq

end

end Sal.ConditionedMRDTs
