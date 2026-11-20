import LeanProofs.Implementations.EfficientORSet.LinearExtension
import LeanProofs.Interface.Laws

/-!
# The efficient OR-set: `Laws(D_type)`, over concurrent events

This row motivated the guard on RC-NON-COMM. Two `add x` events issued by
one replica do not commute, and they carry the same operation, so an
unguarded RC-NON-COMM would demand `add x --rc--> add x` and NO-RC-CHAIN
would refute it.

With the guard the pair is out of scope, because one replica's events are
always causally ordered. Everything still in scope behaves:

| pair, different replicas | commutes | `rc` edge |
| ------------------------ | -------- | --------- |
| `add x` / `add y`        | yes      | no        |
| `add x` / `remove x`     | no       | yes       |
| `remove x` / `remove y`  | yes      | no        |

`Laws` therefore holds. It is **not** enough to reach `Soundness/`, which
also wants `PayloadDetermined`, and that is false here: the same two `add x`
operations commute across replicas and fail to commute within one. The
row's certificate stays in `Certificate.lean`, which needs no replay
contract at all.
-/

namespace LeanProofs.Implementations.EfficientORSet

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

variable {α : Type} [DecidableEq α]

/-- `rc` on operations: `remove x` before `add x`. -/
def rcOps : AppOp α → AppOp α → OrderResult
  | .remove x, .add y => if x = y then OrderResult.Fst_then_snd else OrderResult.Either
  | .add x, .remove y => if x = y then OrderResult.Snd_then_fst else OrderResult.Either
  | _, _ => OrderResult.Either

variable (α)

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def itype : MRDTType where
  OType := AppOp α
  decOType := inferInstance
  QType := α
  ValType := Bool

/-- The same tuple as `D`, in the shape `Interface/` expects. -/
@[reducible] def I : Impl (itype α) where
  Sigma := State α
  decSigma := inferInstance
  sigma0 := ∅
  do_ := update
  merge := merge
  query s x := decide (x ∈ elements s)
  rc := rcOps

variable {α}

@[simp] theorem mem_do (p : Record α) (s : State α) (e : (I α).Event) :
    p ∈ (I α).do_ s e ↔ e = (p.2.1, p.1, AppOp.add p.2.2) ∨ (p ∈ s ∧ ¬ kills p.1 p.2.2 e) :=
  mem_update_iff p s e

/-- An add never touches another replica's records, so two adds from
different replicas commute whatever they add. -/
theorem commutes_add_add {e₁ e₂ : (I α).Event} {x y : α}
    (h₁ : e₁.2.2 = AppOp.add x) (h₂ : e₂.2.2 = AppOp.add y)
    (hr : (I α).rep e₁ ≠ (I α).rep e₂) : (I α).Commutes e₁ e₂ := by
  rcases e₁ with ⟨t₁, r₁, o₁⟩
  rcases e₂ with ⟨t₂, r₂, o₂⟩
  simp only at h₁ h₂
  subst h₁; subst h₂
  simp only [Impl.rep, Op.rep] at hr
  intro s
  ext p
  rcases p with ⟨r, t, z⟩
  simp [update, Finset.mem_insert, Finset.mem_filter, Prod.ext_iff]
  constructor
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨h, hk⟩) <;> tauto
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨h, hk⟩) <;> tauto

/-- Two removes are filters and commute. -/
theorem commutes_rem_rem {e₁ e₂ : (I α).Event} {x y : α}
    (h₁ : e₁.2.2 = AppOp.remove x) (h₂ : e₂.2.2 = AppOp.remove y) :
    (I α).Commutes e₁ e₂ := by
  rcases e₁ with ⟨t₁, r₁, o₁⟩
  rcases e₂ with ⟨t₂, r₂, o₂⟩
  simp only at h₁ h₂
  subst h₁; subst h₂
  intro s
  ext p
  rcases p with ⟨r, t, z⟩
  simp [update, Finset.mem_filter]
  tauto

/-- An add and a remove of **different** elements commute. -/
theorem commutes_add_rem {e₁ e₂ : (I α).Event} {x y : α}
    (h₁ : e₁.2.2 = AppOp.add x) (h₂ : e₂.2.2 = AppOp.remove y) (hxy : x ≠ y) :
    (I α).Commutes e₁ e₂ := by
  rcases e₁ with ⟨t₁, r₁, o₁⟩
  rcases e₂ with ⟨t₂, r₂, o₂⟩
  simp only at h₁ h₂
  subst h₁; subst h₂
  intro s
  ext p
  rcases p with ⟨r, t, z⟩
  simp [update, Finset.mem_insert, Finset.mem_filter, Prod.ext_iff]
  aesop

/-- An add and a remove of the **same** element do not commute. -/
theorem not_commutes_add_rem {e₁ e₂ : (I α).Event} {x : α}
    (h₁ : e₁.2.2 = AppOp.add x) (h₂ : e₂.2.2 = AppOp.remove x) :
    ¬ (I α).Commutes e₁ e₂ := by
  rcases e₁ with ⟨t₁, r₁, o₁⟩
  rcases e₂ with ⟨t₂, r₂, o₂⟩
  simp only at h₁ h₂
  subst h₁; subst h₂
  intro h
  have := congrArg (fun S => (r₁, t₁, x) ∈ S) (h ∅)
  simp [update, Finset.mem_filter] at this

/-- `rc` is empty on every pair except `remove x` against `add x`. -/
theorem rcOps_iff (o₁ o₂ : AppOp α) :
    (rcOps o₁ o₂ = OrderResult.Fst_then_snd ∨ rcOps o₂ o₁ = OrderResult.Fst_then_snd)
      ↔ (∃ x, (o₁ = .add x ∧ o₂ = .remove x) ∨ (o₁ = .remove x ∧ o₂ = .add x)) := by
  cases o₁ <;> cases o₂ <;>
    simp [rcOps, eq_comm] <;> aesop

/-- **RC-NON-COMM, over concurrent events.** The same-replica pair that
breaks the unguarded law is excluded by `hr`; every pair still in scope is
covered exactly. -/
theorem rc_non_comm (e₁ e₂ : (I α).Event)
    (_ht : (I α).time e₁ ≠ (I α).time e₂) (hr : (I α).rep e₁ ≠ (I α).rep e₂) :
    ¬ (I α).Commutes e₁ e₂ ↔ (I α).EventRcBefore e₁ e₂ ∨ (I α).EventRcBefore e₂ e₁ := by
  obtain ⟨t₁, r₁, o₁⟩ := e₁
  obtain ⟨t₂, r₂, o₂⟩ := e₂
  cases o₁ with
  | add x =>
    cases o₂ with
    | add y =>
      have hc := commutes_add_add (e₁ := ((t₁, r₁, AppOp.add x) : (I α).Event))
          (e₂ := ((t₂, r₂, AppOp.add y) : (I α).Event)) (x := x) (y := y) rfl rfl hr
      simp [Impl.EventRcBefore, Impl.RcBefore, I, rcOps, Op.op, hc]
    | remove y =>
      by_cases hxy : x = y
      · subst hxy
        have hn := not_commutes_add_rem (e₁ := ((t₁, r₁, AppOp.add x) : (I α).Event))
          (e₂ := ((t₂, r₂, AppOp.remove x) : (I α).Event)) (x := x) rfl rfl
        simp [Impl.EventRcBefore, Impl.RcBefore, I, rcOps, Op.op, hn]
      · have hc := commutes_add_rem (e₁ := ((t₁, r₁, AppOp.add x) : (I α).Event))
          (e₂ := ((t₂, r₂, AppOp.remove y) : (I α).Event)) (x := x) (y := y) rfl rfl hxy
        simp [Impl.EventRcBefore, Impl.RcBefore, I, rcOps, Op.op, hc, hxy]
        exact fun h => hxy h.symm
  | remove x =>
    cases o₂ with
    | add y =>
      by_cases hxy : y = x
      · subst hxy
        have hn := not_commutes_add_rem
          (e₁ := ((t₂, r₂, AppOp.add y) : (I α).Event))
          (e₂ := ((t₁, r₁, AppOp.remove y) : (I α).Event)) (x := y) rfl rfl
        have hn' : ¬ (I α).Commutes (t₁, r₁, AppOp.remove y) (t₂, r₂, AppOp.add y) :=
          fun h => hn (fun s => (h s).symm)
        simp [Impl.EventRcBefore, Impl.RcBefore, I, rcOps, Op.op, hn']
      · have hc := commutes_add_rem
          (e₁ := ((t₂, r₂, AppOp.add y) : (I α).Event))
          (e₂ := ((t₁, r₁, AppOp.remove x) : (I α).Event)) (x := y) (y := x) rfl rfl hxy
        have hc' : (I α).Commutes (t₁, r₁, AppOp.remove x) (t₂, r₂, AppOp.add y) :=
          fun s => (hc s).symm
        simp only [Impl.EventRcBefore, Impl.RcBefore, I, rcOps, Op.op]
        simp [hc', hxy]
        exact fun h => hxy h.symm
    | remove y =>
      have hc := commutes_rem_rem (e₁ := ((t₁, r₁, AppOp.remove x) : (I α).Event))
          (e₂ := ((t₂, r₂, AppOp.remove y) : (I α).Event)) (x := x) (y := y) rfl rfl
      simp [Impl.EventRcBefore, Impl.RcBefore, I, rcOps, Op.op, hc]

/-- **NO-RC-CHAIN.** Every edge runs `remove x --rc--> add x`, and an `add`
has no outgoing edge, so two edges cannot meet. -/
theorem no_rc_chain (o₁ o₂ o₃ : (itype α).OType) :
    ¬ ((I α).RcBefore o₁ o₂ ∧ (I α).RcBefore o₂ o₃) := by
  rintro ⟨h₁, h₂⟩
  cases o₁ <;> cases o₂ <;> cases o₃ <;>
    simp [Impl.RcBefore, rcOps] at h₁ h₂ <;> aesop

/-! ## COND-COMM

`rc` has only one shape of edge, `remove x --rc--> add x`, so in COND-COMM
`e` is a remove and `e'` the matching add. Swapping them changes the state
by exactly the one record `e'` contributes, and the absorber `e''` is
whatever fails to commute with that add: another `remove x`, or an `add x`
from the issuer's own replica. Both wipe that record, so the two orders
agree once `e''` has run.

`EqOff` is the invariant that makes this precise: agreement outside one
replica's records for one element. -/

/-- Two states agree outside the records of replica `r` for element `x`. -/
def EqOff (r : Replica) (x : α) (a b : State α) : Prop :=
  ∀ p : Record α, ¬ (p.1 = r ∧ p.2.2 = x) → (p ∈ a ↔ p ∈ b)

theorem eqOff_update {r : Replica} {x : α} {a b : State α} (h : EqOff r x a b)
    (e : (I α).Event) : EqOff r x (update a e) (update b e) := by
  intro p hp
  rcases p with ⟨pr, pt, pz⟩
  rcases e with ⟨t, er, o⟩
  cases o <;>
    simp [update, Finset.mem_insert, Finset.mem_filter, Prod.ext_iff, h _ hp]

theorem eqOff_applyList {r : Replica} {x : α} :
    ∀ (pi : List ((I α).Event)) {a b : State α}, EqOff r x a b →
      EqOff r x ((I α).applyList a pi) ((I α).applyList b pi)
  | [], _, _, h => h
  | e :: rest, _, _, h => eqOff_applyList rest (eqOff_update h e)

/-- An absorber that settles replica `r`'s records for `x` collapses the
difference `EqOff` allows. -/
theorem update_eq_of_eqOff {r : Replica} {x : α} {a b : State α}
    (h : EqOff r x a b) {e'' : (I α).Event}
    (hsettle : ∀ p : Record α, p.1 = r → p.2.2 = x →
      (p ∈ update a e'' ↔ p ∈ update b e'')) :
    update a e'' = update b e'' := by
  ext p
  by_cases hp : p.1 = r ∧ p.2.2 = x
  · exact hsettle p hp.1 hp.2
  · rcases p with ⟨pr, pt, pz⟩
    rcases e'' with ⟨t, er, o⟩
    cases o <;>
      simp [update, Finset.mem_insert, Finset.mem_filter, Prod.ext_iff, h _ hp]

/-- Adds of **different elements** commute, whatever their replicas: the two
filters are keyed on disjoint (replica, element) pairs. -/
theorem commutes_add_add_ne {e₁ e₂ : (I α).Event} {x y : α}
    (h₁ : e₁.2.2 = AppOp.add x) (h₂ : e₂.2.2 = AppOp.add y) (hxy : x ≠ y) :
    (I α).Commutes e₁ e₂ := by
  rcases e₁ with ⟨t₁, r₁, o₁⟩
  rcases e₂ with ⟨t₂, r₂, o₂⟩
  simp only at h₁ h₂
  subst h₁; subst h₂
  intro s
  ext p
  rcases p with ⟨r, t, z⟩
  simp [update, Finset.mem_insert, Finset.mem_filter, Prod.ext_iff]
  aesop

/-- **What can fail to commute with an `add x`.** Only a `remove x`, or an
`add x` issued by the same replica. This is the classification COND-COMM
needs, and the same-replica case is the one no `rc` edge can describe. -/
theorem absorber_shape {e' e'' : (I α).Event} {x : α} {r : Replica}
    (h' : e'.2.2 = AppOp.add x) (hr : e'.2.1 = r)
    (hn : ¬ (I α).Commutes e' e'') :
    e''.2.2 = AppOp.remove x ∨ (e''.2.2 = AppOp.add x ∧ e''.2.1 = r) := by
  rcases e'' with ⟨t'', r'', o''⟩
  cases o'' with
  | add y =>
    by_cases hxy : x = y
    · subst hxy
      by_cases hrr : r'' = r
      · exact Or.inr ⟨rfl, hrr⟩
      · exact absurd (commutes_add_add h' rfl (by
          simp only [Impl.rep, Op.rep, hr]; exact fun h => hrr h.symm)) hn
    · exact absurd (commutes_add_add_ne h' rfl hxy) hn
  | remove y =>
    by_cases hxy : x = y
    · exact Or.inl (by rw [hxy])
    · exact absurd (commutes_add_rem h' rfl hxy) hn

/-- Swapping a `remove x` past the matching `add x` changes the state by
exactly the one record the add contributes. -/
theorem eqOff_swap {sigma : State α} {e e' : (I α).Event} {x : α} {r : Replica}
    (he : e.2.2 = AppOp.remove x) (he' : e'.2.2 = AppOp.add x) (hr : e'.2.1 = r) :
    EqOff r x (update (update sigma e') e) (update (update sigma e) e') := by
  intro p hp
  rcases p with ⟨pr, pt, pz⟩
  rcases e with ⟨t, er, o⟩
  rcases e' with ⟨t', er', o'⟩
  simp only at he he' hr
  subst he; subst he'; subst hr
  simp [update, Finset.mem_insert, Finset.mem_filter, Prod.ext_iff] at hp ⊢
  aesop

/-- **COND-COMM.** Once the absorber has run, the record that the swap moved
is settled identically on both sides. -/
theorem cond_comm (sigma : (I α).Sigma) (e e' e'' : (I α).Event)
    (pi : List ((I α).Event))
    (hrc : (I α).EventRcBefore e e') (hn : ¬ (I α).Commutes e' e'') :
    (I α).do_ ((I α).applyList ((I α).do_ ((I α).do_ sigma e') e) pi) e''
      = (I α).do_ ((I α).applyList ((I α).do_ ((I α).do_ sigma e) e') pi) e'' := by
  obtain ⟨x, hex, he'x⟩ : ∃ x, e.2.2 = AppOp.remove x ∧ e'.2.2 = AppOp.add x := by
    rcases e with ⟨t, r, o⟩
    rcases e' with ⟨t', r', o'⟩
    cases o with
    | add a =>
      cases o' with
      | add b =>
        simp only [Impl.EventRcBefore, Impl.RcBefore, I, rcOps, Op.op] at hrc
        exact absurd hrc (by simp)
      | remove b =>
        simp only [Impl.EventRcBefore, Impl.RcBefore, I, rcOps, Op.op] at hrc
        split_ifs at hrc
    | remove a =>
      cases o' with
      | add b =>
        simp only [Impl.EventRcBefore, Impl.RcBefore, I, rcOps, Op.op] at hrc
        split_ifs at hrc with hab
        · exact ⟨a, rfl, by simp [hab]⟩
      | remove b =>
        simp only [Impl.EventRcBefore, Impl.RcBefore, I, rcOps, Op.op] at hrc
        exact absurd hrc (by simp)
  have hswap := eqOff_swap (sigma := sigma) (r := e'.2.1) hex he'x rfl
  refine update_eq_of_eqOff (eqOff_applyList pi hswap) ?_
  intro p hp1 hp2
  rcases absorber_shape (r := e'.2.1) he'x rfl hn with h | ⟨h, hrr⟩
  · rcases p with ⟨pr, pt, pz⟩
    rcases e'' with ⟨t'', r'', o''⟩
    simp only at h
    subst h
    simp only at hp2
    simp [update, Finset.mem_filter, hp2]
  · rcases p with ⟨pr, pt, pz⟩
    rcases e'' with ⟨t'', r'', o''⟩
    simp only at h hrr
    subst h
    simp only at hp1 hp2
    subst hp1; subst hp2
    simp [update, Finset.mem_insert, Finset.mem_filter, Prod.ext_iff, hrr]

/-- **`Laws(D_type)` for the efficient OR-set.**

The row that motivated the guard satisfies the guarded law. What it still
cannot supply is `PayloadDetermined`: two `add x` operations commute across
replicas and fail to commute within one, so commutation is not a function of
the payloads. `Soundness/` needs that to reach the vendored uniform
contract, which is why the certificate in `Certificate.lean` takes the
representation route instead and needs no replay contract at all. -/
theorem laws : Laws (I α) :=
  ⟨rcNonComm_of_exact no_rc_chain rc_non_comm, no_rc_chain,
  fun sigma e e' e'' pi _ _ => cond_comm sigma e e' e'' pi⟩

end LeanProofs.Implementations.EfficientORSet
