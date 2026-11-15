import LeanProofs.Implementations.RemoveWinsSet.Definition
import LeanProofs.Interface.Laws

/-!
# The remove-wins set: discharging `Laws(D_type)`

The OR-set argument with the two operations exchanged. Two operations
interfere only when they name the same element, and the only interfering pair
is `add x` against `remove x`.

As for the OR-set, `merge` reads as intersection where the ancestor holds a
tag and as union where it does not, so the arbitrary-state VC3 fails and the
join lemma is proved directly in `LinearExtension.lean`.
-/

namespace LeanProofs.Implementations.RemoveWinsSet

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

variable {A : Type} [DecidableEq A] [Fintype A]

/-- `rc` relates exactly the pairs `add x`, `remove x`. -/
@[simp] theorem rcBefore_iff (o₁ o₂ : AppOp A) :
    (D A).RcBefore o₁ o₂ ↔ ∃ x, o₁ = .add x ∧ o₂ = .remove x := by
  cases o₁ with
  | remove x =>
      cases o₂ with
      | remove y => simp [Impl.RcBefore, rc]
      | add y => simp only [Impl.RcBefore, rc]; split <;> simp
  | add x =>
      cases o₂ with
      | remove y =>
          simp only [Impl.RcBefore, rc]
          by_cases h : x = y
          · subst h; simp
          · simp [h, Ne.symm h]
      | add y => simp [Impl.RcBefore, rc]

/-- The event-level reading of the same fact. -/
theorem eventRcBefore_iff (e₁ e₂ : (D A).Event) :
    (D A).EventRcBefore e₁ e₂ ↔ ∃ x, e₁.op = .add x ∧ e₂.op = .remove x :=
  rcBefore_iff _ _

@[simp] theorem mem_step (S : St A) (e : Event A) (p : A × Timestamp) :
    p ∈ step S e ↔ match e.op with
    | .remove x => p = (x, e.time) ∨ p ∈ S
    | .add x => p ∈ S ∧ p.1 ≠ x := by
  rcases e with ⟨t, r, o⟩; cases o <;> simp [step, Op.op, Op.time]

/-- Everything `rc` leaves unordered really does commute. -/
theorem commute_of_no_rc (e₁ e₂ : (D A).Event)
    (h : ¬ ((D A).EventRcBefore e₁ e₂ ∨ (D A).EventRcBefore e₂ e₁)) :
    (D A).Commutes e₁ e₂ := by
  simp only [eventRcBefore_iff, not_or] at h
  intro S
  change St A at S
  rcases e₁ with ⟨t₁, r₁, o₁⟩; rcases e₂ with ⟨t₂, r₂, o₂⟩
  change step (step S _) _ = step (step S _) _
  cases o₁ <;> cases o₂ <;> ext p <;> simp [step, Op.op, Op.time] at h ⊢ <;> grind

/-- **RC-NON-COMM**. -/
theorem noncomm_iff (e₁ e₂ : (D A).Event) :
    ¬ (D A).Commutes e₁ e₂ ↔
      (D A).EventRcBefore e₁ e₂ ∨ (D A).EventRcBefore e₂ e₁ := by
  constructor
  · exact fun hn => Classical.byContradiction fun h => hn (commute_of_no_rc e₁ e₂ h)
  · intro hr hc
    rcases hr with hr | hr
    · obtain ⟨x, ha, hr'⟩ := (eventRcBefore_iff _ _).mp hr
      have h := Finset.ext_iff.mp (hc (∅ : St A)) (x, e₂.time)
      simp [step, ha, hr'] at h
    · obtain ⟨x, ha, hr'⟩ := (eventRcBefore_iff _ _).mp hr
      have h := Finset.ext_iff.mp (hc (∅ : St A)) (x, e₁.time)
      simp [step, ha, hr'] at h

/-- **NO-RC-CHAIN**. An `add` can only start an edge and a `remove` can only
end one, so two edges never meet. -/
theorem no_rc_chain (o₁ o₂ o₃ : AppOp A) :
    ¬ ((D A).RcBefore o₁ o₂ ∧ (D A).RcBefore o₂ o₃) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨x, -, hr⟩ := (rcBefore_iff _ _).mp h₁
  obtain ⟨y, ha, -⟩ := (rcBefore_iff _ _).mp h₂
  rw [hr] at ha; cases ha

/-! ### The absorber argument for COND-COMM -/

/-- Two states that agree away from `x`. -/
def EqExcept (x : A) (a b : St A) : Prop := ∀ p, p.1 ≠ x → (p ∈ a ↔ p ∈ b)

theorem eqExcept_step {x : A} {a b : St A} (h : EqExcept x a b) (e : Event A) :
    EqExcept x (step a e) (step b e) := by
  intro p hp
  rcases e with ⟨t, r, o⟩; cases o <;> simp [step, Op.op, h p hp]

theorem eqExcept_applyList {x : A} {a b : St A} (h : EqExcept x a b)
    (pi : List (D A).Event) :
    EqExcept x ((D A).applyList a pi) ((D A).applyList b pi) := by
  induction pi generalizing a b with
  | nil => exact h
  | cons e pi ih => exact ih (eqExcept_step h e)

/-- **COND-COMM**. -/
theorem cond_comm (S : (D A).Sigma) (e e' e'' : (D A).Event)
    (pi : List (D A).Event)
    (hrc : (D A).EventRcBefore e e') (hnc : ¬ (D A).Commutes e' e'') :
    (D A).do_ ((D A).applyList ((D A).do_ ((D A).do_ S e') e) pi) e''
      = (D A).do_ ((D A).applyList ((D A).do_ ((D A).do_ S e) e') pi) e'' := by
  obtain ⟨x, he, he'⟩ := (eventRcBefore_iff _ _).mp hrc
  have habs : e''.op = AppOp.add x := by
    rcases (noncomm_iff e' e'').mp hnc with h | h
    · obtain ⟨y, ha, -⟩ := (eventRcBefore_iff _ _).mp h
      rw [he'] at ha; cases ha
    · obtain ⟨y, ha, hr⟩ := (eventRcBefore_iff _ _).mp h
      rw [he'] at hr; injection hr with hxy; subst y; exact ha
  have hbase : EqExcept x (step (step S e') e) (step (step S e) e') := by
    intro p hp; simp [step, he, he', hp]
  have hfold := eqExcept_applyList hbase pi
  change step _ e'' = step _ e''
  ext p
  simp only [step, habs, Finset.mem_filter]
  by_cases hp : p.1 = x
  · simp [hp]
  · exact and_congr (hfold p hp) Iff.rfl

/-- Non-commutation here is a function of the payloads alone, which is what
lets the guarded RC-NON-COMM be lifted to the uniform contract `Soundness`
still runs on. -/
theorem payloadDetermined : PayloadDetermined (D A) := by
  intro e₁ e₂ f₁ f₂ h₁ h₂
  have key : ¬ (D A).Commutes e₁ e₂ ↔ ¬ (D A).Commutes f₁ f₂ := by
    rw [noncomm_iff, noncomm_iff, Impl.EventRcBefore, Impl.EventRcBefore,
      Impl.EventRcBefore, Impl.EventRcBefore, h₁, h₂]
  exact not_iff_not.mp key

/-- `Laws(D_type)`: RC-NON-COMM over concurrent events, NO-RC-CHAIN and
COND-COMM. -/
theorem laws : Laws (D A) := ⟨fun e₁ e₂ _ _ => noncomm_iff e₁ e₂, no_rc_chain, cond_comm⟩

end LeanProofs.Implementations.RemoveWinsSet
