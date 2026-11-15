import LeanProofs.Implementations.ORSet.Definition
import LeanProofs.Interface.Laws

/-!
# The OR-set: discharging `Laws(D_type)`

The first row here with a nonempty `rc`, so the three conditions of Section 4
have real content. They are proved from one observation: `add x` and
`remove x` disagree only about records whose element is `x`, and every other
pair of operations commutes outright.

The canonical join laws of Section 5 are **not** available in their
arbitrary-state form, so the join lemma is proved directly in
`LinearExtension.lean`, which is the other route Section 5 allows.
-/

namespace LeanProofs.Implementations.ORSet

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

variable {A : Type} [DecidableEq A]

/-- `rc` relates exactly the pairs `remove x`, `add x`. -/
@[simp] theorem rcBefore_iff (o₁ o₂ : Act A) :
    (D A).RcBefore o₁ o₂ ↔ ∃ x, o₁ = .remove x ∧ o₂ = .add x := by
  cases o₁ with
  | add x =>
      cases o₂ with
      | add y => simp [Impl.RcBefore, rc]
      | remove y => simp only [Impl.RcBefore, rc]; split <;> simp
  | remove x =>
      cases o₂ with
      | add y =>
          simp only [Impl.RcBefore, rc]
          by_cases h : x = y
          · subst h; simp
          · simp [h, Ne.symm h]
      | remove y => simp [Impl.RcBefore, rc]

/-- The event-level reading of the same fact. -/
theorem eventRcBefore_iff (e₁ e₂ : (D A).Event) :
    (D A).EventRcBefore e₁ e₂ ↔ ∃ x, e₁.op = .remove x ∧ e₂.op = .add x :=
  rcBefore_iff _ _

@[simp] theorem mem_step (S : St A) (e : Op (Act A)) (p : A × Timestamp) :
    p ∈ step S e ↔ match e.op with
    | .add x => p = (x, e.time) ∨ p ∈ S
    | .remove x => p ∈ S ∧ p.1 ≠ x := by
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
    · obtain ⟨x, ha, hb⟩ := (eventRcBefore_iff _ _).mp hr
      have h := Finset.ext_iff.mp (hc (∅ : St A)) (x, e₂.time)
      simp [step, ha, hb] at h
    · obtain ⟨x, hb, ha⟩ := (eventRcBefore_iff _ _).mp hr
      have h := Finset.ext_iff.mp (hc (∅ : St A)) (x, e₁.time)
      simp [step, ha, hb] at h

/-- **NO-RC-CHAIN**. A `remove` can only start an edge and an `add` can only
end one, so two edges never meet. -/
theorem no_rc_chain (o₁ o₂ o₃ : Act A) :
    ¬ ((D A).RcBefore o₁ o₂ ∧ (D A).RcBefore o₂ o₃) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨x, -, hb⟩ := (rcBefore_iff _ _).mp h₁
  obtain ⟨y, hb', -⟩ := (rcBefore_iff _ _).mp h₂
  rw [hb] at hb'; cases hb'

/-! ### The absorber argument for COND-COMM

Swapping `remove x` with a concurrent `add x` changes the state only in the
records whose element is `x`. The absorber of the pair is another `remove x`,
and it erases exactly those records, so the two orders agree after it. -/

/-- Two states that agree away from `x`. -/
def EqExcept (x : A) (a b : St A) : Prop := ∀ p, p.1 ≠ x → (p ∈ a ↔ p ∈ b)

theorem eqExcept_step {x : A} {a b : St A} (h : EqExcept x a b) (e : Op (Act A)) :
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
  have habs : e''.op = Act.remove x := by
    rcases (noncomm_iff e' e'').mp hnc with h | h
    · obtain ⟨y, ha, -⟩ := (eventRcBefore_iff _ _).mp h
      rw [he'] at ha; cases ha
    · obtain ⟨y, hr, ha⟩ := (eventRcBefore_iff _ _).mp h
      rw [he'] at ha; injection ha with hxy; subst y; exact hr
  have hbase : EqExcept x (step (step S e') e) (step (step S e) e') := by
    intro p hp; simp [step, he, he', hp]
  have hfold := eqExcept_applyList hbase pi
  change step _ e'' = step _ e''
  ext p
  simp only [step, habs, Finset.mem_filter]
  by_cases hp : p.1 = x
  · simp [hp]
  · exact and_congr (hfold p hp) Iff.rfl

/-- `Laws(D_type)`: RC-NON-COMM, NO-RC-CHAIN and COND-COMM. -/
theorem laws : Laws (D A) := ⟨noncomm_iff, no_rc_chain, cond_comm⟩

end LeanProofs.Implementations.ORSet
