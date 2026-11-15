import LeanProofs.Implementations.EnableWinsFlag.Definition
import LeanProofs.Interface.Laws

/-!
# The flag core: discharging `Laws(D_type)`

Two `winning` events commute: they add to their issuers' counters and set a
bit to the same value. Two `reset` events commute: a reset reads nothing it
changes. A `winning` and a `reset` do not commute, and `rc` orders them.

COND-COMM is the absorber argument again. Swapping a `reset` past a
concurrent `winning` leaves every counter alone and changes only one bit, and
the absorber of such a pair is another `reset`, which rebuilds every bit from
the counters.

The canonical join laws are not available at arbitrary states, so the join
lemma is proved directly in `LinearExtension.lean`.
-/

namespace LeanProofs.Implementations.EnableWinsFlag

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

/-! ### Unfolding `do` -/

theorem step_winning (s : St) (e : Op Act) (h : e.op = .winning) :
    step s e = fun r => if r = e.rep then ((s r).1 + 1, true) else s r := by
  simp only [step, h]

theorem step_reset (s : St) (e : Op Act) (h : e.op = .reset) :
    step s e = fun r => ((s r).1, false) := by
  simp only [step, h]

/-! ### `rc` -/

/-- `rc` relates exactly the pair `reset`, `winning`. -/
@[simp] theorem rcBefore_iff (o₁ o₂ : Act) :
    D.RcBefore o₁ o₂ ↔ o₁ = .reset ∧ o₂ = .winning := by
  cases o₁ <;> cases o₂ <;> simp [Impl.RcBefore, rc]

/-- The event-level reading. -/
theorem eventRcBefore_iff (e₁ e₂ : D.Event) :
    D.EventRcBefore e₁ e₂ ↔
      e₁.op = .reset ∧ e₂.op = .winning :=
  rcBefore_iff _ _

/-! ### Commutation -/

theorem commutes_symm {e₁ e₂ : D.Event}
    (h : D.Commutes e₁ e₂) :
    D.Commutes e₂ e₁ := fun s => (h s).symm

/-- Equal requests commute, whatever their issuers. Two `winning` events add
to their own rows and agree on the bit; two `reset` events agree outright. -/
theorem commutes_of_same_op (e₁ e₂ : D.Event)
    (h : e₁.op = e₂.op) : D.Commutes e₁ e₂ := by
  intro s
  change step (step s e₁) e₂ = step (step s e₂) e₁
  cases h₁ : e₁.op with
  | winning =>
      have h₂ : e₂.op = Act.winning := h.symm.trans h₁
      simp only [step, h₁, h₂]
      funext r
      by_cases hp : r = e₁.rep
      · by_cases hq : r = e₂.rep
        · have hpq : e₁.rep = e₂.rep := hp ▸ hq
          simp [hp, hq, hpq]
        · have hne : ¬ (e₁.rep = e₂.rep) := hp ▸ hq
          simp [hp, hq, hne]
      · by_cases hq : r = e₂.rep
        · have hne : ¬ (e₂.rep = e₁.rep) := hq ▸ hp
          simp [hp, hq, hne]
        · simp [hp, hq]
  | reset =>
      have h₂ : e₂.op = Act.reset := h.symm.trans h₁
      simp only [step, h₁, h₂]

/-- A `reset` and a `winning` do not commute: performed in one order the
issuer's bit ends up set, in the other it ends up clear. -/
theorem not_commutes_reset_winning (e₁ e₂ : D.Event)
    (h₁ : e₁.op = .reset) (h₂ : e₂.op = .winning) :
    ¬ D.Commutes e₁ e₂ := by
  intro hc
  have h := congrFun (hc (fun _ => (0, false))) e₂.rep
  simp only [step, h₁, h₂] at h
  simp at h

/-- **RC-NON-COMM**. -/
theorem noncomm_iff (e₁ e₂ : D.Event) :
    ¬ D.Commutes e₁ e₂ ↔
      D.EventRcBefore e₁ e₂
        ∨ D.EventRcBefore e₂ e₁ := by
  simp only [eventRcBefore_iff]
  cases h₁ : e₁.op with
  | winning =>
      cases h₂ : e₂.op with
      | winning => simp [commutes_of_same_op e₁ e₂ (h₁.trans h₂.symm)]
      | reset =>
          have hn : ¬ D.Commutes e₁ e₂ := fun hc =>
            not_commutes_reset_winning e₂ e₁ h₂ h₁ (commutes_symm hc)
          simp [hn, h₁, h₂]
  | reset =>
      cases h₂ : e₂.op with
      | winning => simp [not_commutes_reset_winning e₁ e₂ h₁ h₂, h₁, h₂]
      | reset => simp [commutes_of_same_op e₁ e₂ (h₁.trans h₂.symm)]

/-- **NO-RC-CHAIN**. A `reset` can only start an edge and a `winning` can only
end one, so two edges never meet. -/
theorem no_rc_chain (o₁ o₂ o₃ : Act) :
    ¬ (D.RcBefore o₁ o₂ ∧ D.RcBefore o₂ o₃) := by
  cases o₂ <;> simp

/-! ### The absorber argument for COND-COMM -/

/-- Two states with the same counters everywhere. Bits may differ. -/
def EqCounters (a b : St) : Prop := ∀ r, (a r).1 = (b r).1

theorem eqCounters_step {a b : St} (h : EqCounters a b) (e : Op Act) :
    EqCounters (step a e) (step b e) := by
  intro r
  cases he : e.op with
  | winning =>
      simp only [step, he]
      by_cases hr : r = e.rep
      · simp [hr, h e.rep]
      · simp [hr, h r]
  | reset =>
      simp only [step, he]
      exact h r

theorem eqCounters_foldl {a b : St} (h : EqCounters a b) (pi : List (Op Act)) :
    EqCounters (pi.foldl step a) (pi.foldl step b) := by
  induction pi generalizing a b with
  | nil => exact h
  | cons e pi ih => exact ih (eqCounters_step h e)

/-- A `reset` rebuilds every bit from the counters, so it maps states with
equal counters to the same state. -/
theorem reset_eq_of_eqCounters {a b : St} (h : EqCounters a b) {e : Op Act}
    (he : e.op = .reset) : step a e = step b e := by
  simp only [step, he]
  funext r
  rw [h r]

/-- **COND-COMM**. -/
theorem cond_comm (S : D.Sigma)
    (e e' e'' : D.Event) (pi : List D.Event)
    (hrc : D.EventRcBefore e e')
    (hnc : ¬ D.Commutes e' e'') :
    D.do_ (D.applyList
        (D.do_ (D.do_ S e') e) pi) e''
      = D.do_ (D.applyList
          (D.do_ (D.do_ S e) e') pi) e'' := by
  obtain ⟨he, he'⟩ := (eventRcBefore_iff e e').mp hrc
  have habs : e''.op = Act.reset := by
    rcases (noncomm_iff e' e'').mp hnc with h | h
    · exact absurd (((eventRcBefore_iff _ _).mp h).1.symm.trans he') (by simp)
    · exact ((eventRcBefore_iff _ _).mp h).1
  have hbase : EqCounters (step (step S e') e) (step (step S e) e') := by
    intro r
    simp only [step, he, he']
    by_cases hr : r = e'.rep <;> simp [hr]
  exact reset_eq_of_eqCounters (eqCounters_foldl hbase pi) habs

/-- `Laws(D_type)`: RC-NON-COMM, NO-RC-CHAIN and COND-COMM. -/
theorem laws : Laws D := ⟨noncomm_iff, no_rc_chain, cond_comm⟩

end LeanProofs.Implementations.EnableWinsFlag
