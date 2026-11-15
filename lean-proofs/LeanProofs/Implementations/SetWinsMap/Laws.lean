import LeanProofs.Implementations.SetWinsMap.Definition
import LeanProofs.Interface.Laws

/-!
# The set-wins multimap: discharging `Laws(D_type)`

The same shape of argument as the OR-set, now indexed by keys rather than by
elements. Two operations interfere only when they name the same key, and the
only interfering pair is `del k` against `set k v`.

As for the OR-set, the arbitrary-state canonical join laws fail on this
merge, so the join lemma is proved directly in `LinearExtension.lean`.
-/

namespace LeanProofs.Implementations.SetWinsMap

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-- `rc` relates exactly the pairs `del k`, `set k v`. -/
@[simp] theorem rcBefore_iff (o₁ o₂ : AppOp K V) :
    (D K V).RcBefore o₁ o₂ ↔ ∃ k v, o₁ = .del k ∧ o₂ = .set k v := by
  cases o₁ with
  | set k w =>
      cases o₂ with
      | set j u => simp [Impl.RcBefore, rc]
      | del j => simp only [Impl.RcBefore, rc]; split <;> simp
  | del k =>
      cases o₂ with
      | set j u =>
          simp only [Impl.RcBefore, rc]
          by_cases h : k = j
          · subst h; simp
          · simp [h, Ne.symm h]
      | del j => simp [Impl.RcBefore, rc]

/-- The event-level reading of the same fact. -/
theorem eventRcBefore_iff (e₁ e₂ : (D K V).Event) :
    (D K V).EventRcBefore e₁ e₂ ↔ ∃ k v, e₁.op = .del k ∧ e₂.op = .set k v :=
  rcBefore_iff _ _

@[simp] theorem mem_step (S : St K V) (e : Event K V) (p : (K × V) × Timestamp) :
    p ∈ step S e ↔ match e.op with
    | .set k v => p = ((k, v), e.time) ∨ p ∈ S
    | .del k => p ∈ S ∧ p.1.1 ≠ k := by
  rcases e with ⟨t, r, o⟩; cases o <;> simp [step, Op.op, Op.time]

/-- Everything `rc` leaves unordered really does commute. -/
theorem commute_of_no_rc (e₁ e₂ : (D K V).Event)
    (h : ¬ ((D K V).EventRcBefore e₁ e₂ ∨ (D K V).EventRcBefore e₂ e₁)) :
    (D K V).Commutes e₁ e₂ := by
  simp only [eventRcBefore_iff, not_or] at h
  intro S
  change St K V at S
  rcases e₁ with ⟨t₁, r₁, o₁⟩; rcases e₂ with ⟨t₂, r₂, o₂⟩
  change step (step S _) _ = step (step S _) _
  cases o₁ <;> cases o₂ <;> ext p <;> simp [step, Op.op, Op.time] at h ⊢ <;> grind

/-- **RC-NON-COMM**. -/
theorem noncomm_iff (e₁ e₂ : (D K V).Event) :
    ¬ (D K V).Commutes e₁ e₂ ↔
      (D K V).EventRcBefore e₁ e₂ ∨ (D K V).EventRcBefore e₂ e₁ := by
  constructor
  · exact fun hn => Classical.byContradiction fun h => hn (commute_of_no_rc e₁ e₂ h)
  · intro hr hc
    rcases hr with hr | hr
    · obtain ⟨k, v, hd, hs⟩ := (eventRcBefore_iff _ _).mp hr
      have h := Finset.ext_iff.mp (hc (∅ : St K V)) ((k, v), e₂.time)
      simp [step, hd, hs] at h
    · obtain ⟨k, v, hd, hs⟩ := (eventRcBefore_iff _ _).mp hr
      have h := Finset.ext_iff.mp (hc (∅ : St K V)) ((k, v), e₁.time)
      simp [step, hd, hs] at h

/-- **NO-RC-CHAIN**. A `del` can only start an edge and a `set` can only end
one, so two edges never meet. -/
theorem no_rc_chain (o₁ o₂ o₃ : AppOp K V) :
    ¬ ((D K V).RcBefore o₁ o₂ ∧ (D K V).RcBefore o₂ o₃) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨k, v, -, hs⟩ := (rcBefore_iff _ _).mp h₁
  obtain ⟨j, -, hd, -⟩ := (rcBefore_iff _ _).mp h₂
  rw [hs] at hd; cases hd

/-! ### The absorber argument for COND-COMM

Swapping `del k` with a concurrent `set k v` changes the state only in the
bindings for `k`. The absorber is another `del k`, which erases exactly those
bindings, so the two orders agree after it. -/

/-- Two states that agree away from key `k`. -/
def EqExcept (k : K) (a b : St K V) : Prop := ∀ p, p.1.1 ≠ k → (p ∈ a ↔ p ∈ b)

theorem eqExcept_step {k : K} {a b : St K V} (h : EqExcept k a b) (e : Event K V) :
    EqExcept k (step a e) (step b e) := by
  intro p hp
  rcases e with ⟨t, r, o⟩; cases o <;> simp [step, Op.op, h p hp]

theorem eqExcept_applyList {k : K} {a b : St K V} (h : EqExcept k a b)
    (pi : List (D K V).Event) :
    EqExcept k ((D K V).applyList a pi) ((D K V).applyList b pi) := by
  induction pi generalizing a b with
  | nil => exact h
  | cons e pi ih => exact ih (eqExcept_step h e)

/-- **COND-COMM**. -/
theorem cond_comm (S : (D K V).Sigma) (e e' e'' : (D K V).Event)
    (pi : List (D K V).Event)
    (hrc : (D K V).EventRcBefore e e') (hnc : ¬ (D K V).Commutes e' e'') :
    (D K V).do_ ((D K V).applyList ((D K V).do_ ((D K V).do_ S e') e) pi) e''
      = (D K V).do_ ((D K V).applyList ((D K V).do_ ((D K V).do_ S e) e') pi) e'' := by
  obtain ⟨k, v, he, he'⟩ := (eventRcBefore_iff _ _).mp hrc
  have habs : e''.op = AppOp.del k := by
    rcases (noncomm_iff e' e'').mp hnc with h | h
    · obtain ⟨j, w, hd, -⟩ := (eventRcBefore_iff _ _).mp h
      rw [he'] at hd; cases hd
    · obtain ⟨j, w, hd, hs⟩ := (eventRcBefore_iff _ _).mp h
      rw [he'] at hs; injection hs with hkj _; subst j; exact hd
  have hbase : EqExcept k (step (step S e') e) (step (step S e) e') := by
    intro p hp; simp [step, he, he', hp]
  have hfold := eqExcept_applyList hbase pi
  change step _ e'' = step _ e''
  ext p
  simp only [step, habs, Finset.mem_filter]
  by_cases hp : p.1.1 = k
  · simp [hp]
  · exact and_congr (hfold p hp) Iff.rfl

/-- Non-commutation here is a function of the payloads alone, which is what
lets the guarded RC-NON-COMM be lifted to the uniform contract `Soundness`
still runs on. -/
theorem payloadDetermined : PayloadDetermined (D K V) := by
  intro e₁ e₂ f₁ f₂ h₁ h₂
  have key : ¬ (D K V).Commutes e₁ e₂ ↔ ¬ (D K V).Commutes f₁ f₂ := by
    rw [noncomm_iff, noncomm_iff, Impl.EventRcBefore, Impl.EventRcBefore,
      Impl.EventRcBefore, Impl.EventRcBefore, h₁, h₂]
  exact not_iff_not.mp key

/-- `Laws(D_type)`: RC-NON-COMM over concurrent events, NO-RC-CHAIN and
COND-COMM. -/
theorem laws : Laws (D K V) := ⟨fun e₁ e₂ _ _ => noncomm_iff e₁ e₂, no_rc_chain, cond_comm⟩

end LeanProofs.Implementations.SetWinsMap
