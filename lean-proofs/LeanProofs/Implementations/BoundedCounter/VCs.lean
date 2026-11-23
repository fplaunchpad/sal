import LeanProofs1.Implementations.BoundedCounter.Definition
import LeanProofs1.Metatheory.Adequacy

/-!
# The bounded counter: `Laws(D_type)`, VC1 and VC2

Every effector adds its amount to one cell, so every pair of events
commutes and `rc` is empty. `Laws(D_type)` is then immediate, VC1 is the
commutativity of `max`, and VC2 is `max 0 x = x`.

VC3, VC4 and VC5 are **not** here. `Negative.lean` shows VC4 is false.
-/

namespace LeanProofs1.Implementations.BoundedCounter

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

variable {n : Nat} {K : Int}

theorem do_eq (s : St) (e : (D n K).Event) : (D n K).do_ s e = step s e := rfl

theorem merge_eq (l a b : (D n K).Sigma) : (D n K).merge l a b = mergeState l a b := rfl

theorem sigma0_eq : (D n K).sigma0 = initial := rfl

/-! ## Every pair of events commutes -/

theorem bump_comm (f : Nat → Nat) (r₁ a₁ r₂ a₂ : Nat) :
    bump (bump f r₁ a₁) r₂ a₂ = bump (bump f r₂ a₂) r₁ a₁ := by
  funext k; simp only [bump]; omega

theorem bumpMatrix_comm (f : Nat → Nat → Nat) (r₁ c₁ a₁ r₂ c₂ a₂ : Nat) :
    bumpMatrix (bumpMatrix f r₁ c₁ a₁) r₂ c₂ a₂
      = bumpMatrix (bumpMatrix f r₂ c₂ a₂) r₁ c₁ a₁ := by
  funext i j; simp only [bumpMatrix]; omega

theorem all_commute (e₁ e₂ : (D n K).Event) : (D n K).Commutes e₁ e₂ := by
  intro s
  simp only [do_eq]
  rcases h₁ : e₁.op with a₁ | a₁ | ⟨a₁, j₁⟩ <;> rcases h₂ : e₂.op with a₂ | a₂ | ⟨a₂, j₂⟩ <;>
    simp only [step, h₁, h₂] <;>
    refine St.ext (fun i j => ?_) (fun i => ?_) <;>
    simp only [bumpMatrix, bump] <;> omega

/-! ## `Laws(D_type)` -/

theorem no_rc_edge (e₁ e₂ : (D n K).Event) : ¬ (D n K).EventRcBefore e₁ e₂ := by
  simp [Impl.EventRcBefore, Impl.RcBefore, D, rcOf]

theorem no_rc_chain (o₁ o₂ o₃ : type.OType) :
    ¬ ((D n K).RcBefore o₁ o₂ ∧ (D n K).RcBefore o₂ o₃) := by
  rintro ⟨h, -⟩
  simp [Impl.RcBefore, D, rcOf] at h

theorem rc_non_comm (e₁ e₂ : (D n K).Event)
    (_ht : (D n K).time e₁ ≠ (D n K).time e₂)
    (_hr : (D n K).rep e₁ ≠ (D n K).rep e₂) :
    ((¬ (D n K).Commutes e₁ e₂ ∧ e₁.op ≠ e₂.op) ↔
      (D n K).EventRcBefore e₁ e₂ ∨ (D n K).EventRcBefore e₂ e₁) := by
  constructor
  · exact fun h => absurd (all_commute e₁ e₂) h.1
  · rintro (h | h) <;> exact absurd h (no_rc_edge _ _)

theorem cond_comm (sigma : (D n K).Sigma) (e e' e'' : (D n K).Event)
    (pi : List (D n K).Event)
    (_ht : (D n K).time e ≠ (D n K).time e') (_hr : (D n K).rep e ≠ (D n K).rep e')
    (hrc : (D n K).EventRcBefore e e') (_hnc : ¬ (D n K).Commutes e' e'') :
    (D n K).do_ ((D n K).applyList ((D n K).do_ ((D n K).do_ sigma e') e) pi) e''
      = (D n K).do_ ((D n K).applyList ((D n K).do_ ((D n K).do_ sigma e) e') pi) e'' :=
  absurd hrc (no_rc_edge e e')

theorem laws : Laws (D n K) := ⟨rc_non_comm, no_rc_chain, cond_comm⟩

/-! ## VC1 and VC2 -/

theorem vc1_merge_comm (l a b : (D n K).Sigma) :
    (D n K).merge l a b = (D n K).merge l b a := by
  simp only [merge_eq, mergeState]
  exact St.ext (fun i j => Nat.max_comm _ _) (fun i => Nat.max_comm _ _)

theorem vc2_merge_init (s : (D n K).Sigma) :
    (D n K).merge (D n K).sigma0 (D n K).sigma0 s = s := by
  simp only [merge_eq, mergeState, sigma0_eq]
  exact St.ext (fun i j => by simp [initial]) (fun i => by simp [initial])

end LeanProofs1.Implementations.BoundedCounter
