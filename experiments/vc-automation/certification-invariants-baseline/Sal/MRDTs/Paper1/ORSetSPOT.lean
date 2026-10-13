import Sal.MRDTs.Paper1.ORSetVerified

/-! Concrete, hand-derived PASS+FAIL tests for the exact paper implementation.
The finite pair values are written literally, never obtained by evaluating the
implementation to manufacture expected answers. -/
namespace Sal.MRDTs.Paper1.ORSet.SPOT
open Sal.MRDTs.Foundation

abbrev Aₚ : Op (Update Nat) := (1, 0, .add 7)
abbrev Aᵩ : Op (Update Nat) := (2, 1, .add 7)
abbrev Rₚ : Op (Update Nat) := (3, 0, .remove 7)
abbrev Rᵩ : Op (Update Nat) := (4, 1, .remove 7)

def v₀ : State Nat := ∅
def v₁ := step v₀ Aₚ
def v₂ := step v₀ Aᵩ
def v₃ := merge v₀ v₁ v₂
def v₄ := step v₁ Rₚ
def v₅ := step v₂ Rᵩ
def v₆ := merge v₁ v₄ v₃
def v₇ := merge v₂ v₅ v₃
def v₈ := merge v₃ v₆ v₇

/-- Two additions at one replica retain both unique timestamps. -/
theorem retains_all_adds :
    step (step v₀ Aₚ) (2, 0, .add 7) = {(7, 1), (7, 2)} ∧
    step (step v₀ Aₚ) (2, 0, .add 7) ≠ {(7, 2)} := by decide

/-- A sequential remove erases every timestamp and cannot be a no-op. -/
theorem removes_all_adds :
    step (step (step v₀ Aₚ) (2, 0, .add 7)) Rₚ = ∅ ∧
    step (step (step v₀ Aₚ) (2, 0, .add 7)) Rₚ ≠ {(7, 1), (7, 2)} ∧
    query (step (step (step v₀ Aₚ) (2, 0, .add 7)) Rₚ) 7 = false := by decide

/-- Concurrent removal from an empty fork loses to a newly tagged add. -/
theorem concurrent_add_wins :
    merge v₀ (step v₀ Rᵩ) v₁ = {(7, 1)} ∧
    merge v₀ (step v₀ Rᵩ) v₁ ≠ ∅ ∧
    query (merge v₀ (step v₀ Rᵩ) v₁) 7 = true ∧
    query (merge v₀ (step v₀ Rᵩ) v₁) 8 = false := by decide

/-- The defeater's first branch retains exactly the other replica's add. -/
theorem defeater_left :
    v₆ = {(7, 2)} ∧ v₆ ≠ ∅ ∧ v₆ ≠ v₄ ∧ v₆ ≠ v₃ := by decide

/-- The mirror branch retains the first replica's add. -/
theorem defeater_right :
    v₇ = {(7, 1)} ∧ v₇ ≠ ∅ ∧ v₇ ≠ v₅ ∧ v₇ ≠ v₃ := by decide

/-- The true shared ancestor makes the final merge empty, unlike either
branch projection or their union. -/
theorem defeater_union :
    v₈ = ∅ ∧ v₈ ≠ v₆ ∧ v₈ ≠ v₇ ∧ v₈ ≠ v₆ ∪ v₇ ∧
    query v₈ 7 = false := by decide

/-- Ordinary set labels cannot reveal or depend on implementation tags. -/
theorem ordinary_set_sequences :
    ([Update.add 7, .add 7, .remove 7].foldl abstractStep (∅ : Finset Nat)) = ∅ ∧
    ([Update.add 7, .add 7, .remove 7].foldl abstractStep (∅ : Finset Nat)) ≠ {7} ∧
    ([Update.remove 7, .add 7].foldl abstractStep (∅ : Finset Nat)) = {7} ∧
    ([Update.remove 7, .add 7].foldl abstractStep (∅ : Finset Nat)) ≠ ∅ := by decide

#print axioms retains_all_adds
#print axioms removes_all_adds
#print axioms defeater_union
end Sal.MRDTs.Paper1.ORSet.SPOT
