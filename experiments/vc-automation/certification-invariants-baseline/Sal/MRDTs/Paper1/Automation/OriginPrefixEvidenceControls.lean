import Sal.MRDTs.Paper1.Automation.OriginPrefixEvidence
import Mathlib.Data.Finset.Empty

/-! Hand-derived PASS+FAIL controls. The only causal edge is 1 → 2. -/
namespace Sal.MRDTs.Paper1.Automation.OriginPrefixEvidenceControls
open Sal.MRDTs.Foundation OriginPrefixEvidence

private def edge (a b : Nat) : Prop := a = 1 ∧ b = 2
private def events : Set Nat := {1, 2}

private theorem closed : ∀ a b, edge a b → b ∈ events → a ∈ events := by
  intro a b h _
  simp [events, h.1]

/-- In the ordered replay, the predecessor enters a nonempty prefix. -/
theorem ordered_predecessor :
    ([1] : List Nat).toFinset ⊆ ([1] : List Nat).toFinset ∧
      ([1] : List Nat).toFinset ≠ ∅ := by
  constructor
  · apply origin_subset_prefix
      (ops := [1,2]) (origin := [1]) (pre := [1]) (post := [])
      (e := 2) (R := edge) (E := events)
    · constructor
      · decide
      · intro a; simp [events]
    · simp [respects, edge]
    · intro a h; rcases h with ⟨h1,h2⟩; omega
    · exact closed
    · intro a h; simp only [List.mem_singleton] at h; subst a; exact ⟨rfl,rfl⟩
    · rfl
  · decide

/-- Reversing the replay retains enumeration, closure and predecessor evidence,
but violates order and puts that predecessor outside the empty prefix. -/
theorem unordered_counterexample :
    listPermOf ([2,1] : List Nat) events ∧
      (∀ a, ¬ edge a a) ∧
      (∀ a b, edge a b → b ∈ events → a ∈ events) ∧
      (∀ a ∈ ([1] : List Nat), edge a 2) ∧
      ([2,1] : List Nat) = [] ++ 2 :: [1] ∧
      ¬ respects ([2,1] : List Nat) edge ∧
      ¬ (([1] : List Nat).toFinset ⊆ ([] : List Nat).toFinset) := by
  refine ⟨⟨by decide, ?_⟩, ?_, closed, ?_, rfl, ?_, ?_⟩
  · intro a; simp [events, or_comm]
  · intro a h; rcases h with ⟨h1,h2⟩; omega
  · intro a h; simp only [List.mem_singleton] at h; subst a; exact ⟨rfl,rfl⟩
  · simp [respects, edge]
  · decide

end Sal.MRDTs.Paper1.Automation.OriginPrefixEvidenceControls
