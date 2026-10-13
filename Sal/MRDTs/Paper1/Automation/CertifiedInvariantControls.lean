import Sal.MRDTs.Framework.CertifiedInvariant
import Sal.MRDTs.Framework.GuardedProjectionAutomation

/-! Hand-derived finite controls. Birth membership is monotone upwards, but
neither backwards to arbitrary origins nor across unsupported issuance. -/
namespace Sal.MRDTs.Paper1.Automation.CertifiedInvariantControls
open Foundation

def hasBirth (events : Finset Nat) (_ : Nat) : Prop := 0 ∈ events

theorem hasBirth_mono {s t : Finset Nat} (h : s ⊆ t) {e : Nat}
    (birth : hasBirth s e) : hasBirth t e := h birth

example : ∀ e ∈ insert 1 ({0} : Finset Nat), hasBirth (insert 1 {0}) e := by
  apply all_insert_of_origin hasBirth hasBirth_mono
    (origin := ({0} : Finset Nat))
  · simp [hasBirth]
  · exact Finset.Subset.refl _
  · intro prior
    exact prior 0 (by simp)

example : ¬ (∀ e ∈ ({1} : Finset Nat), hasBirth {1} e) := by
  simp [hasBirth]

example : (∀ e ∈ ({0, 1} : Finset Nat), hasBirth {0, 1} e) ∧
    ({1} : Finset Nat) ⊆ {0, 1} ∧
    ¬ (∀ e ∈ ({1} : Finset Nat), hasBirth {1} e) := by
  simp [hasBirth]

example : ¬ (({0} : Finset Nat) ⊆ ∅) ∧
    (∀ e ∈ (∅ : Finset Nat), hasBirth ∅ e) ∧
    hasBirth {0} 1 ∧ ¬ hasBirth (insert 1 ∅) 1 := by
  simp [hasBirth]

example (s t : Finset Nat) (subset : s ⊆ t)
    (birth : ∃ e ∈ s, e = 0) : ∃ e ∈ t, e = 0 := by
  guarded_projection_step [] using [witness_mono]

example (s : Finset Nat) (old : ∀ e ∈ s, hasBirth s e)
    (new : hasBirth s 1) : ∀ e ∈ insert 1 s, hasBirth (insert 1 s) e := by
  guarded_projection_step [] using [all_insert, hasBirth_mono]

def key (event : Nat × Nat) : Nat := event.1

example : ∀ a ∈ insert (2, 8) ({(1, 7)} : Finset (Nat × Nat)),
    ∀ b ∈ insert (2, 8) ({(1, 7)} : Finset (Nat × Nat)), key a = key b → a = b := by
  apply key_unique_insert
  · simp
  · decide

example : ¬ (∀ a ∈ insert (1, 8) ({(1, 7)} : Finset (Nat × Nat)),
    ∀ b ∈ insert (1, 8) ({(1, 7)} : Finset (Nat × Nat)), key a = key b → a = b) := by
  decide

/-- Event predicates that are not upward closed cannot use the insertion rule. -/
example : ({0} : Finset Nat).card ≤ 1 ∧
    ¬ (insert 1 ({0} : Finset Nat)).card ≤ 1 := by decide

end Sal.MRDTs.Paper1.Automation.CertifiedInvariantControls
