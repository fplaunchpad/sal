import CertifiedExpansion

/-! Hand-derived controls for the finite membership expansion. Each pair
checks a permitted calculation and rejects omission of one evidence premise. -/
namespace NeemExpansion.Certified.Controls

-- Deleting record 1 can be reconstructed from a past containing record 1.
-- An empty past cannot remove a record that appears only in the remainder.
example :
    merge ({1} : Finset Nat) {1} ∅ = ∅ ∧
    merge (∅ : Finset Nat) {1} ∅ ≠ ∅ := by decide

-- A common removed record must be accounted for in the common history.
example :
    merge ({1} : Finset Nat) (merge {1} ∅ ∅) {1} =
      merge {1} (merge {1} ∅ {1}) ∅ ∧
    merge (∅ : Finset Nat) (merge {1} ∅ ∅) {1} ≠
      merge {1} (merge ∅ ∅ {1}) ∅ := by decide

-- A genuinely newborn record is absent from the common history.
example :
    merge (∅ : Finset Nat) (merge ∅ ∅ {1}) ∅ =
      merge ∅ (merge ∅ ∅ ∅) {1} ∧
    merge ({1} : Finset Nat) (merge ∅ ∅ {1}) ∅ ≠
      merge ∅ (merge {1} ∅ ∅) {1} := by decide

end NeemExpansion.Certified.Controls
