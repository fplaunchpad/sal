import InductiveLeaves

/-! The nested shared equation is a universal finite collection identity.
It needs neither side-last-event rewrites nor compatible-history coverage. -/
namespace NeemExpansion
open Sal.MRDTs.Foundation

def collectionMerge {β : Type} [DecidableEq β] (l a b : Finset β) : Finset β :=
  (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

theorem collection_shared {β : Type} [DecidableEq β]
    (t₀ t₁ t₂ B d : Finset β) :
    collectionMerge (collectionMerge B t₀ d) (collectionMerge B t₁ d)
      (collectionMerge B t₂ d) = collectionMerge B (collectionMerge t₀ t₁ t₂) d := by
  ext p
  by_cases h₀ : p ∈ t₀ <;> by_cases h₁ : p ∈ t₁ <;>
    by_cases h₂ : p ∈ t₂ <;> by_cases hB : p ∈ B <;>
    by_cases hd : p ∈ d <;> simp [collectionMerge, *]

namespace Signature

def shared_nested (D : Signature) : Prop := ∀ t₀ t₁ t₂ B e,
  D.merge (D.merge B t₀ (D.step B e)) (D.merge B t₁ (D.step B e))
    (D.merge B t₂ (D.step B e)) = D.merge B (D.merge t₀ t₁ t₂) (D.step B e)
end Signature

namespace Exact
variable {α : Type} [DecidableEq α]
theorem shared_nested : (signature (α := α)).shared_nested := by
  intro t₀ t₁ t₂ B e
  exact collection_shared t₀ t₁ t₂ B ((signature (α := α)).step B e)
end Exact

namespace Efficient
variable {α : Type} [DecidableEq α]
theorem shared_nested : (signature (α := α)).shared_nested := by
  intro t₀ t₁ t₂ B e
  exact collection_shared t₀ t₁ t₂ B ((signature (α := α)).step B e)
end Efficient
end NeemExpansion
