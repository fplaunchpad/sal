import Sal.MRDTs.Paper1.MetadataSupply

/-! Shared redistribution is concrete finite-set algebra for both OR-sets.
These proofs do not invoke representation Join or sequential adequacy. -/
namespace Sal.MRDTs.Paper1
open Foundation

private def setMerge {β : Type} [DecidableEq β] (l a b : Finset β) : Finset β :=
  (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

private theorem setMerge_shared {β : Type} [DecidableEq β]
    (t₀ t₁ t₂ B d : Finset β) :
    setMerge (setMerge B t₀ d) (setMerge B t₁ d) (setMerge B t₂ d) =
      setMerge B (setMerge t₀ t₁ t₂) d := by
  apply Finset.ext
  intro p
  by_cases base : p ∈ B <;> by_cases delta : p ∈ d
  all_goals
    simp only [setMerge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,base,delta,
      and_true,true_and,false_and,and_false,false_or,or_false,or_true,
      not_true_eq_false,not_false_eq_true]

namespace ORSet.AbstractSpec
variable {α : Type} [DecidableEq α]

theorem shared_replay_eq (t₀ t₁ t₂ B : (D α).State) (e : Op (Update α)) :
    (D α).merge ((D α).merge B t₀ ((D α).update B e))
      ((D α).merge B t₁ ((D α).update B e))
      ((D α).merge B t₂ ((D α).update B e)) =
    (D α).merge B ((D α).merge t₀ t₁ t₂) ((D α).update B e) :=
  setMerge_shared t₀ t₁ t₂ B ((D α).update B e)

theorem sharedMetadata : AbstractMRDT.SharedMetadata (model (α := α)) (conflict α)
    representation (fun C => AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C) := by
  intro C E₁ E₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ target
  rw [shared_replay_eq]
  exact target

end ORSet.AbstractSpec

namespace EfficientORSet.AbstractSpec
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

theorem shared_replay_eq (t₀ t₁ t₂ B : (D α).State) (e : Event α) :
    (D α).merge ((D α).merge B t₀ ((D α).update B e))
      ((D α).merge B t₁ ((D α).update B e))
      ((D α).merge B t₂ ((D α).update B e)) =
    (D α).merge B ((D α).merge t₀ t₁ t₂) ((D α).update B e) :=
  setMerge_shared t₀ t₁ t₂ B ((D α).update B e)

theorem sharedMetadata : AbstractMRDT.SharedMetadata (model (α := α)) (EventSpec.conflict α)
    representation (fun C => AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C) := by
  intro C E₁ E₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ target
  rw [shared_replay_eq]
  exact target

end EfficientORSet.AbstractSpec
end Sal.MRDTs.Paper1
