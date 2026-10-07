import Sal.MRDTs.Paper1.MetadataInduction
import Sal.MRDTs.Paper1.MetadataRedistribution

/-! Validation of the induction's initial-state and init-rewrite metadata
companions on both exact and efficient OR-set representations. -/
namespace Sal.MRDTs.Paper1
open Foundation

namespace ORSet.AbstractSpec
variable {α : Type} [DecidableEq α]

theorem mergeCommMetadata : AbstractMRDT.MergeCommMetadata (representation (α := α)) := by
  intro C E₁ E₂ l a b h
  have equation : (D α).merge l a b = (D α).merge l b a := by
    change merge l a b = merge l b a
    apply Finset.ext
    intro p
    simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  rw [equation]
  exact h

theorem initialMetadata : AbstractMRDT.InitialMetadata (representation (α := α)) := by
  intro C E s _
  exact ⟨[],⟨List.nodup_nil,by simp⟩,List.Pairwise.nil,rfl⟩

private theorem merge_init_eq (s : (D α).State) : (D α).merge (D α).init (D α).init s = s := by
  change merge ∅ ∅ s = s
  ext p
  simp [merge]

theorem initMetadata : AbstractMRDT.InitMetadata (representation (α := α)) := by
  intro C E s _ h
  rw [merge_init_eq]
  exact h

theorem initVC (C : ReplayContext (D α).toUpdateSig) (E : Set (Op (Update α))) (s : (D α).State) :
    AbstractMRDT.Equivalent (model (α := α)) ((D α).merge (D α).init (D α).init s) s := by
  rw [merge_init_eq]
  exact AbstractMRDT.equivalent_refl _ _

end ORSet.AbstractSpec

namespace EfficientORSet.AbstractSpec
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

theorem mergeCommMetadata : AbstractMRDT.MergeCommMetadata (representation (α := α)) := by
  intro C E₁ E₂ l a b h
  have equation : (D α).merge l a b = (D α).merge l b a := by
    change merge l a b = merge l b a
    apply Finset.ext
    intro p
    simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  rw [equation]
  exact h

theorem initialMetadata : AbstractMRDT.InitialMetadata (representation (α := α)) := by
  intro C E s h
  refine ⟨represents_empty C.vis,⟨[],⟨List.nodup_nil,by simp⟩⟩,by simp,?_,?_⟩
  · exact h.2.2.2.1
  · exact h.2.2.2.2

private theorem merge_init_eq (s : (D α).State) : (D α).merge (D α).init (D α).init s = s := by
  change merge ∅ ∅ s = s
  ext p
  simp [merge]

theorem initMetadata : AbstractMRDT.InitMetadata (representation (α := α)) := by
  intro C E s _ h
  rw [merge_init_eq]
  exact h

theorem initVC (C : ReplayContext (D α).toUpdateSig) (E : Set (Event α)) (s : (D α).State) :
    AbstractMRDT.Equivalent (model (α := α)) ((D α).merge (D α).init (D α).init s) s := by
  rw [merge_init_eq]
  exact AbstractMRDT.equivalent_refl _ _

end EfficientORSet.AbstractSpec
end Sal.MRDTs.Paper1
