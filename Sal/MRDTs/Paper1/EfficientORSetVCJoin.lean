import Sal.MRDTs.Paper1.EfficientRemoveObservations

namespace Sal.MRDTs.Paper1.EfficientORSet.AbstractSpec
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

/-- Adds use equality of element observations; removes and shared
redistribution admit stronger concrete equations. None uses Join. -/
theorem mergeVCs : AbstractMRDT.DependencyMergeVCs (model (α := α)) (EventSpec.conflict α)
    representation (fun C => AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C) := by
  refine ⟨?_,⟨?_,?_,?_⟩,?_⟩
  · intro l a b
    have equation : (D α).merge l a b = (D α).merge l b a := by
      change merge l a b = merge l b a
      apply Finset.ext
      intro p
      simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
      tauto
    rw [equation]
    exact AbstractMRDT.equivalent_refl _ _
  · intro C E s _ _
    exact initVC C E s
  · intro C E₁ E₂ l B t s e trans _ _ _ closed₁ _ member absent _ base past _ other
    rcases e with ⟨et,er,op⟩
    cases op with
    | add x =>
      have freshPast := fresh_past_record C B et er x past.2.1
      have freshBase : (er,et,x) ∉ (show State α from l) := by
        intro mem
        exact absent ((base.2.1 (er,et,x)).mp mem).1.2
      exact local_add_observation l B t s et er x freshPast freshBase
    | remove x =>
      have equation := local_remove_eq C E₁ E₂ l B t s et er x
        (fun _ _ _ h k => trans h k) member closed₁ base.2.1 past.2.1 other.2.1
      change AbstractMRDT.Equivalent (model (α := α))
        (merge l (merge B t (update B (et,er,.remove x))) s)
        (merge B (merge l t s) (update B (et,er,.remove x)))
      rw [equation]
      exact AbstractMRDT.equivalent_refl _ _
  · intro C E₁ E₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [shared_replay_eq]
    exact AbstractMRDT.equivalent_refl _ _
  · intro C U A B e trans _ supported closed member maximal pre past
    rcases e with ⟨et,er,op⟩
    cases op with
    | add x =>
      exact causal_add_observation A B et er x (fresh_past_record C B et er x past.2.1)
    | remove x =>
      have equation := causal_remove_eq C U A B et er x trans member supported closed maximal pre.2.1 past.2.1
      change AbstractMRDT.Equivalent (model (α := α))
        (merge B A (update B (et,er,.remove x))) (update A (et,er,.remove x))
      rw [equation]
      exact AbstractMRDT.equivalent_refl _ _

theorem vcRepresentationJoin : AbstractMRDT.RepresentationJoin (representation (α := α)) := by
  apply AbstractMRDT.representationJoin_of_vcs laws mergeVCs representsCanonical metadataSubstitution
    initialMetadata initMetadata mergeCommMetadata causalMetadata localMetadata sharedMetadata
  intro C E₁ E₂ a b trans irrefl _ _ ha _
  exact replaySupply C trans irrefl ha.2.2.2.2

end Sal.MRDTs.Paper1.EfficientORSet.AbstractSpec
