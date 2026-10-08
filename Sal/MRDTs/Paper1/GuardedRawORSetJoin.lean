import Sal.MRDTs.Paper1.GuardedRawORSetVC
import Sal.MRDTs.Paper1.ConcreteORSetAlgebra

/-! Exact and efficient OR-set Join derived from five raw equality VCs and
finite replay reconstruction. No representation-merge theorem is a premise. -/
namespace Sal.MRDTs.Paper1.EfficientORSet.GuardedRawVC
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

theorem representationJoin : ConcreteMRDT.RepresentationJoin (RawReplay.representation (α := α)) := by
  apply ConcreteMRDT.Raw.representationJoin_of_vcs mergeVCs RawReplay.unique
    RawReplay.initial_from_representation RawReplay.finite
  intro C E₁ E₂ a b trans irrefl _ _ ha _
  exact RawReplay.replaySupply C trans irrefl ha.2.2.2.2

#print axioms representationJoin
end Sal.MRDTs.Paper1.EfficientORSet.GuardedRawVC

namespace Sal.MRDTs.Paper1.ORSet.GuardedRawVC
open Foundation
variable {α : Type} [DecidableEq α]

theorem mergeVCs : ConcreteMRDT.Raw.MergeVCs (conflict α)
    RawReplay.representation (RawReplay.scheme (α := α)) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro C E₁ E₂ l a b _ _ _ _ _ _ _
    change merge l a b = merge l b a
    ext p
    simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  · intro C E s _ _ _
    change merge ∅ ∅ s = s
    ext p
    simp [merge]
  · intro C U s B e _ _ supported closed member semantic _ hs hB _ _
    exact ConcreteRep.causal_replay_eq C U s B e member supported closed
      semantic hs.1 hB.1
  · intro C E₁ E₂ l B t b e ctx member absent base past _ other _ _ _
    exact ConcreteRep.local_replay_eq C E₁ E₂ l B t b e member absent
      ctx.supported₁ ctx.supported₂ ctx.closed₁ base.1 past.1 other.1
  · intro C E₁ E₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _
    exact ConcreteRep.shared_replay_eq t₀ t₁ t₂ B e

theorem representationJoin : ConcreteMRDT.RepresentationJoin (RawReplay.representation (α := α)) := by
  apply ConcreteMRDT.Raw.representationJoin_of_vcs mergeVCs RawReplay.unique
    (fun C _ _ _ => RawReplay.initial C) RawReplay.finite
  intro C E₁ E₂ a b trans irrefl _ _ _ _
  exact RawReplay.replaySupply C trans irrefl

#print axioms mergeVCs
#print axioms representationJoin
end Sal.MRDTs.Paper1.ORSet.GuardedRawVC
