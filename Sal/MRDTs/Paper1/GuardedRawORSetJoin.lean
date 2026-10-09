import Sal.MRDTs.Paper1.Automation.ORSetInputs
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
    RawReplay.representation (RawReplay.scheme (α := α)) := by mrdt_verify


theorem representationJoin : ConcreteMRDT.RepresentationJoin (RawReplay.representation (α := α)) := by
  apply ConcreteMRDT.Raw.representationJoin_of_vcs mergeVCs RawReplay.unique
    (fun C _ _ _ => RawReplay.initial C) RawReplay.finite
  intro C E₁ E₂ a b trans irrefl _ _ _ _
  exact RawReplay.replaySupply C trans irrefl

#print axioms mergeVCs
#print axioms representationJoin
end Sal.MRDTs.Paper1.ORSet.GuardedRawVC
