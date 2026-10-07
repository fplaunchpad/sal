import Sal.MRDTs.Paper1.GuardedRawORSetVC
import Sal.MRDTs.Paper1.ORSetCausalMetadata

/-! Exact and efficient OR-set Join derived from five raw equality VCs and
finite replay reconstruction. No representation-merge theorem is a premise. -/
namespace Sal.MRDTs.Paper1.EfficientORSet.GuardedRawVC
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

theorem representationJoin : AbstractMRDT.RepresentationJoin (RawReplay.representation (α := α)) := by
  apply AbstractMRDT.Raw.representationJoin_of_vcs mergeVCs RawReplay.unique
    RawReplay.initial_from_representation RawReplay.finite
  intro C E₁ E₂ a b trans irrefl _ _ ha _
  exact RawReplay.replaySupply C trans irrefl ha.2.2.2.2

#print axioms representationJoin
end Sal.MRDTs.Paper1.EfficientORSet.GuardedRawVC

namespace Sal.MRDTs.Paper1.ORSet.GuardedRawVC
open Foundation
variable {α : Type} [DecidableEq α]

private theorem old_order_iff_raw (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Op (Update α))) (a b : Op (Update α)) :
    AbstractMRDT.order (AbstractSpec.model (α := α)) (conflict α) C U a b ↔
      paperOrder (conflict α) C U a b := by
  have hc : ∀ a b, AbstractMRDT.Commutes (AbstractSpec.model (α := α)) a b ↔
      (D α).toUpdateSig.commutes a b := by
    intro a b
    exact (AbstractMRDT.ofQuery_commutes QuerySpec.abstraction a b).trans
      (QuerySpec.commutes_iff_concrete a b)
  simp only [AbstractMRDT.order,paperOrder,hc]

theorem mergeVCs : AbstractMRDT.Raw.MergeVCs (RawReplay.model (α := α)) (conflict α)
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
    exact AbstractSpec.causal_replay_eq C U s B e member supported closed
      (fun x hx ne h => semantic x hx ne ((old_order_iff_raw C U e x).mp h)) hs.1 hB.1
  · intro C E₁ E₂ l B t b e ctx member absent base past _ other _ _ _
    exact AbstractSpec.local_replay_eq C E₁ E₂ l B t b e member absent
      ctx.supported₁ ctx.supported₂ ctx.closed₁ base.1 past.1 other.1
  · intro C E₁ E₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _
    exact AbstractSpec.shared_replay_eq t₀ t₁ t₂ B e

theorem representationJoin : AbstractMRDT.RepresentationJoin (RawReplay.representation (α := α)) := by
  apply AbstractMRDT.Raw.representationJoin_of_vcs mergeVCs RawReplay.unique
    (fun C _ _ _ => RawReplay.initial C) RawReplay.finite
  intro C E₁ E₂ a b trans irrefl _ _ _ _
  exact RawReplay.replaySupply C trans irrefl

#print axioms mergeVCs
#print axioms representationJoin
end Sal.MRDTs.Paper1.ORSet.GuardedRawVC
