import LocalAssembly
import SharedExpansion
import CausalCoverage
import Sal.MRDTs.Paper1.GuardedRawORSetReplay

/-! Integration of newly expanded equations into the unchanged production
five-field MergeVCs package. Datatype representation/scheme names below are
the existing ones; existing VC proofs and Join proofs are not invoked. -/
namespace NeemExpansion.Exact
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
variable {α : Type} [DecidableEq α]

theorem native_initial (s : ORSet.State α) :
    (ORSet.D α).merge (ORSet.D α).init (ORSet.D α).init s = s := by
  change ORSet.merge ∅ ∅ s = s
  exact (comm (∅ : ORSet.State α) (∅ : ORSet.State α) s).trans (diagonal ∅ s)

end NeemExpansion.Exact

namespace NeemExpansion.Efficient
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

theorem native_initial (s : State α) : (D α).merge (D α).init (D α).init s = s := by
  change merge ∅ ∅ s = s
  exact (comm (∅ : State α) (∅ : State α) s).trans (diagonal ∅ s)

end NeemExpansion.Efficient

namespace NeemExpansion.Exact
open Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
variable {α : Type} [DecidableEq α]

/-- All five original equality VCs for the existing exact representation and
metadata scheme, assembled through new finite equation expansion. -/
theorem expanded_vcs : Raw.MergeVCs (ORSet.conflict α)
    (ORSet.RawReplay.representation (α := α)) (ORSet.RawReplay.scheme (α := α)) := by
  constructor
  · intro C E₁ E₂ l a b
    intros
    exact comm l a b
  · intro C E s
    intros
    exact native_initial s
  · exact raw_causal
  · exact raw_local
  · intro C E₁ E₂ t₀ t₁ t₂ B e
    intros
    exact shared_nested t₀ t₁ t₂ B e

end NeemExpansion.Exact

namespace NeemExpansion.Efficient
open Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
variable {α : Type} [DecidableEq α]

/-- All five original equality VCs for the existing efficient semantic
representation; its replay adapter derives the needed facts afresh. -/
theorem expanded_vcs : Raw.MergeVCs (EfficientORSet.EventSpec.conflict α)
    (EfficientORSet.RawReplay.representation (α := α))
    (EfficientORSet.RawReplay.scheme (α := α)) := by
  constructor
  · intro C E₁ E₂ l a b
    intros
    exact comm l a b
  · intro C E s
    intros
    exact native_initial s
  · exact raw_causal
  · exact raw_local
  · intro C E₁ E₂ t₀ t₁ t₂ B e
    intros
    exact shared_nested t₀ t₁ t₂ B e

end NeemExpansion.Efficient

#print axioms NeemExpansion.Exact.expanded_vcs
#print axioms NeemExpansion.Efficient.expanded_vcs
