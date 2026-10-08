import InductiveCountermodelVC

/-! The exact scope of the negative result: the 21 translated merge leaves,
even with Sal's stronger policy laws, do not imply its five indexed VCs for
canonical representations and concrete-conflict metadata. -/
namespace NeemExpansion
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1
open Sal.MRDTs.Paper1.ConcreteMRDT

structure MergeLeaves (D : Signature) : Prop where
  comm : D.comm
  idem : D.idem
  base1 : D.base1
  base2 : D.base2
  common1 : D.common1
  common2 : D.common2
  zero : D.zero
  inter_right_base_2op : D.inter_right_base_2op
  inter_left_base_2op : D.inter_left_base_2op
  inter_right_2op : D.inter_right_2op
  inter_left_2op : D.inter_left_2op
  inter_lca_2op : D.inter_lca_2op
  ind_right_2op : D.ind_right_2op
  ind_left_2op : D.ind_left_2op
  inter_right_base_1op : D.inter_right_base_1op
  inter_left_base_1op : D.inter_left_base_1op
  inter_right_1op : D.inter_right_1op
  inter_left_1op : D.inter_left_1op
  inter_lca_1op : D.inter_lca_1op
  ind_left_1op : D.ind_left_1op
  ind_right_1op : D.ind_right_1op

def ghostLeaves : MergeLeaves Ghost.signature where
  comm := Ghost.comm
  idem := Ghost.idem
  base1 := Ghost.base1
  base2 := Ghost.base2
  common1 := Ghost.common1
  common2 := Ghost.common2
  zero := Ghost.zero
  inter_right_base_2op := Ghost.inter_right_base_2op
  inter_left_base_2op := Ghost.inter_left_base_2op
  inter_right_2op := Ghost.inter_right_2op
  inter_left_2op := Ghost.inter_left_2op
  inter_lca_2op := Ghost.inter_lca_2op
  ind_right_2op := Ghost.ind_right_2op
  ind_left_2op := Ghost.ind_left_2op
  inter_right_base_1op := Ghost.inter_right_base_1op
  inter_left_base_1op := Ghost.inter_left_base_1op
  inter_right_1op := Ghost.inter_right_1op
  inter_left_1op := Ghost.inter_left_1op
  inter_lca_1op := Ghost.inter_lca_1op
  ind_left_1op := Ghost.ind_left_1op
  ind_right_1op := Ghost.ind_right_1op

def fromMRDT (D : MRDTSig) (order : Op D.AppOp → Op D.AppOp → RcRes) : Signature :=
  ⟨D.State,D.AppOp,D.init,D.update,D.merge,order⟩

/-- A single checked witness packages the positive contracts and the failed
five-VC conclusion. The real exact/efficient OR-sets are not counterexamples. -/
theorem counterexample :
    MergeLeaves Ghost.signature ∧
    GuardedReplay.Laws GhostVC.datatype.toUpdateSig GhostVC.policy ∧
    ¬ Raw.MergeVCs GhostVC.policy GhostVC.represented GhostVC.scheme :=
  ⟨ghostLeaves,GhostVC.guardedLaws,GhostVC.not_raw_merge_vcs⟩

/-- There is no universal implication from precisely these leaves and policy
laws to the unchanged five VCs on canonical histories with concrete metadata.
This does not rule out a richer expansion with additional finite obligations. -/
theorem no_generic_bridge :
    ¬ (∀ (D : MRDTSig) (P : OperationPolicy D.AppOp)
      (order : Op D.AppOp → Op D.AppOp → RcRes),
      (∀ a b, order a b = .Fst_then_snd ↔ P.before a.op b.op) →
      MergeLeaves (fromMRDT D order) →
      GuardedReplay.Laws D.toUpdateSig P →
      Raw.MergeVCs P (Canonical P) (fun C => MetadataDependencies.ofConcrete C)) := by
  intro bridge
  exact GhostVC.not_raw_merge_vcs
    (bridge GhostVC.datatype GhostVC.policy Ghost.signature.order
      GhostVC.order_before ghostLeaves GhostVC.guardedLaws)

#print axioms counterexample
#print axioms no_generic_bridge

end NeemExpansion
