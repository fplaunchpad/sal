import Sal.MRDTs.Instances.PriorityQueueSameRecord
import Sal.MRDTs.Paper1.ConcreteCommutingVCReplay
import Sal.MRDTs.Paper1.Automation.CommutingAssembly

/-! The repaired query leaves immutable source effects unchanged. Five merge
VCs derive Join via the common metadata induction. These are replay/convergence
results; no ordinary-priority-queue history certificate is claimed here. -/
namespace Sal.MRDTs.Paper1.PriorityQueueSameRecord
open Foundation Instances.PriorityQueueSameRecord
open Instances.PublishedAddWinsPriorityQueue (State.ext)

abbrev policy := commutingPolicy Payload

private theorem merge_update (a b l : State) (e : Event) :
    merge l (step a e) b = step (merge l a b) e := by
  rcases e with ⟨t,r,op⟩
  cases op <;> apply Instances.PublishedAddWinsPriorityQueue.State.ext <;>
    simp [step,merge,Instances.PublishedAddWinsPriorityQueue.step,
      Instances.PublishedAddWinsPriorityQueue.merge,Finset.union_assoc,
      Finset.union_comm,Finset.union_left_comm]

def mergeLaws : MergeLaws D where
  replay := ReplayLaws.of_all_comm effects_commute (by
    apply replayAcyclic_of_noReplayChain
    intro a b c
    simp [UpdateSig.replayOrder,EventOrder.default,EventOrder.unconstrained])
  merge_comm := by
    intro l a b
    apply Instances.PublishedAddWinsPriorityQueue.State.ext <;>
      simp [D,merge,Instances.PublishedAddWinsPriorityQueue.merge,Finset.union_comm]
  merge_init := by
    intro s
    apply Instances.PublishedAddWinsPriorityQueue.State.ext <;>
      simp [D,merge,Instances.PublishedAddWinsPriorityQueue.merge]

def deltaLaws : DeltaLaws D where
  redistribute := by
    intro l a b c d
    apply Instances.PublishedAddWinsPriorityQueue.State.ext <;>
      simp [D,merge,Instances.PublishedAddWinsPriorityQueue.merge,
        Finset.union_assoc,Finset.union_comm,Finset.union_left_comm]
  local_redistribute := by
    intro l a b c d
    apply Instances.PublishedAddWinsPriorityQueue.State.ext <;>
      simp [D,merge,Instances.PublishedAddWinsPriorityQueue.merge,
        Finset.union_assoc,Finset.union_comm,Finset.union_left_comm]

def peelLaw : CommutingPeelLaw D where
  commuting_peel := by
    intro a e pre post _ _
    exact merge_update a (applySeq D.toUpdateSig D.init post) (applySeq D.toUpdateSig D.init pre) e

theorem fiveVC : ConcreteMRDT.Raw.MergeVCs policy
    (ConcreteMRDT.CommutingPort.representation D)
    (ConcreteMRDT.CommutingPort.scheme effects_commute) :=
  ConcreteMRDT.CommutingPort.mergeVCs effects_commute mergeLaws deltaLaws peelLaw

def replayConditions : ConcreteMRDT.VCReplayConditions policy generation :=
  ConcreteMRDT.CommutingPort.automatedReplayConditions effects_commute fiveVC generation

theorem representationJoin : ConcreteMRDT.RepresentationJoin replayConditions.representation :=
  replayConditions.join

theorem joinAt (C : ReplayContext D.toUpdateSig) : JoinAt D C :=
  ConcreteMRDT.CommutingPort.automatedJoinAt effects_commute fiveVC C

/-- All allocated versions in ordinary or recursive-merge certified executions
have a replay witness. This theorem does not yet supply an ordinary queue spec. -/
theorem canonicalVersions {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C) :
    CanonicalConfig C :=
  ConcreteMRDT.CommutingPort.automatedCanonicalConfig effects_commute fiveVC reach

#print axioms fiveVC
#print axioms representationJoin
#print axioms canonicalVersions
end Sal.MRDTs.Paper1.PriorityQueueSameRecord
