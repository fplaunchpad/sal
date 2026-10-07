import Sal.MRDTs.Paper1.CommutingVCReplay
import Sal.MRDTs.Paper1.BoundedCounterEvent
import Sal.MRDTs.Paper1.TreeSheetEventSpec

/-! Abstraction VC ports for the three guarded commuting production datatypes.
Their languages and issuers are unchanged. Canonical version evidence comes
from the VC induction; origin legality is reconstructed from that evidence and
honest issuance. No production Join theorem is used by these ports. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT.GuardedPorts
open Foundation

private theorem virtual_reach {D : MRDTSig} {I : Issuance D} {C : Configuration D}
    (exec : CertifiedExecution D I C) :
    MintCertifiedReachV D (canonicalVirtualMergeBase D) I C := by
  cases exec with
  | ordinary reach => exact reach.toV
  | virtual reach => exact reach

namespace Bounded
open Instances.BoundedCounter

noncomputable def model : Model BC := Model.future BC

private theorem issuanceHonest {C : Configuration BC}
    (mint : MintHonest BC bcApplicable C) : HonestAppOn BC bcApplicable C := by
  intro e he
  obtain ⟨ops,perm,visible,guard⟩ := mint e he
  exact ⟨applySeq BC.toUpdateSig BC.init ops,⟨ops,perm,visible,rfl⟩,guard⟩

theorem history : EventExecutionHistoryAdequacy BC (commutingPolicy BC.AppOp)
    BoundedCounterEvent.spec generation := by
  intro C exec v s E hv q
  have good := CommutingPort.vcCanonicalConfig model BC_all_comm
    BC_mergeLaws BC_deltaLaws BC_commutingPeelLaw (virtual_reach exec)
  have causal := causalCanonical_of_all_comm_rc_either BC_all_comm
    (fun _ _ => rfl) good
  obtain ⟨ops,hperm,hvis,_,_⟩ := causal v s E hv
  have legal : SequentialHonest ops :=
    prefix_inv_of_causal_witness bc_inv_init bc_safetyStep good
      (issuanceHonest exec.mintHonest) hv hperm hvis
  refine ⟨ops,hperm,?_,hvis.imp (fun {_ _} h edge => h edge.1),?_⟩
  · apply List.pairwise_of_forall
    intro a b
    exact paperOrder_false_of_all_commute BC_all_comm C.replayContext E b a
  · have accepted := BoundedCounterEvent.accepted_of_prefix_safety ops legal q
    have answer : BoundedCounterEvent.run ops q =
        BC.query (applySeq BC.toUpdateSig BC.init ops) q := by
      rw [BoundedCounterEvent.run_refines]
      rfl
    simpa only [projectedLabels, List.map_id_fun, answer] using accepted

noncomputable def conditions : ScopedVCConditions model (commutingPolicy BC.AppOp)
    BoundedCounterEvent.spec generation :=
  CommutingPort.scopedConditions model (future_complete BC) BC_all_comm
    BC_mergeLaws BC_deltaLaws BC_commutingPeelLaw generation history

theorem versionsV {C : Configuration BC}
    (reach : MintCertifiedReachV BC (canonicalVirtualMergeBase BC) generation C) :
    VersionsRALinearizable model (commutingPolicy BC.AppOp) BoundedCounterEvent.spec C :=
  conditions.versionsV reach

theorem executions (trace : List (Label BC × Configuration BC))
    (exec : (certifiedTS BC generation).Execution (initConfig BC) trace) :
    ExecutionCorrect model (commutingPolicy BC.AppOp) BoundedCounterEvent.spec trace :=
  conditions.executions trace exec

theorem executionsV (trace : List (Label BC × Configuration BC))
    (exec : (certifiedTSV BC generation).Execution (initConfig BC) trace) :
    ExecutionCorrect model (commutingPolicy BC.AppOp) BoundedCounterEvent.spec trace :=
  conditions.executionsV trace exec

end Bounded

namespace Tree
open Instances.TreeMove

noncomputable def model : Model D := Model.future D

/-- Honest origins remain in a visibility-respecting replay prefix. The
canonical configuration premise is supplied by the abstraction VC induction.
-/
theorem originLegal {C : Configuration D} (good : CanonicalConfig C)
    (mint : MintHonest D generation.CanIssue C)
    {v : Version} {s : D.State} {E : Set Event} {ops : List Event}
    (hv : C.ver v = some (s,E)) (perm : listPermOf ops E)
    (legal : SequentialLegal ops) (visible : respects ops C.vis) :
    ClientLegal ops := by
  refine ⟨legal,?_⟩
  intro pre e post split
  have heE : e ∈ E := (perm.2 e).mp (by rw [split]; simp)
  obtain ⟨past,hpast,_,guard⟩ := mint e (good.version_events_supported v s E hv e heE)
  refine ⟨past.toFinset,?_,?_⟩
  · intro old hold
    have before := (hpast.2 old).mp (List.mem_toFinset.mp hold)
    have oldE := good.version_events_causal v s E hv old e before.2 heE
    have member := (perm.2 old).mpr oldE
    rw [split] at member
    rcases List.mem_append.mp member with inPre | inRest
    · exact List.mem_toFinset.mpr inPre
    · rcases List.mem_cons.mp inRest with same | inPost
      · subst old
        exact False.elim (Nat.lt_irrefl _ (C.causal_mono before.2))
      · have ordered := visible
        rw [split] at ordered
        have noBack := (List.pairwise_cons.mp
          (List.pairwise_append.mp ordered).2.1).1 old inPost
        exact False.elim (noBack before.2)
  · simpa only [generation, applySeq_eq_toFinset] using guard

theorem history : EventExecutionHistoryAdequacy D (commutingPolicy D.AppOp)
    TreeMoveEvent.spec generation := by
  intro C exec v s E hv q
  cases q
  have good := CommutingPort.vcCanonicalConfig model all_comm
    mergeLaws deltaLaws commutingPeelLaw (virtual_reach exec)
  obtain ⟨ops,perm,_,folded⟩ := good.canonical v s E hv
  have state : ops.toFinset = s := by rw [← folded,applySeq_eq_toFinset]
  let π := orderedEvents s
  have πperm : listPermOf π E := by
    refine ⟨Finset.sort_nodup _ _,?_⟩
    intro e
    simp only [π,orderedEvents,Finset.mem_sort]
    rw [← state]
    simpa using perm.2 e
  have chronological : SequentialLegal π :=
    ⟨Finset.sort_nodup _ _,Finset.pairwise_sort _ _⟩
  have visible : respects π C.vis := by
    unfold respects
    refine chronological.2.imp ?_
    intro a b hab hba
    have hbaLE := eventLE_of_timestamp_lt (C.causal_mono hba)
    have same := eventKey_injective (le_antisymm hab hbaLE)
    subst b
    exact Nat.lt_irrefl _ (C.causal_mono hba)
  have legal := originLegal good exec.mintHonest hv πperm chronological visible
  refine ⟨π,πperm,?_,visible.imp (fun {_ _} h edge => h edge.1),?_⟩
  · apply List.pairwise_of_forall
    intro a b
    exact paperOrder_false_of_all_commute all_comm C.replayContext E b a
  · have accepted := GuardedHistory.admits_updates_query sequentialSpec
      TreeMoveEvent.legal_prefix π legal ()
    have answer : D.query (applySeq D.toUpdateSig D.init π) () =
        sequentialSpec.query (sequentialSpec.run π) () :=
      congrArg visibleTree (sequentialSound π chronological)
    rw [answer]
    exact accepted

noncomputable def conditions : ScopedVCConditions model (commutingPolicy D.AppOp)
    TreeMoveEvent.spec generation :=
  CommutingPort.scopedConditions model (future_complete D) all_comm
    mergeLaws deltaLaws commutingPeelLaw generation history

theorem versionsV {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C) :
    VersionsRALinearizable model (commutingPolicy D.AppOp) TreeMoveEvent.spec C :=
  conditions.versionsV reach

theorem executions (trace : List (Label D × Configuration D))
    (exec : (certifiedTS D generation).Execution (initConfig D) trace) :
    ExecutionCorrect model (commutingPolicy D.AppOp) TreeMoveEvent.spec trace :=
  conditions.executions trace exec

theorem executionsV (trace : List (Label D × Configuration D))
    (exec : (certifiedTSV D generation).Execution (initConfig D) trace) :
    ExecutionCorrect model (commutingPolicy D.AppOp) TreeMoveEvent.spec trace :=
  conditions.executionsV trace exec

end Tree

namespace Sheet
open Instances.AegisSheet
open Instances.AegisSheet.Sequential

def model : Model D := Model.future D

/-- Parameterized form of causal-origin legality: support and causal closure
are explicit evidence, not obtained from the existing production Join theorem.
-/
theorem originLegal {C : Configuration D} (good : CanonicalConfig C)
    (mint : MintHonest D generation.CanIssue C)
    {v : Version} {s : D.State} {E : Set Event} {ops : List Event}
    (hv : C.ver v = some (s,E)) (perm : listPermOf ops E) :
    CausalOriginLegal (canonical ops) := by
  have supported := good.version_events_supported v s E hv
  have closed := good.version_events_causal v s E hv
  have unique : Instances.AegisSheet.GC.TimestampUnique ops.toFinset := by
    intro a ha b hb same
    apply C.replayContext.ts_unique
    · exact supported a ((perm.2 a).mp (by simpa using ha))
    · exact supported b ((perm.2 b).mp (by simpa using hb))
    · exact same
  have chronological := canonical_chronological perm.1 unique
  refine ⟨chronological,?_⟩
  intro pre e post split
  have eCanonical : e ∈ canonical ops := by rw [split]; simp
  have eE : e ∈ E := (perm.2 e).mp ((canonical_perm ops).mem_iff.mp eCanonical)
  obtain ⟨origin,originPerm,_,issued⟩ := mint e (supported e eE)
  have guard : applicable e origin.toFinset := by
    simpa [Instances.AegisSheet.applySeq_eq_toFinset] using issued
  refine ⟨origin.toFinset,?_,guard⟩
  intro old member
  have oldPred := (originPerm.2 old).mp (by simpa using member)
  have oldE := closed old e oldPred.2 eE
  have oldCanonical : old ∈ canonical ops :=
    (canonical_perm ops).mem_iff.mpr ((perm.2 old).mpr oldE)
  have oldTime : old.1 < e.1 := guard.2.lt old.1 (eventTime_mem member)
  have oldPrefix := mem_prefix_of_chronological chronological split oldCanonical oldTime
  simpa using oldPrefix

theorem history : EventExecutionHistoryAdequacy D (commutingPolicy D.AppOp)
    AegisSheetEvent.spec generation := by
  intro C exec v s E hv q
  have good := CommutingPort.vcCanonicalConfig model all_comm
    mergeLaws deltaLaws commutingPeelLaw (virtual_reach exec)
  obtain ⟨ops,perm,_,_⟩ := good.canonical v s E hv
  have legal := originLegal good exec.mintHonest hv perm
  have πperm : listPermOf (canonical ops) E :=
    ⟨canonical_nodup perm.1,fun e => (canonical_perm ops).mem_iff.trans (perm.2 e)⟩
  refine ⟨canonical ops,πperm,?_,?_,?_⟩
  · apply List.pairwise_of_forall
    intro a b
    exact paperOrder_false_of_all_commute all_comm C.replayContext E b a
  · exact (chronological_respects_vis C legal.1).imp (fun {_ _} h edge => h edge.1)
  · have accepted := GuardedHistory.admits_updates_query clientSpec
      AegisSheetEvent.legal_prefix (canonical ops) legal q
    have refined := causalOriginSequentialSound (canonical ops) legal
    have answer : D.query (applySeq D.toUpdateSig D.init (canonical ops)) q =
        clientSpec.query (clientSpec.run (canonical ops)) q := by
      cases q
      simpa [D,clientSpec] using refined.2.2.symm
    rw [answer]
    exact accepted

noncomputable def conditions : ScopedVCConditions model (commutingPolicy D.AppOp)
    AegisSheetEvent.spec generation :=
  CommutingPort.scopedConditions model (future_complete D) all_comm
    mergeLaws deltaLaws commutingPeelLaw generation history

theorem versionsV {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C) :
    VersionsRALinearizable model (commutingPolicy D.AppOp) AegisSheetEvent.spec C :=
  conditions.versionsV reach

theorem executions (trace : List (Label D × Configuration D))
    (exec : (certifiedTS D generation).Execution (initConfig D) trace) :
    ExecutionCorrect model (commutingPolicy D.AppOp) AegisSheetEvent.spec trace :=
  conditions.executions trace exec

theorem executionsV (trace : List (Label D × Configuration D))
    (exec : (certifiedTSV D generation).Execution (initConfig D) trace) :
    ExecutionCorrect model (commutingPolicy D.AppOp) AegisSheetEvent.spec trace :=
  conditions.executionsV trace exec

end Sheet

#print axioms Bounded.conditions
#print axioms Tree.conditions
#print axioms Sheet.conditions
#print axioms Bounded.executionsV
#print axioms Tree.executionsV
#print axioms Sheet.executionsV
end Sal.MRDTs.Paper1.AbstractMRDT.GuardedPorts
