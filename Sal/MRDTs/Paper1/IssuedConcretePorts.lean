import Sal.MRDTs.Paper1.GuardedProjectionHistory
import Sal.MRDTs.Paper1.Automation.CommutingInputs
import Sal.MRDTs.Paper1.Automation.CommutingAssembly
import Sal.MRDTs.Paper1.ConcreteCommutingVCReplay
import Sal.MRDTs.Paper1.TreeSheetEventSpec

/-! Concrete VC ports for the two guarded commuting production datatypes.
Their languages and issuers are unchanged. Canonical version evidence comes
from the VC induction; origin legality is reconstructed from that evidence and
honest issuance. No production Join theorem is used by these ports. -/
namespace Sal.MRDTs.Paper1.ConcreteMRDT.GuardedPorts
open Foundation

private theorem virtual_reach {D : MRDTSig} {I : Issuance D} {C : Configuration D}
    (exec : CertifiedExecution D I C) :
    MintCertifiedReachV D (canonicalVirtualMergeBase D) I C := by
  cases exec with
  | ordinary reach => exact reach.toV
  | virtual reach => exact reach



namespace Tree
open Instances.TreeMove

/-- Honest origins remain in a visibility-respecting replay prefix. The
canonical configuration premise is supplied by the concrete VC induction.
-/
theorem originLegal {C : Configuration D} (good : CanonicalConfig C)
    (mint : MintHonest D generation.CanIssue C)
    {v : Version} {s : D.State} {E : Set Event} {ops : List Event}
    (hv : C.ver v = some (s,E)) (perm : listPermOf ops E)
    (legal : SequentialLegal ops) (visible : respects ops C.vis) :
    ClientLegal ops := by
  refine ⟨legal, ?_⟩
  exact Automation.mint_origin_prefix id applicable applySeq_eq_toFinset
    (fun _ _ h => h) mint (good.version_events_supported v s E hv)
    (good.version_events_causal v s E hv) perm visible

theorem history : EventExecutionHistoryAdequacy D (commutingPolicy D.AppOp)
    TreeMoveEvent.spec generation := by
  intro C exec v s E hv q
  cases q
  have good := CommutingPort.automatedCanonicalConfig all_comm (by mrdt_verify) (virtual_reach exec)
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
  exact ⟨π, stateProjection.witness all_comm C E π πperm visible legal ()⟩

noncomputable def conditions : ScopedVCConditions (commutingPolicy D.AppOp)
    TreeMoveEvent.spec generation :=
  CommutingPort.automatedScopedConditions all_comm (by mrdt_verify) generation history

theorem versionsV {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C) :
    VersionsWitness (commutingPolicy D.AppOp) TreeMoveEvent.spec C :=
  conditions.versionsV reach

theorem executions (trace : List (Label D × Configuration D))
    (exec : (certifiedTS D generation).Execution (initConfig D) trace) :
    ExecutionCorrect (commutingPolicy D.AppOp) TreeMoveEvent.spec trace :=
  conditions.executions trace exec

theorem executionsV (trace : List (Label D × Configuration D))
    (exec : (certifiedTSV D generation).Execution (initConfig D) trace) :
    ExecutionCorrect (commutingPolicy D.AppOp) TreeMoveEvent.spec trace :=
  conditions.executionsV trace exec

end Tree

namespace Sheet
open Instances.AegisSheet
open Instances.AegisSheet.Sequential

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
  refine ⟨chronological, ?_⟩
  exact Automation.mint_origin_prefix id applicable applySeq_eq_toFinset
    (fun _ _ h => h) mint supported closed
    ⟨canonical_nodup perm.1,
      fun a => (canonical_perm ops).mem_iff.trans (perm.2 a)⟩
    (chronological_respects_vis C chronological)

theorem history : EventExecutionHistoryAdequacy D (commutingPolicy D.AppOp)
    AegisSheetEvent.spec generation := by
  intro C exec v s E hv q
  have good := CommutingPort.automatedCanonicalConfig all_comm (by mrdt_verify) (virtual_reach exec)
  obtain ⟨ops,perm,_,_⟩ := good.canonical v s E hv
  have legal := originLegal good exec.mintHonest hv perm
  have πperm : listPermOf (canonical ops) E :=
    ⟨canonical_nodup perm.1,fun e => (canonical_perm ops).mem_iff.trans (perm.2 e)⟩
  exact ⟨canonical ops, materializeProjection.witness all_comm C E (canonical ops)
    πperm (chronological_respects_vis C legal.1) legal q⟩

noncomputable def conditions : ScopedVCConditions (commutingPolicy D.AppOp)
    AegisSheetEvent.spec generation :=
  CommutingPort.automatedScopedConditions all_comm (by mrdt_verify) generation history

theorem versionsV {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C) :
    VersionsWitness (commutingPolicy D.AppOp) AegisSheetEvent.spec C :=
  conditions.versionsV reach

theorem executions (trace : List (Label D × Configuration D))
    (exec : (certifiedTS D generation).Execution (initConfig D) trace) :
    ExecutionCorrect (commutingPolicy D.AppOp) AegisSheetEvent.spec trace :=
  conditions.executions trace exec

theorem executionsV (trace : List (Label D × Configuration D))
    (exec : (certifiedTSV D generation).Execution (initConfig D) trace) :
    ExecutionCorrect (commutingPolicy D.AppOp) AegisSheetEvent.spec trace :=
  conditions.executionsV trace exec

end Sheet

#print axioms Tree.conditions
#print axioms Sheet.conditions
#print axioms Tree.executionsV
#print axioms Sheet.executionsV
end Sal.MRDTs.Paper1.ConcreteMRDT.GuardedPorts
