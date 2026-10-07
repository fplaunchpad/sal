import Sal.MRDTs.Paper1.EventBridge
import Sal.MRDTs.Paper1.RGAEventSpec

/-! Execution-scoped integration of the independent full-input list machine.
The timestamp is the supplied insertion identifier, and the replica remains
part of every sequential input. The witness uses honest reached execution
facts, including unique timestamps and valid anchors. No global adequacy claim
over arbitrary merely MintHonest configurations is introduced. -/
namespace Sal.MRDTs.Paper1.RGA.EventMigration
open Foundation
open Sal.MRDTs.Instances.RGA

theorem versions {C : Configuration RGAM}
    (execution : CertifiedExecution RGAM generation C) :
    EventVersionsSpecificationRA RGAM emptyPolicy EventSpec.spec C :=
  EventSpec.versions_of_execution execution

/-- The independently accepted history explains its own merge-free fold.
Allocated-version provenance supplies unique births and honest anchor use;
the statement does not consult the stored version's query answer. -/
theorem history :
    EventExecutionHistoryAdequacy RGAM emptyPolicy EventSpec.spec generation := by
  intro C execution v s E hv q
  cases q
  have replay : HasReplayWitness C := by
    cases execution with
    | ordinary reach => exact replayAdequacy.sound reach
    | virtual reach => exact replayAdequacy.soundV reach
  obtain ⟨ops,hp,_,_⟩ := replay v s E hv
  have hwf := versionWellFormed_of_execution execution hv
  refine ⟨canonical ops,canonical_listPermOf hp,
    (canonical_ordered ops).imp (fun {_ _} _ => paperOrder_empty _ _ _ _),?_,?_⟩
  · apply (Identified.canonical_respects_specVisibility true execution hv hp).imp
    intro a b hab hnew
    exact hab ⟨hnew.1,fun hc => hnew.2 ((EventSpec.commutes_iff b a).mpr hc)⟩
  · have href := canonical_refines_list hp hwf
    change read (applySeq RGAM.toUpdateSig RGAM.init (canonical ops)) =
      listSpec.run (canonical ops) at href
    change EventSpec.spec.admits (projectedLabels (D := RGAM) id (canonical ops) ++
      [.query () (read (applySeq RGAM.toUpdateSig RGAM.init (canonical ops)))])
    rw [href,EventSpec.spec_eq]
    simpa only [HistorySpec.withInputs, projectedLabels, List.map_append,
      List.map_cons, List.map_nil, List.map_map, SeqLabel.mapUpdate] using
      (Identified.strict_canonical_admitted hp hwf)

theorem joinAt (C : Configuration RGAM) :
    @JoinAt RGAM emptyPolicy.lift C.replayContext := by
  have policy_eq : emptyPolicy.lift = ReplayPolicy.default RGAM.toUpdateSig := by
    unfold OperationPolicy.lift ReplayPolicy.default ReplayPolicy.unconstrained
    congr 1
    funext a b
    simp [emptyPolicy]
  rw [policy_eq]
  exact Sal.MRDTs.Instances.RGA.join C.replayContext

theorem certifiedV :
    EventCertifiedSpecificationRAV RGAM emptyPolicy EventSpec.spec generation :=
  event_certified_of_join_execution restrictedLaws (fun C _ => joinAt C) history

theorem certified :
    EventCertifiedSpecificationRA RGAM emptyPolicy EventSpec.spec generation :=
  certifiedV.ordinary

theorem executions (trace : List (Label RGAM × Configuration RGAM))
    (execution : (certifiedTS RGAM generation).Execution (initConfig RGAM) trace) :
    ProjectedSpecificationExecution RGAM emptyPolicy id EventSpec.spec
      (initConfig RGAM) trace := certified.executions trace execution

theorem executionsV (trace : List (Label RGAM × Configuration RGAM))
    (execution : (certifiedTSV RGAM generation).Execution (initConfig RGAM) trace) :
    ProjectedSpecificationExecution RGAM emptyPolicy id EventSpec.spec
      (initConfig RGAM) trace := certifiedV.executions trace execution

/-- The same nonempty crossed branch/merge is accepted by the migrated
full-input language. Its concrete read is independently pinned. -/
theorem crossed_control :
    EventVersionsSpecificationRA RGAM emptyPolicy EventSpec.spec
      (CrossedExecution.config 10) ∧
    RGAM.query (CrossedExecution.records 10).1 () = [5,4,8,7] ∧
    RGAM.query (CrossedExecution.records 10).1 () ≠ [] := by
  refine ⟨certified _ CrossedExecution.Evidence.mint_certified,
    CrossedExecution.Evidence.final_read, ?_⟩
  rw [CrossedExecution.Evidence.final_read]
  change ([5,4,8,7] : List Nat) ≠ []
  decide

#print axioms certified
#print axioms history
#print axioms certifiedV
#print axioms crossed_control
end Sal.MRDTs.Paper1.RGA.EventMigration
