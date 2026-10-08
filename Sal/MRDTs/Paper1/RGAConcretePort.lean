import Sal.MRDTs.Paper1.ConcreteCommutingVCReplay
import Sal.MRDTs.Paper1.RGAEventSpec

/-! Plain RGA uses the shared concrete VC induction and an independent
strict list/registry history bridge. Mint evidence establishes unique supplied
identifiers, live anchors at issuance, and the absence of prior deletion.
These facts select an accepted history; they do not redefine spec commutation.
-/
namespace Sal.MRDTs.Paper1.RGA.ConcretePort
open Foundation ConcreteMRDT
open Sal.MRDTs.Instances.RGA

theorem joinAt (C : ReplayContext RGAM.toUpdateSig) : JoinAt RGAM C :=
  CommutingPort.vcJoinAt RGAM_all_comm RGAM_mergeLaws RGAM_deltaLaws
    RGAM_commutingPeelLaw C

theorem canonicalConfig {C : Configuration RGAM}
    (execution : CertifiedExecution RGAM generation C) : CanonicalConfig C :=
  execution.canonicalConfig (fun _ _ => joinAt _)

/-- This bridge uses the new VC-derived canonical configuration. In
particular, no direct RGA Join theorem is used to obtain replay provenance. -/
theorem history : EventExecutionHistoryAdequacy RGAM (commutingPolicy RGAOp)
    EventSpec.spec generation := by
  intro C execution v s E hv q
  cases q
  have good := canonicalConfig execution
  obtain ⟨ops,hp,_,_⟩ := hasReplayWitness_of_canonical good v s E hv
  have hwf := versionWellFormed_of_evidence good execution.mintHonest hv
  refine ⟨canonical ops, canonical_listPermOf hp,
    (canonical_ordered ops).imp (fun {_ _} _ =>
      paperOrder_false_of_all_commute RGAM_all_comm _ _ _ _), ?_, ?_⟩
  · apply (Identified.canonical_respects_specVisibility_of_evidence
      true good execution.mintHonest hv hp).imp
    intro a b hab edge
    exact hab ⟨edge.1,fun hc => edge.2 ((EventSpec.commutes_iff b a).mpr hc)⟩
  · have refines := canonical_refines_list hp hwf
    change read (applySeq RGAM.toUpdateSig RGAM.init (canonical ops)) =
      listSpec.run (canonical ops) at refines
    change EventSpec.spec.admits (projectedLabels (D := RGAM) id (canonical ops) ++
      [.query () (read (applySeq RGAM.toUpdateSig RGAM.init (canonical ops)))])
    rw [refines, EventSpec.spec_eq]
    simpa only [HistorySpec.withInputs, projectedLabels, List.map_append,
      List.map_cons, List.map_nil, List.map_map, SeqLabel.mapUpdate] using
      Identified.strict_canonical_admitted hp hwf

noncomputable def conditions : ScopedVCConditions (commutingPolicy RGAOp) EventSpec.spec generation :=
  CommutingPort.scopedConditions RGAM_all_comm
    RGAM_mergeLaws RGAM_deltaLaws RGAM_commutingPeelLaw generation history

theorem versionsV {C : Configuration RGAM}
    (reach : MintCertifiedReachV RGAM (canonicalVirtualMergeBase RGAM) generation C) :
    VersionsWitness (commutingPolicy RGAOp) EventSpec.spec C :=
  conditions.versionsV reach

theorem executions (trace : List (Label RGAM × Configuration RGAM))
    (execution : (certifiedTS RGAM generation).Execution (initConfig RGAM) trace) :
    ExecutionCorrect (commutingPolicy RGAOp) EventSpec.spec trace :=
  conditions.executions trace execution

theorem executionsV (trace : List (Label RGAM × Configuration RGAM))
    (execution : (certifiedTSV RGAM generation).Execution (initConfig RGAM) trace) :
    ExecutionCorrect (commutingPolicy RGAOp) EventSpec.spec trace :=
  conditions.executionsV trace execution

/-- Concrete implementation commutation does not make the independent
strict sequential language commute. The execution-scoped bridge is necessary
for this unchanged specification. -/
theorem globalCompatibility_impossible : ¬ CommutationCompatibility RGAM id EventSpec.spec := by
  intro compatible
  have h := compatible (1,0,.addAfter 0) (2,0,.remove 1)
    (RGAM_all_comm _ _)
  exact Identified.ReadSide.strict_add_delete_not_commute ((EventSpec.commutes_iff _ _).mp h)

theorem crossed_control :
    VersionsWitness (commutingPolicy RGAOp) EventSpec.spec
      (CrossedExecution.config 10) ∧
    RGAM.query (CrossedExecution.records 10).1 () = [5,4,8,7] ∧
    RGAM.query (CrossedExecution.records 10).1 () ≠ [] := by
  refine ⟨versionsV CrossedExecution.Evidence.mint_certified.toV,
    CrossedExecution.Evidence.final_read, ?_⟩
  rw [CrossedExecution.Evidence.final_read]
  change ([5,4,8,7] : List Nat) ≠ []
  decide

end Sal.MRDTs.Paper1.RGA.ConcretePort
