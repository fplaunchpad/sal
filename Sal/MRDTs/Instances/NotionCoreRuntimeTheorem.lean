import Sal.MRDTs.Instances.NotionCoreRuntimeAdapterProofs
import Sal.MRDTs.Instances.NotionCoreRuntimeRefinement

/-! Native indexed execution inherits the checked structural document answer.
Protocol/archive image assumptions express receipt provenance; no query equality
or successful-receipt totality is smuggled into the document endpoints. -/
namespace Sal.MRDTs.Instances.NotionCoreRuntimeTheorem
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open NotionCorePayload (Transaction)
open NotionCoreRuntimeEngine (State Refines)

/-- A native version with honest closed archive provenance returns exactly the
verified structural MRDT query of its own retained archive's fact projection. -/
theorem closed_version_query (state : State) (refined : Refines state)
    (network : NotionCorePayloadNetwork.State)
    (honest : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (receipts : state.metadata.archive.toFinset =
      (NotionCoreReconstruction.transactionsFor network version).toFinset) :
    NotionCoreRuntimeAdapter.observeState state.core =
      NotionCoreStructuralMRDT.D.query
        (NotionCoreStructuralTransport.project state.metadata.archive.toFinset) () := by
  have image : NotionCoreRuntimeState.abstract state.core =
      NotionCoreStructuralFacts.ofTransactions (NotionCoreReconstruction.transactionsFor network version) :=
    refined.2.2.trans (NotionCoreRuntimeEngine.Facts.congr receipts)
  have observed := NotionCoreRuntimeAdapter.observeState_correct state.core refined.1 network honest version closed image
  rw [NotionCoreStructuralTransport.project_list]
  change NotionCoreRuntimeAdapter.observeState state.core =
    NotionCoreStructuralRender.observe (NotionCoreStructuralFacts.ofTransactions state.metadata.archive)
  rw [← refined.2.2]
  exact observed

/-- The compiled query returns the same create/insert/delete/split observation
as actual reference reconstruction for the received honest closed version. -/
theorem closed_version_reference (state : State) (refined : Refines state)
    (network : NotionCorePayloadNetwork.State)
    (honest : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (receipts : state.metadata.archive.toFinset =
      (NotionCoreReconstruction.transactionsFor network version).toFinset) :
    NotionCoreRuntimeAdapter.observeState state.core =
      (NotionCoreMachine.replay {} (NotionCoreReconstruction.transactionsFor network version) >>=
        NotionCoreMachine.render) := by
  rw [closed_version_query state refined network honest version closed receipts]
  rw [NotionCoreStructuralTransport.project_list]
  change NotionCoreStructuralRender.observe (NotionCoreStructuralFacts.ofTransactions state.metadata.archive) = _
  rw [NotionCoreRuntimeEngine.Facts.congr receipts]
  exact NotionCoreStructuralRender.honest_observe network honest version closed

/-- Registered Sal versions use the original honest factory/client protocol.
The native archive can arrive in any order and include duplicate receipts;
only its actual represented version image must match the registered archive. -/
theorem registered_query (state : State) (refined : Refines state)
    {sessions initialLift C network lift}
    (injective : Function.Injective sessions)
    (honest : NotionCoreProtocol.Reach sessions initialLift C network lift)
    (v : Version) (archive : Finset Transaction) (events : Set (Op Transaction))
    (registered : C.ver v = some (archive,events))
    (receipts : state.metadata.archive.toFinset = archive) :
    NotionCoreRuntimeAdapter.observeState state.core = NotionCoreMRDT.D.query archive () := by
  have paired := honest.paired injective
  have payloadReach := NotionCoreCreatorNetwork.payload_reachable
    (NotionCoreMachineNetwork.creator_reachable paired.honest)
  have certified := NotionCoreCarrierExecution.certify honest.raw
  have execution := CertifiedExecution.virtual certified
  have metadata := execution.canonicalConfig
    (fun C _ => CommutingPort.automatedJoinAt (D := NotionCoreMRDT.D)
      NotionCoreMRDT.all_comm NotionCoreMRDT.fiveVCs C.replayContext)
  have image := NotionCoreArchiveCertificate.represented_state_image network payloadReach C.replayContext
    events lift paired.events archive (NotionCoreMRDT.represented_versions certified v archive events registered)
  have closed := NotionCoreArchiveEvents.version_closed network payloadReach C.events events C.vis lift
    paired.events (metadata.version_events_causal v archive events registered)
  have observed := closed_version_query state refined network paired.honest _ closed (receipts.trans image)
  rw [receipts] at observed
  exact observed.trans (NotionCoreStructuralMRDT.registered_query injective honest v archive events registered)

#print axioms closed_version_query
#print axioms closed_version_reference
#print axioms registered_query
end Sal.MRDTs.Instances.NotionCoreRuntimeTheorem
