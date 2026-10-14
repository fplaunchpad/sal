import Sal.MRDTs.Instances.NotionCoreRuntimeTheorem
import Sal.MRDTs.Instances.NotionCoreRuntimeHonestProgress

/-! Constructive executable endpoint: start from the actual empty engine,
receive an honest closed version in arbitrary order with arbitrary duplicates,
and obtain the reference answer. No invariant or acceptance premise is supplied
by the caller. -/
namespace Sal.MRDTs.Instances.NotionCoreRuntimeEndToEnd
open NotionCorePayload (Transaction)
open NotionCoreRuntimeEngine

theorem load_closed_version (network : NotionCorePayloadNetwork.State)
    (honest : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (txs : List Transaction)
    (receipts : txs.toFinset = (NotionCoreReconstruction.transactionsFor network version).toFinset) :
    ∃ state, receiveMany NotionCoreRuntimeEngine.empty txs = .ok state ∧ Refines state ∧
      state.metadata.archive.toFinset = txs.toFinset ∧
      NotionCoreRuntimeAdapter.observeState state.core =
        (NotionCoreMachine.replay {} (NotionCoreReconstruction.transactionsFor network version) >>=
          NotionCoreMachine.render) := by
  have published : ∀ tx ∈ txs, tx ∈ network.entries.map (·.tx) := by
    intro tx member
    have selected : tx ∈ NotionCoreReconstruction.transactionsFor network version := by
      have : tx ∈ txs.toFinset := by simpa using member
      rw [receipts] at this
      simpa using this
    obtain ⟨⟨entry,present,same⟩,_⟩ :=
      (NotionCoreReconstruction.transactionsFor_membership network version tx).mp selected
    exact List.mem_map.mpr ⟨entry,present,same⟩
  obtain ⟨state,accepted,valid,archive⟩ :=
    NotionCoreRuntimeHonestProgress.receiveMany_honest network honest NotionCoreRuntimeEngine.empty empty_refines
      (by intro tx member; simp [NotionCoreRuntimeEngine.empty,NotionCoreRuntimeMetadata.empty] at member) txs published
  have image : state.metadata.archive.toFinset = txs.toFinset := by
    simpa [NotionCoreRuntimeEngine.empty,NotionCoreRuntimeMetadata.empty] using archive
  exact ⟨state,accepted,valid,image,
    NotionCoreRuntimeTheorem.closed_version_reference state valid network honest version closed
      (image.trans receipts)⟩

#print axioms load_closed_version
end Sal.MRDTs.Instances.NotionCoreRuntimeEndToEnd
