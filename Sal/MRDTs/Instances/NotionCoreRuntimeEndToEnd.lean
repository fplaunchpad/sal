import Sal.MRDTs.Instances.NotionCoreRuntimeTheorem
import Sal.MRDTs.Instances.NotionCoreRuntimeHonestProgress

/-! Constructive executable endpoint: start from the actual empty engine,
receive an honest closed version in arbitrary order with arbitrary duplicates,
and obtain the reference answer. No invariant or acceptance premise is supplied
by the caller. The endpoint covers merge-free closed versions: merge
transactions are refused on receipt, and the structural renderer the query
refines works from facts that record no merge. Merges elsewhere in the network do not
enter the version. -/
namespace Sal.MRDTs.Instances.NotionCoreRuntimeEndToEnd
open NotionCorePayload (Transaction)
open NotionCoreRuntimeEngine

/-- Loading a merge-free closed version of an honest network into the empty
engine yields the reference answer. A version containing a merge is refused
on receipt. -/
theorem load_closed_version (network : NotionCorePayloadNetwork.State)
    (honest : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (free : NotionCoreRuntimeQuery.VersionFree network version)
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
  have admitted : ∀ tx ∈ txs, NotionCoreMergeFree.NotMerge tx := by
    intro tx member
    apply free tx
    have : tx ∈ txs.toFinset := by simpa using member
    rw [receipts] at this
    simpa using this
  obtain ⟨state,accepted,valid,archive⟩ :=
    NotionCoreRuntimeHonestProgress.receiveMany_honest network honest NotionCoreRuntimeEngine.empty empty_refines
      (by intro tx member; simp [NotionCoreRuntimeEngine.empty,NotionCoreRuntimeMetadata.empty] at member) txs published
      admitted
  have image : state.metadata.archive.toFinset = txs.toFinset := by
    simpa [NotionCoreRuntimeEngine.empty,NotionCoreRuntimeMetadata.empty] using archive
  exact ⟨state,accepted,valid,image,
    NotionCoreRuntimeTheorem.closed_version_reference state valid network honest version closed
      (image.trans receipts)⟩

namespace SPOT
private def seed : Transaction := NotionCorePayload.bootstrap [97,98]
private def low : Transaction := ⟨⟨3,[66]⟩,.split .initial .initial (.item ⟨1,[65]⟩)⟩
private def high : Transaction := ⟨⟨3,[67]⟩,.split .initial .initial (.item ⟨1,[65]⟩)⟩
private def mergeBack : Transaction := ⟨⟨4,[66]⟩,.merge (.issued low.id) .initial⟩
private def concurrentNetwork : NotionCorePayloadNetwork.State :=
  NotionCorePayloadNetwork.exchange
    (NotionCorePayloadNetwork.exchange (NotionCorePayloadNetwork.seeded [97,98]) [66] [65]) [67] [65]
private def withLow : NotionCorePayloadNetwork.State :=
  NotionCorePayloadNetwork.emit concurrentNetwork [66] low.payload low
private def withBoth : NotionCorePayloadNetwork.State :=
  NotionCorePayloadNetwork.emit withLow [67] high.payload high
private def version : List NotionRunAllocation.Run := (withBoth.allocation.peers [66]).received

/-- Splitting `ab` after `a` and merging the new block back: the archive with
the merge is refused on receipt from every state, while the merge is still a
well-formed payload that only admission rejects. The same archive without the
merge is accepted from the empty engine, and its query is the hand-derived split
view, neither the merged view `ab` nor a view that drops the split block. -/
theorem merge_refused :
    admissible mergeBack = false ∧ admissible low = true ∧
    (∀ state next, receiveMany state [seed,low,mergeBack] ≠ .ok next) ∧
    ∃ state, receiveMany NotionCoreRuntimeEngine.empty [seed,low] = .ok state ∧
      NotionCoreRuntimeAdapter.observeState state.core =
        some [(0,[97]),(NotionCoreMachine.blockName (.issued low.id),[98])] ∧
      NotionCoreRuntimeAdapter.observeState state.core ≠ some [(0,[97,98])] ∧
      NotionCoreRuntimeAdapter.observeState state.core ≠ some [(0,[97])] := by
  refine ⟨by decide,by decide,?_,?_⟩
  · intro state next accepted
    exact receiveMany_merge_free _ accepted mergeBack (by simp) (.issued low.id) .initial rfl
  have reach : NotionCoreMachineNetwork.Reach withBoth :=
    NotionCoreIncrementalCounterexample.honestly_issuable_splits.2.2
  have closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget withBoth).records version :=
    NotionCoreIssuance.peers_closed
      (NotionCorePayloadNetwork.forget_reachable
        (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reach))) [66]
  have raw : ((withBoth.entries.map NotionCorePayloadNetwork.Entry.tx).filter
      (fun tx => NotionCorePayload.reservation tx ∈ version)) = [low,seed] := by decide +kernel
  have ordered : NotionCoreReconstruction.transactionsFor withBoth version = [seed,low] := by
    unfold NotionCoreReconstruction.transactionsFor
    rw [raw]
    simp [List.mergeSort,NotionCoreReconstruction.Ascending,NotionCoreSourceInvariant.Desc,
      NotionRunAllocation.Before,low,seed,NotionCorePayload.bootstrap]
  have free : NotionCoreRuntimeQuery.VersionFree withBoth version := by
    rw [NotionCoreRuntimeQuery.VersionFree,ordered]
    intro tx member source target payload
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> simp [seed,low,NotionCorePayload.bootstrap] at payload
  obtain ⟨state,accepted,_,_,observed⟩ :=
    load_closed_version withBoth reach version closed free [seed,low] (by rw [ordered])
  have reference : (NotionCoreMachine.replay {} [seed,low] >>= NotionCoreMachine.render) =
      some [(0,[97]),(NotionCoreMachine.blockName (.issued low.id),[98])] := by decide +kernel
  rw [ordered,reference] at observed
  refine ⟨state,accepted,observed,?_,?_⟩ <;> rw [observed] <;> simp [NotionCoreMachine.blockName]
end SPOT

#print axioms load_closed_version
#print axioms SPOT.merge_refused

end Sal.MRDTs.Instances.NotionCoreRuntimeEndToEnd
