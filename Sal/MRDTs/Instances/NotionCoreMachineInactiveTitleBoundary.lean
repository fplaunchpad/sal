import Sal.MRDTs.Instances.NotionCoreMachineNetwork

/-! Creator admission alone does not protect inactive title emptiness.
The inserted payload below is a fabricated raw choice, not honest positional
preparation. Equal visible text and unchanged tree shape hide the distinction.
-/
namespace Sal.MRDTs.Instances.NotionCoreMachineInactiveTitleBoundary
open NotionCorePayload (BlockKey Payload Transaction)
open NotionCoreMachine

private def seed := NotionCorePayloadNetwork.seeded [97,98]
private def copied := NotionCorePayloadNetwork.exchange seed [83] [65]
private def marker : NotionRunAllocation.Id := ⟨3,[83]⟩
private def cut : Transaction := ⟨marker,.split .initial .initial (.item ⟨1,[65]⟩)⟩
private def cutState := NotionCorePayloadNetwork.emit copied [83] cut.payload cut
private def raw : Transaction := ⟨⟨4,[83]⟩,.insert (.issued marker) (.issued marker) .start [88]⟩
private def rawState := NotionCorePayloadNetwork.emit cutState [83] raw.payload raw
private def before := replay {} [NotionCorePayload.bootstrap [97,98],cut]
private def after := replay {} [NotionCorePayload.bootstrap [97,98],cut,raw]

private theorem honest_cut : NotionCoreCreatorNetwork.Reach cutState := by
  apply NotionCoreCreatorNetwork.Reach.emit [83] cut.payload cut
    (.exchange [83] [65] (.bootstrap [97,98]))
  · decide +kernel
  · intro address member
    have same : address = (.initial, (⟨1,[65]⟩ : NotionRunAllocation.Id)) := by
      simpa [cut,NotionCorePayloadNetwork.locatedReferences,NotionCorePayload.originReference] using member
    subst address
    simp [NotionCorePayloadNetwork.Known,NotionCorePayloadNetwork.exchange,
      NotionCorePayloadNetwork.seeded,NotionCorePayloadNetwork.initial,NotionCorePayload.reservation,
      NotionCorePayload.bootstrap,NotionCoreIssuance.importRuns,NotionRunAllocation.issue,
      NotionRunAllocation.reserve,NotionRunAllocation.initial,NotionRunAllocation.emptyPeer,
      NotionRunAllocation.receive,NotionRunAllocation.deliver,NotionCorePayload.Payload.width,
      NotionCorePayload.Payload.itemCount,NotionCorePayloadNetwork.birthAddresses,NotionCorePayload.births,
      NotionCorePayload.operations,NotionCorePayload.Operation.births,NotionCorePayload.textItems,
      NotionCoreParentMap.runRows,NotionCorePayload.birthId,NotionCorePayload.offsetId,List.range_succ]
  · intro block member
    have same : block = .initial := by simpa [cut,NotionCoreCreatorNetwork.requiredBlocks] using member
    subst block
    simp [NotionCoreCreatorNetwork.KnownCreator,NotionCorePayloadNetwork.exchange,
      NotionCorePayloadNetwork.seeded,NotionCorePayloadNetwork.initial,NotionCorePayload.reservation,
      NotionCorePayload.bootstrap,NotionCoreCreatorNetwork.createdBlocks,NotionCoreIssuance.importRuns,
      NotionRunAllocation.issue,NotionRunAllocation.reserve,NotionRunAllocation.initial,
      NotionRunAllocation.emptyPeer,NotionRunAllocation.receive,NotionRunAllocation.deliver,
      NotionCorePayload.Payload.width,NotionCorePayload.Payload.itemCount]

private theorem known_title : NotionCoreCreatorNetwork.KnownCreator cutState [83] (.issued marker) := by
  refine ⟨⟨cut,(copied.allocation.peers [83]).received⟩, ?_, ?_, ?_⟩
  · simp [cutState,NotionCorePayloadNetwork.emit]
  · simp [cutState,NotionCorePayloadNetwork.emit,NotionRunAllocation.issue,NotionRunAllocation.receive,
      NotionCorePayload.reservation,cut,NotionCorePayload.Payload.width,
      NotionCorePayload.Payload.itemCount,copied,NotionCorePayloadNetwork.exchange,seed,
      NotionCorePayloadNetwork.seeded,NotionCorePayloadNetwork.initial,NotionRunAllocation.reserve,
      NotionCoreIssuance.importRuns,NotionRunAllocation.deliver,NotionRunAllocation.initial,
      NotionRunAllocation.emptyPeer,NotionRunAllocation.Run.last,marker]
  · simp [NotionCoreCreatorNetwork.createdBlocks,cut]

/-- Actual old creator admission accepts the inactive-title raw insertion;
no required item reference exists for START, and the title has a creator. -/
theorem raw_creator_admitted : NotionCoreCreatorNetwork.Reach rawState := by
  apply NotionCoreCreatorNetwork.Reach.emit [83] raw.payload raw
    honest_cut
  · decide +kernel
  · simp [raw,NotionCorePayloadNetwork.locatedReferences,NotionCorePayload.originReference]
  · intro block member
    have same : block = .issued marker := by
      simpa [raw,NotionCoreCreatorNetwork.requiredBlocks] using member
    exact same ▸ known_title

/-- PASS+FAIL: real client preparation selects the inherited marker; the raw
payload instead populates the empty title, while the two-node shape remains. -/
theorem inactive_title_control :
    (before >>= fun state => NotionCoreMachineClient.prepareInsert state (.issued marker) 0 [88]) =
      some (.insert (.issued marker) .initial (.item marker) [88]) ∧
    (after.map fun state => (getInstance state (blockName (.issued marker))).rows.map
      (fun row => row.item.kind)) = some [.text 88 false] ∧
    (after.map fun state => (getInstance state (blockName (.issued marker))).rows) ≠ some [] ∧
    (after.map fun state => (state.forest.find? (fun block => block.id == blockName (.issued marker))).map
      (fun block => (NotionCoreSliceForest.preorderTree block.title).length)) = some (some 2) := by decide +kernel

private def rawMachine : State := after.getD {}

/-- Shape alone survives this fabricated insertion. -/
theorem normal_shape_survives : NotionCoreSliceForest.NormalForest rawMachine.forest := by
  have shape : rawMachine.forest =
      [⟨0,.node ⟨(0,.start),some (NotionCorePhysicalReplay.address 0 marker)⟩ .nil⟩,
       ⟨blockName (.issued marker),.node (NotionCoreSliceForest.titleRef (blockName (.issued marker)))
         (.cons (.node ⟨NotionCorePhysicalReplay.address 0 marker,none⟩ .nil) .nil)⟩] := by decide +kernel
  intro block member
  rw [shape] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact .own _
  · have same := List.mem_singleton.mp member
    subst block
    exact .attached _

/-- The old tree still has its inherited leaf, but its inactive own instance
is no longer empty. Creator admission cannot establish this stronger invariant. -/
theorem empty_inactive_failure :
    ¬ NotionCoreSliceForest.EmptyInactive (physical rawMachine)
      (NotionCoreSliceForest.profile rawMachine.forest) := by
  let current : NotionCoreSliceForest.Profile :=
    (blockName (.issued marker), NotionCorePhysicalReplay.address 0 marker, true)
  have member : current ∈ NotionCoreSliceForest.profile rawMachine.forest := by decide +kernel
  have different : physical rawMachine (blockName (.issued marker)) ≠
      NotionCoreSliceForest.emptyPhysical (blockName (.issued marker)) := by decide +kernel
  intro empty
  exact different (empty current member rfl)

#print axioms normal_shape_survives
#print axioms empty_inactive_failure
#print axioms raw_creator_admitted
#print axioms inactive_title_control
end Sal.MRDTs.Instances.NotionCoreMachineInactiveTitleBoundary
