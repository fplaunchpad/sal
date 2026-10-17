import Sal.MRDTs.Instances.NotionCoreMachineDocumentInvariant
import Sal.MRDTs.Instances.NotionCoreMachineDocumentClient

/-! Honest local deletion has its independent positional visible effect.
All structural and address-uniqueness guards come from actual reconstruction.
This is a local request/operation theorem, not yet complete network-history
refinement or the Sal RA bridge. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineClientEffects
open NotionCoreMachine
open NotionCoreMachineDocument
open NotionCoreMachineDocumentClient
open NotionCorePayload (BlockKey Transaction reservation)
open NotionCoreSource (Block Atom)

private theorem selected_instances_exist (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (state : State) (accepted : replay {} (NotionCoreReconstruction.transactions network peer) = some state)
    (block : BlockKey) (start stop : Nat) (groups : List (BlockKey × List NotionRunAllocation.Id))
    (prepared : NotionCoreMachineDelete.selectErase state block start stop = some (.erase block groups)) :
    ∀ group ∈ groups, ∃ entry ∈ state.instances, entry.1 = blockName group.1 := by
  intro group member
  have known := NotionCoreMachineDelete.selectErase_creators network
    (NotionCoreMachineNetwork.creator_reachable reachable) peer _ state
    (NotionCoreReconstruction.transactions_received network peer) accepted block start stop _ prepared
  obtain ⟨provider,published,received,created⟩ := known group.1
    (by simp only [NotionCoreCreatorNetwork.requiredBlocks]
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨group,member,rfl⟩))
  have inReplay : provider.tx ∈ NotionCoreReconstruction.transactions network peer :=
    (NotionCoreReconstruction.transactions_membership network peer provider.tx).mpr
      ⟨⟨provider,published,rfl⟩,received⟩
  exact (NotionCoreMachineCreatorPresence.replay_created_instances _ state accepted).2
    provider.tx inReplay group.1 created

/-- Valid nonempty deletion preparation and execution have the ordinary local
range effect on the actual renderer, preserving every other displayed block,
also when the range spans several text instances of a merged block. No
acceptance, structural invariant, slot uniqueness, selection, or desired
after-render equation is supplied for the resulting operations. -/
theorem honest_erase_effect (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (state : State) (reconstructed : NotionCoreReconstruction.reconstruct network peer = some state)
    (pre post : NotionCoreSourceDocument.Document) (source : Block)
    (materialized : materializeDocument state = some (pre ++ source :: post))
    (block : BlockKey) (name : source.id = blockName block) (start stop : Nat)
    (nonempty : start < stop) (bound : stop ≤ NotionCoreMachineDeleteTotal.visibleLength state block) :
    ∃ groups result after,
      NotionCoreMachineDelete.selectErase state block start stop = some (.erase block groups) ∧
      applyOperations state (groups.map fun group => .erase block group.1 group.2) = some result ∧
      materializeDocument result = some after ∧
      render result = some (NotionCoreSpec.view (NotionCoreSourceDocument.project pre) ++
        [(source.id,(NotionCoreSpec.text source.project.slots).take start ++
          (NotionCoreSpec.text source.project.slots).drop stop)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project post)) ∧
      NotionCoreMachinePartition.Partitioned result ∧ NotionCoreMachineShape.ShapeInvariant result := by
  obtain ⟨checked,current,part,shape,_⟩ := NotionCoreMachineHonestReplay.honest_reconstruct network reachable peer
  have same : checked = state := Option.some.inj (current.symm.trans reconstructed)
  subst checked
  have accepted : replay {} (NotionCoreReconstruction.transactions network peer) = some state := reconstructed
  have physicalUnique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable)) peer
    (NotionCoreReconstruction.transactions network peer) [] (by simp) state accepted
  have aligned := NotionCoreMachineDisplay.reconstructed_aligned network peer state accepted
  have addresses := NotionCoreMachineDocumentInvariant.projected_addresses_unique state part physicalUnique aligned
    _ materialized
  obtain ⟨groups,result,after,prepared,operations,extracted,effect⟩ := erase_request_effect _ state accepted part
    physicalUnique pre post source materialized block name start stop nonempty bound addresses
  have existsInstance := selected_instances_exist network reachable peer state accepted block start stop
    groups prepared
  obtain ⟨checked,checkedOperations,nextPart⟩ := NotionCoreMachinePartitionUpdates.erase_operations_partitioned
    state block groups part existsInstance
  have sameResult : checked = result := Option.some.inj (checkedOperations.symm.trans operations)
  subst checked
  have nextShape := (NotionCoreMachineRootReplay.erase_groups_shape_active state result block groups shape
    operations).1
  have rendered := materialized_render result after extracted
  rw [effect] at rendered
  exact ⟨groups,result,after,prepared,operations,extracted,rendered,nextPart,nextShape⟩

#print axioms honest_erase_effect

namespace SPOT
private def erasedView (state : State) (start stop : Nat) : Option (List (Nat × List Nat)) := do
  let payload ← NotionCoreMachineDelete.selectErase state .initial start stop
  match payload with
  | .erase block groups =>
    applyOperations state (groups.map fun group => .erase block group.1 group.2) >>= render
  | _ => none
/-- Actual positional preparation and erasure remove a, retain b, and retain
its block. The rival no-op and wrong-range renderings are explicitly rejected. -/
theorem actual_range_control :
    (replay {} [NotionCorePayload.bootstrap [97,98]] >>= fun state => erasedView state 0 1) =
      some [(0,[98])] ∧
    (replay {} [NotionCorePayload.bootstrap [97,98]] >>= fun state => erasedView state 0 1) ≠
      some [(0,[97])] ∧
    (replay {} [NotionCorePayload.bootstrap [97,98]] >>= fun state => erasedView state 0 1) ≠
      some [(0,[97,98])] := by decide +kernel

private def x : NotionRunAllocation.Id := ⟨3,[66]⟩
private def merged : List Transaction :=
  [NotionCorePayload.bootstrap [97], ⟨x,.create (some .initial)⟩,
    ⟨⟨4,[66]⟩,.insert (.issued x) (.issued x) .start [98,99]⟩, ⟨⟨6,[66]⟩,.merge (.issued x) .initial⟩]

/-- After merging bc into a, erasing the range ab spanning the merged
boundary leaves c alone, in one transaction of two instance groups. Erasing
only the first instance's part, or nothing, is rejected. -/
theorem merged_range_control :
    (replay {} merged >>= fun state => erasedView state 0 2) = some [(0,[99])] ∧
    (replay {} merged >>= fun state => erasedView state 0 2) ≠ some [(0,[98,99])] ∧
    (replay {} merged >>= fun state => erasedView state 0 2) ≠ some [(0,[97,98,99])] := by
  decide +kernel
end SPOT
end Sal.MRDTs.Instances.NotionCoreMachineClientEffects
