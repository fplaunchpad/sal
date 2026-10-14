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

private theorem selected_instance_exists (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (state : State) (accepted : replay {} (NotionCoreReconstruction.transactions network peer) = some state)
    (block inst : BlockKey) (start stop : Nat) (ids : List NotionRunAllocation.Id)
    (prepared : NotionCoreMachineDelete.selectErase state block start stop = some (.erase block inst ids)) :
    ∃ entry ∈ state.instances, entry.1 = blockName inst := by
  have known := NotionCoreMachineDelete.selectErase_creators network
    (NotionCoreMachineNetwork.creator_reachable reachable) peer _ state
    (NotionCoreReconstruction.transactions_received network peer) accepted block start stop _ prepared
  obtain ⟨provider,published,received,created⟩ := known inst
    (by simp [NotionCoreCreatorNetwork.requiredBlocks])
  have inReplay : provider.tx ∈ NotionCoreReconstruction.transactions network peer :=
    (NotionCoreReconstruction.transactions_membership network peer provider.tx).mpr
      ⟨⟨provider,published,rfl⟩,received⟩
  exact (NotionCoreMachineCreatorPresence.replay_created_instances _ state accepted).2
    provider.tx inReplay inst created

/-- Valid nonempty deletion preparation and execution have the ordinary local
range effect on the actual renderer, preserving every other displayed block.
No acceptance, structural invariant, slot uniqueness, selection, or desired
after-render equation is supplied for the resulting operation. -/
theorem honest_erase_effect (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (state : State) (reconstructed : NotionCoreReconstruction.reconstruct network peer = some state)
    (pre post : NotionCoreSourceDocument.Document) (source : Block)
    (materialized : materializeDocument state = some (pre ++ source :: post))
    (block : BlockKey) (name : source.id = blockName block) (start stop : Nat)
    (nonempty : start < stop) (bound : stop ≤ NotionCoreMachineDeleteTotal.visibleLength state block) :
    ∃ inst ids result after,
      NotionCoreMachineDelete.selectErase state block start stop = some (.erase block inst ids) ∧
      applyOperation state (.erase block inst ids) = some result ∧
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
  have addresses := NotionCoreMachineDocumentInvariant.projected_addresses_unique state part physicalUnique shape aligned
    _ materialized
  obtain ⟨inst,ids,result,after,prepared,operation,extracted,effect⟩ := erase_request_effect _ state accepted part shape
    physicalUnique pre post source materialized block name start stop nonempty bound addresses
  have existsInstance := selected_instance_exists network reachable peer state accepted block inst start stop ids prepared
  obtain ⟨checked,checkedOperation,nextPart⟩ := NotionCoreMachinePartitionUpdates.erase_operation_partitioned
    state block inst ids part existsInstance
  have sameResult : checked = result := Option.some.inj (checkedOperation.symm.trans operation)
  subst checked
  have nextShape := (NotionCoreMachineRootReplay.erase_shape_active state result block inst ids shape operation).1
  have rendered := materialized_render result nextPart nextShape.1 nextShape.2.2 after extracted
  rw [effect] at rendered
  exact ⟨inst,ids,result,after,prepared,operation,extracted,rendered,nextPart,nextShape⟩

#print axioms honest_erase_effect

namespace SPOT
private def erasedView (state : State) : Option (List (Nat × List Nat)) := do
  let payload ← NotionCoreMachineDelete.selectErase state .initial 0 1
  match payload with
  | .erase block inst ids => applyOperation state (.erase block inst ids) >>= render
  | _ => none
/-- Actual positional preparation and erasure remove a, retain b, and retain
its block. The rival no-op and wrong-range renderings are explicitly rejected. -/
theorem actual_range_control :
    (replay {} [NotionCorePayload.bootstrap [97,98]] >>= erasedView) = some [(0,[98])] ∧
    (replay {} [NotionCorePayload.bootstrap [97,98]] >>= erasedView) ≠ some [(0,[97])] ∧
    (replay {} [NotionCorePayload.bootstrap [97,98]] >>= erasedView) ≠ some [(0,[97,98])] := by decide +kernel
end SPOT
end Sal.MRDTs.Instances.NotionCoreMachineClientEffects
