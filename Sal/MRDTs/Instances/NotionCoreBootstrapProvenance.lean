import Sal.MRDTs.Instances.NotionCoreMachineNetwork
import Sal.MRDTs.Instances.NotionCoreRootCreators
import Sal.MRDTs.Instances.NotionCoreMachineCreatorPresence

/-! Bootstrap need not be first in source key order. Its initial instance is
nevertheless fresh in the actual earlier prefix; creator use before its unique
bootstrap is impossible. No fresh-state or successful-bootstrap premise. -/
namespace Sal.MRDTs.Instances.NotionCoreBootstrapProvenance
local instance (a b : List Nat) : Decidable (a < b) := List.decidableLT a b
open NotionRunAllocation (Session Run)
open NotionCorePayload (Transaction BlockKey)
open NotionCoreMachine

theorem canonical_bootstrap_transaction_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List Run)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (atoms : List Nat) (payload : tx.payload = .bootstrap atoms) :
    tx = NotionCorePayload.bootstrap atoms := by
  obtain ⟨entry,member,same,_⟩ := NotionCoreReconstruction.transactionsFor_received network version tx
    (position ▸ List.mem_append_right pre (by simp))
  exact same.symm.trans (NotionCoreRootCreators.archived_bootstrap network
    (NotionCoreCreatorNetwork.payload_reachable reachable) entry member atoms (same ▸ payload))

theorem canonical_bootstrap_transaction (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (atoms : List Nat) (payload : tx.payload = .bootstrap atoms) :
    tx = NotionCorePayload.bootstrap atoms := by
  exact canonical_bootstrap_transaction_version network reachable (network.allocation.peers peer).received
    pre suffix tx position atoms payload

theorem canonical_bootstrap_fresh_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (atoms : List Nat) (payload : tx.payload = .bootstrap atoms)
    (state : State) (accepted : replay {} pre = some state) :
    (∀ entry ∈ state.instances, entry.1 ≠ blockName .initial) ∧
      FreshBlock state (blockName .initial) := by
  have excluded := NotionCoreRootCreators.canonical_no_initial_use_version network reachable version closed pre suffix tx position atoms payload
  have noInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName .initial := by
    intro stored member equal
    have keyMember : stored.1 ∈ NotionCoreMachineCreators.instanceKeys state := List.mem_map.mpr ⟨stored,member,rfl⟩
    obtain ⟨previous,present,key,used,encoded⟩ := NotionCoreMachineCreators.replay_instance_used pre state accepted stored.1 keyMember
    have sameKey : key = .initial := blockName_injective (encoded.symm.trans equal)
    exact excluded previous present (sameKey ▸ used)
  have supported := (NotionCoreMachineCreatorPresence.replay_created_instances pre state accepted).1
  refine ⟨noInstance,?_,?_⟩
  · intro block member equal
    obtain ⟨entry,present,name⟩ := supported block.id (List.mem_append_left _ (List.mem_map.mpr ⟨block,member,rfl⟩))
    exact noInstance entry present (name.trans equal)
  · intro shown
    obtain ⟨entry,present,name⟩ := supported _ (List.mem_append_right _ shown)
    exact noInstance entry present name

theorem canonical_bootstrap_fresh (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (atoms : List Nat) (payload : tx.payload = .bootstrap atoms)
    (state : State) (accepted : replay {} pre = some state) :
    (∀ entry ∈ state.instances, entry.1 ≠ blockName .initial) ∧
      FreshBlock state (blockName .initial) := by
  have issued := NotionCorePayloadNetwork.forget_reachable
    (NotionCoreCreatorNetwork.payload_reachable reachable)
  exact canonical_bootstrap_fresh_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed issued peer) pre suffix tx position atoms payload state accepted

private def seed := NotionCorePayloadNetwork.seeded [97]
private def issued := NotionCoreMachineNetwork.issue seed [64] (.create none)
private def received := issued.map (fun network => NotionCorePayloadNetwork.exchange network [64] [65])
private def earlier : Transaction := ⟨⟨1,[64]⟩,.create none⟩

/-- Honest @ replica has no bootstrap receipt when it creates. On subsequent
receipt, its @1 create sorts before A1 bootstrap; the prefix is not empty. -/
theorem bootstrap_after_create_control :
    (issued.map (fun network => network.entries.head?.map (fun entry => entry.tx))) = some (some earlier) ∧
    (received.map (fun network => NotionCoreReconstruction.transactions network [64])) =
      some [earlier,NotionCorePayload.bootstrap [97]] ∧
    (received.map (fun network => NotionCoreReconstruction.transactions network [64])) ≠
      some [NotionCorePayload.bootstrap [97],earlier] := by
  have order : ([64] : List Nat) < [65] := by decide +kernel
  simp [issued,received,seed,earlier,NotionCoreMachineNetwork.issue,
    NotionCoreMachineNetwork.Request.earlyNoop,NotionCorePayloadNetwork.forget,order,
    NotionCoreMachineNetwork.prepareRequest,NotionCoreMachineClient.prepareCreate,
    NotionCoreReconstruction.reconstruct,NotionCoreReconstruction.transactions,
    NotionCorePayloadNetwork.seeded,NotionCorePayloadNetwork.initial,NotionCorePayloadNetwork.emit,
    NotionCorePayloadNetwork.exchange,NotionCoreIssuance.importRuns,
    NotionCorePayload.prepare,NotionCorePayload.Payload.emits,NotionCorePayload.bootstrap,
    NotionCorePayload.reservation,NotionCorePayload.Payload.width,NotionCorePayload.Payload.itemCount,
    NotionCoreMachine.replay,NotionRunAllocation.issue,NotionRunAllocation.initial,
    NotionRunAllocation.emptyPeer,NotionRunAllocation.reserve,NotionRunAllocation.receive,
    NotionRunAllocation.deliver,NotionRunAllocation.Run.last,List.mergeSort,
    NotionCoreReconstruction.Ascending,NotionCoreSourceInvariant.Desc,NotionRunAllocation.Before]

#print axioms canonical_bootstrap_transaction_version
#print axioms canonical_bootstrap_fresh_version
#print axioms bootstrap_after_create_control
#print axioms canonical_bootstrap_transaction
#print axioms canonical_bootstrap_fresh
end Sal.MRDTs.Instances.NotionCoreBootstrapProvenance
