import Sal.MRDTs.Instances.NotionCoreRichProtocolEvents

/-! Every actual rich caller receipt list is a complete captured-past version.
The allocation skeleton below forgets payload references only for this
structural closure argument; it supplies no semantic or endpoint invariant.
All rich transactions, including formats, remain in the skeleton. -/
namespace Sal.MRDTs.Instances.NotionCoreRichProtocolPeerClosure
open NotionRunAllocation (Session)
open NotionCoreRichProtocolNetwork (State Entry Reach)

private def record (entry : Entry) : NotionCoreIssuance.Record :=
  ⟨entry.transaction.reservation,entry.past,[],false⟩

private def skeleton (network : State) : NotionCoreIssuance.State :=
  ⟨network.allocation,network.entries.map record⟩

private theorem skeleton_reachable {network : State} (reachable : Reach network) :
    NotionCoreIssuance.Reach (skeleton network) := by
  induction reachable with
  | init => exact .init
  | bootstrap text =>
    exact .mint [65] _ false [] .init
      (NotionCoreRichProtocolNetwork.width_positive _) (by simp)
  | exchange target source prior ih => exact .exchange target source ih
  | @request state next session request prior issued ih =>
    obtain ⟨current,payload,reconstructed,prepared,checked,rfl⟩ :=
      NotionCoreRichProtocolNetwork.issue_data state next session request issued
    exact .mint session payload.width false [] ih
      (NotionCoreRichProtocolNetwork.width_positive payload) (by simp)

theorem peers_closed {network : State} (reachable : Reach network) (session : Session) :
    NotionCoreRichProtocolEvents.Closed network (network.allocation.peers session).received := by
  have closed := NotionCoreIssuance.peers_closed (skeleton_reachable reachable) session
  intro entry published selected old past
  exact closed (record entry) (List.mem_map.mpr ⟨entry,published,rfl⟩) selected old past

/-- The generic saved-version enumeration is exactly the executable caller's
sorted received-transaction list when the selected version is a real peer. -/
theorem transactionsFor_peer (network : State) (session : Session) :
    NotionCoreRichProtocolEvents.transactionsFor network (network.allocation.peers session).received =
      NotionCoreRichPayload.sort (NotionCoreRichProtocolNetwork.receivedTransactions network session) := rfl

theorem reconstruct_peer (network : State) (session : Session) :
    NotionCoreRichProtocolNetwork.reconstruct network session =
      NotionCoreAtomicFormattingMachine.replay {}
        (NotionCoreRichProtocolEvents.transactionsFor network (network.allocation.peers session).received) := rfl

#print axioms peers_closed
end Sal.MRDTs.Instances.NotionCoreRichProtocolPeerClosure
